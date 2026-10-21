-- Prove2me | solution 1 for GabayMercier.Approximation.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T08:00:27.068702+00:00
-- url     : https://prove2.me/submissions/f86c2419-9696-4b2a-8ea7-47183ce236ba

/-
SPDX-License-Identifier: Apache-2.0
Lean formalization of Gabay and Mercier, A Dual Algorithm for the Solution of
Nonlinear Variational Problems via Finite Element Approximation, Theorem 4.1.
Native Prove2Me definitions are imported unchanged. The finite convex-value
helper adapts our own prior Gabay-Mercier ADMM formalization; the approximation
and weak-compactness proofs are new. No other participant's proof source is used.
-/
import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_Approximation_Model
import Mathlib.Analysis.InnerProductSpace.Adjoint

-- BEGIN ERealGrowth
open Filter Topology Set InertialFB.IFB
open scoped RealInnerProductSpace

namespace GabayApproximationProof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma convex_finite_value {f : H → EReal} (hc : IsConvexFn f)
    {x y : H} (hx : f x ≠ ⊤) (hy : f y ≠ ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    f (a • x+b • y) ≤ ((a*(f x).toReal+b*(f y).toReal : ℝ) : EReal) := by
  have hh := hc (show (x,(f x).toReal) ∈ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)} from EReal.le_coe_toReal hx)
    (show (y,(f y).toReal) ∈ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)} from EReal.le_coe_toReal hy) ha hb hab
  change f (a • x+b • y) ≤ ((a • (f x).toReal+b • (f y).toReal : ℝ) : EReal) at hh
  simpa only [smul_eq_mul] using hh

lemma exists_linear_norm_lower {f : H → EReal} (hp : IsProperFn f)
    (hc : IsConvexFn f) (hl : LowerSemicontinuous f) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ y, f y ≠ ⊤ → -C-D*‖y‖ ≤ (f y).toReal := by
  obtain ⟨x,hx⟩ := hp.2
  let q := (f x).toReal
  have hfx : f x = (q : EReal) := (EReal.coe_toReal hx (hp.1 x)).symm
  have hev : ∀ᶠ z in 𝓝 x, ((q-1 : ℝ) : EReal) < f z :=
    hl x _ (by change ((q-1 : ℝ) : EReal) < f x; rw [hfx, EReal.coe_lt_coe_iff]; linarith)
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hev
  let D := 2/r
  let C := |q|+2+D*‖x‖
  have hD : 0 ≤ D := div_nonneg (by norm_num) hr.le
  refine ⟨C,D,by dsimp [C]; positivity,hD,?_⟩
  intro y hy
  let d := ‖y-x‖
  let t := r/(2*(r+d))
  have hd : 0 ≤ d := norm_nonneg _
  have hden : 0 < 2*(r+d) := by positivity
  have ht : 0 < t := div_pos hr hden
  have ht1 : t ≤ 1 := (div_le_one hden).2 (by linarith)
  have htid : t*(2*(r+d)) = r := div_mul_cancel₀ _ (ne_of_gt hden)
  have htd : t*d < r := by nlinarith
  have hz : dist ((1-t) • x+t • y) x < r := by
    have he : (1-t) • x+t • y-x = t • (y-x) := by module
    rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    exact htd
  have hlo := hball hz
  have hup := convex_finite_value hc hx hy (by linarith : 0 ≤ 1-t) ht.le (by ring)
  have hreal : q-1 < (1-t)*q+t*(f y).toReal := by
    exact EReal.coe_lt_coe_iff.mp (lt_of_lt_of_le hlo hup)
  have hprod : t*(2+D*d)=1 := by
    have hdr : D*r=2 := div_mul_cancel₀ _ (ne_of_gt hr)
    nlinarith [congrArg (fun z : ℝ => z*D) htid]
  have hbase : q-2-D*d ≤ (f y).toReal := by nlinarith
  have hdist : d ≤ ‖y‖+‖x‖ := norm_sub_le _ _
  have hq : -|q| ≤ q := neg_abs_le q
  dsimp [C]
  nlinarith [mul_le_mul_of_nonneg_left hdist hD]

end GabayApproximationProof
-- END ERealGrowth

-- BEGIN QuadraticObjective
open Filter Topology Set InertialFB.IFB
open scoped RealInnerProductSpace
namespace GabayApproximationProof

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

noncomputable def qObjective (A : V →L[ℝ] Y) (f : Y → EReal)
    (b : StrongDual ℝ V) (v : V) : EReal :=
  ((1/2*‖A v‖^2-b v : ℝ) : EReal)+f (A v)

noncomputable def qValue (A : V →L[ℝ] Y) (f : Y → EReal)
    (b : StrongDual ℝ V) (v : V) : ℝ :=
  1/2*‖A v‖^2-b v+(f (A v)).toReal

lemma qObjective_eq {A : V →L[ℝ] Y} {f : Y → EReal} {b : StrongDual ℝ V}
    (hp : IsProperFn f) {v : V} (hv : f (A v) ≠ ⊤) :
    qObjective A f b v = (qValue A f b v : EReal) := by
  unfold qObjective qValue
  conv_lhs => rw [← EReal.coe_toReal hv (hp.1 _), ← EReal.coe_add]

lemma qObjective_ne_top_iff {A : V →L[ℝ] Y} {f : Y → EReal} {b : StrongDual ℝ V}
    {v : V} : qObjective A f b v ≠ ⊤ ↔ f (A v) ≠ ⊤ := by
  exact EReal.add_ne_top_iff_ne_top_right (EReal.coe_ne_bot _) (EReal.coe_ne_top _)

lemma quadratic_midpoint_identity (A : V →L[ℝ] Y) (b : StrongDual ℝ V) (x y : V) :
    1/2*‖A ((1/2:ℝ) • x+(1/2:ℝ) • y)‖^2-b ((1/2:ℝ) • x+(1/2:ℝ) • y) =
      (1/2*‖A x‖^2-b x)/2+(1/2*‖A y‖^2-b y)/2-‖A (x-y)‖^2/8 := by
  simp only [map_add,map_smul, map_sub, smul_eq_mul]
  rw [← smul_add,norm_smul,Real.norm_eq_abs]
  norm_num
  rw [mul_pow,norm_add_sq_real,norm_sub_sq_real]
  ring

lemma qObjective_midpoint {A : V →L[ℝ] Y} {f : Y → EReal} {b : StrongDual ℝ V}
    (_hp : IsProperFn f) (hc : IsConvexFn f) {x y : V}
    (hx : f (A x) ≠ ⊤) (hy : f (A y) ≠ ⊤) :
    qObjective A f b ((1/2:ℝ) • x+(1/2:ℝ) • y) ≤
      ((qValue A f b x/2+qValue A f b y/2-‖A (x-y)‖^2/8 : ℝ) : EReal) := by
  have h := convex_finite_value hc hx hy (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  have he := quadratic_midpoint_identity A b x y
  unfold qObjective
  rw [he]
  have h' := add_le_add (le_refl (((1/2*‖A x‖^2-b x)/2+
    (1/2*‖A y‖^2-b y)/2-‖A (x-y)‖^2/8 : ℝ) : EReal)) h
  simp only [map_add,map_smul] at ⊢
  convert h' using 1
  rw [← EReal.coe_add]
  congr 1
  unfold qValue
  ring

lemma qObjective_lsc (A : V →L[ℝ] Y) (f : Y → EReal) (b : StrongDual ℝ V)
    (hl : LowerSemicontinuous f) : LowerSemicontinuous (qObjective A f b) := by
  have hg : Continuous (fun v : V => ((1/2*‖A v‖^2-b v : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp ((continuous_const.mul (A.continuous.norm.pow 2)).sub b.continuous)
  exact hg.lowerSemicontinuous.add' (hl.comp A.continuous)
    (fun _ => EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _)))

lemma qValue_lower (A : V →L[ℝ] Y) (f : Y → EReal) (b : StrongDual ℝ V)
    {α M C D : ℝ} (hα : 0 ≤ α) (hD : 0 ≤ D)
    (ha : ∀ v, α*‖v‖ ≤ ‖A v‖) (hM : ∀ v, ‖A v‖ ≤ M*‖v‖)
    (hf : ∀ y, f y ≠ ⊤ → -C-D*‖y‖ ≤ (f y).toReal)
    {v : V} (hv : f (A v) ≠ ⊤) :
    α^2/2*‖v‖^2-(D*M+‖b‖)*‖v‖-C ≤ qValue A f b v := by
  have h1 := hf (A v) hv
  have h2 := b.le_opNorm v
  have h3 := ha v
  have h4 := hM v
  have h5 := mul_le_mul_of_nonneg_left h4 hD
  have h6 : (α*‖v‖)^2 ≤ ‖A v‖^2 := (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 h3
  have hb : b v ≤ ‖b‖*‖v‖ := le_trans (le_abs_self _) h2
  unfold qValue
  nlinarith

lemma quadratic_convex (A : V →L[ℝ] Y) (b : StrongDual ℝ V) :
    ConvexOn ℝ univ (fun v => 1/2*‖A v‖^2-b v) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a c ha hc hac
  simp only [map_add,map_smul,smul_eq_mul]
  rw [norm_add_sq_real,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg ha,abs_of_nonneg hc,inner_smul_left,inner_smul_right]
  have hn := sq_nonneg ‖A x-A y‖
  rw [norm_sub_sq_real] at hn
  have hp := mul_nonneg (mul_nonneg ha hc) hn
  simp only [starRingEnd_apply, star_trivial] at ⊢
  have he : c=1-a := by linarith
  rw [he] at hp ⊢
  nlinarith

lemma qObjective_convex (A : V →L[ℝ] Y) (f : Y → EReal) (b : StrongDual ℝ V)
    (hp : IsProperFn f) (hc : IsConvexFn f) : IsConvexFn (qObjective A f b) := by
  intro p hp' q hq a c ha hc' hac
  have hpf : f (A p.1) ≠ ⊤ := qObjective_ne_top_iff.mp
    (ne_of_lt (lt_of_le_of_lt hp' (EReal.coe_lt_top p.2)))
  have hqf : f (A q.1) ≠ ⊤ := qObjective_ne_top_iff.mp
    (ne_of_lt (lt_of_le_of_lt hq (EReal.coe_lt_top q.2)))
  have hpv : qValue A f b p.1 ≤ p.2 :=
    EReal.coe_le_coe_iff.mp ((qObjective_eq hp hpf) ▸ hp')
  have hqv : qValue A f b q.1 ≤ q.2 :=
    EReal.coe_le_coe_iff.mp ((qObjective_eq hp hqf) ▸ hq)
  have hgv := convex_finite_value hc hpf hqf ha hc' hac
  have hfv := (quadratic_convex A b).2 (mem_univ p.1) (mem_univ q.1) ha hc' hac
  change qObjective A f b (a • p.1+c • q.1) ≤ ((a*p.2+c*q.2 : ℝ) : EReal)
  unfold qObjective
  simp only [map_add,map_smul]
  apply (add_le_add (le_refl _) hgv).trans
  rw [← EReal.coe_add,EReal.coe_le_coe_iff]
  have hh := add_le_add (mul_le_mul_of_nonneg_left hpv ha)
    (mul_le_mul_of_nonneg_left hqv hc')
  unfold qValue at hh
  simp only [map_add,map_smul,smul_eq_mul] at hfv ⊢
  nlinarith

end GabayApproximationProof
-- END QuadraticObjective

-- BEGIN CoerciveAlgebra
open Filter Topology Set InertialFB.IFB
namespace GabayApproximationProof

lemma quadratic_sublevel_bound {a L C B : ℝ} (ha : 0<a) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t : ℝ, 0 ≤ t → a*t^2-L*t-C ≤ B → t ≤ R := by
  refine ⟨(|L|+|C+B|+a+1)/a, by positivity, ?_⟩
  intro t ht hb
  by_contra hn
  have hlarge : |L|+|C+B|+a+1 < a*t := by simpa only [mul_comm] using (div_lt_iff₀ ha).mp (lt_of_not_ge hn)
  have ht1 : 1<t := by nlinarith [abs_nonneg L,abs_nonneg (C+B)]
  have hL := le_abs_self L
  have hC := le_abs_self (C+B)
  have hp := mul_pos (by linarith [abs_nonneg (C+B)] : 0<a*t-L) (by linarith : 0<t-1)
  nlinarith

lemma quadratic_global_lower {a L C : ℝ} (ha : 0<a) :
    ∃ B : ℝ, ∀ t : ℝ, B ≤ a*t^2-L*t-C := by
  refine ⟨-C-L^2/(4*a), ?_⟩
  intro t
  have h := sq_nonneg (2*a*t-L)
  have he : L^2/(4*a)*(4*a)=L^2 := div_mul_cancel₀ _ (by positivity)
  nlinarith

end GabayApproximationProof
-- END CoerciveAlgebra

-- BEGIN WeakInfrastructure
open Set Filter Topology
open scoped RealInnerProductSpace
namespace GabayApproximationProof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable def weakEmbed (x : H) : WeakDual ℝ H :=
  (InnerProductSpace.toDual ℝ H x).toWeakDual

noncomputable def weakDecode (z : WeakDual ℝ H) : H :=
  (InnerProductSpace.toDual ℝ H).symm z.toStrongDual

@[simp] lemma weakDecode_embed (x : H) : weakDecode (weakEmbed x) = x := by
  simp [weakDecode, weakEmbed]

@[simp] lemma weakEmbed_decode (z : WeakDual ℝ H) : weakEmbed (weakDecode z) = z := by
  simp [weakDecode, weakEmbed]

@[simp] lemma weakEmbed_apply (x v : H) : weakEmbed x v = inner ℝ x v := rfl

lemma dual_decode (f : StrongDual ℝ H) (z : WeakDual ℝ H) :
    f (weakDecode z) = z ((InnerProductSpace.toDual ℝ H).symm f) := by
  rw [← InnerProductSpace.toDual_symm_apply (y := f), real_inner_comm]
  exact InnerProductSpace.toDual_symm_apply

lemma continuous_dual_decode (f : StrongDual ℝ H) :
    Continuous (fun z : WeakDual ℝ H => f (weakDecode z)) := by
  simp_rw [dual_decode]
  exact WeakBilin.eval_continuous _ _

lemma tendsto_weakEmbed_iff {ι : Type*} {l : Filter ι} {u : ι → H} {x : H} :
    Tendsto (fun i => weakEmbed (u i)) l (𝓝 (weakEmbed x)) ↔
      ∀ v : H, Tendsto (fun i => inner ℝ (u i) v) l (𝓝 (inner ℝ x v)) := by
  exact tendsto_iff_forall_eval_tendsto_topDualPairing

lemma isCompact_weakBall (C : ℝ) :
    IsCompact {z : WeakDual ℝ H | ‖weakDecode z‖ ≤ C} := by
  have he : {z : WeakDual ℝ H | ‖weakDecode z‖ ≤ C} =
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) C := by
    ext z
    simp [weakDecode, Metric.mem_closedBall, dist_zero_right]
  rw [he]
  exact WeakDual.isCompact_closedBall 0 C

lemma isClosed_weak_preimage {s : Set H} (hs : IsClosed s) (hc : Convex ℝ s) :
    IsClosed (weakDecode ⁻¹' s : Set (WeakDual ℝ H)) := by
  apply isClosed_of_closure_subset
  intro z hz
  by_contra hn
  obtain ⟨f, a, hfa, haf⟩ := geometric_hahn_banach_closed_point hc hs hn
  have he : closure (weakDecode ⁻¹' s : Set (WeakDual ℝ H)) ⊆
      {z : WeakDual ℝ H | f (weakDecode z) ≤ a} := by
    apply closure_minimal
    · intro w hw
      exact (hfa _ hw).le
    · exact isClosed_le (continuous_dual_decode f) continuous_const
  exact (he hz).not_gt haf

lemma lowerSemicontinuous_weak {f : H → EReal} (hf : LowerSemicontinuous f)
    (hc : ∀ a : EReal, Convex ℝ {x | f x ≤ a}) :
    LowerSemicontinuous (fun z : WeakDual ℝ H => f (weakDecode z)) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  exact isClosed_weak_preimage (hf.isClosed_preimage a) (hc a)

omit [CompleteSpace H] in
lemma convex_sublevel_of_epigraph {f : H → EReal}
    (hp : ∀ x, f x ≠ ⊥) (hc : InertialFB.IFB.IsConvexFn f) (a : EReal) :
    Convex ℝ {x | f x ≤ a} := by
  cases a with
  | bot =>
    have he : {x | f x ≤ ⊥} = (∅ : Set H) := by
      ext x
      simp [hp x]
    rw [he]
    exact convex_empty
  | top => simpa using (convex_univ : Convex ℝ (Set.univ : Set H))
  | coe a =>
    intro x hx y hy u v hu hv huv
    have hh := hc (x := (x, a)) (y := (y, a)) hx hy hu hv huv
    change f (u • x + v • y) ≤ ↑(u * a + v * a) at hh
    have ha : u * a + v * a = a := by rw [← add_mul, huv, one_mul]
    change f (u • x + v • y) ≤ (a : EReal)
    simpa only [ha] using hh

lemma lowerSemicontinuous_weak_of_epigraph {f : H → EReal}
    (hp : ∀ x, f x ≠ ⊥) (hc : InertialFB.IFB.IsConvexFn f)
    (hf : LowerSemicontinuous f) :
    LowerSemicontinuous (fun z : WeakDual ℝ H => f (weakDecode z)) :=
  lowerSemicontinuous_weak hf (convex_sublevel_of_epigraph hp hc)

lemma exists_min_on_ball {f : H → EReal} (hf : LowerSemicontinuous f)
    (hc : ∀ a : EReal, Convex ℝ {x | f x ≤ a}) {C : ℝ} (hC : 0 ≤ C) :
    ∃ x : H, ‖x‖ ≤ C ∧ ∀ y : H, ‖y‖ ≤ C → f x ≤ f y := by
  have hn : ({z : WeakDual ℝ H | ‖weakDecode z‖ ≤ C} : Set (WeakDual ℝ H)).Nonempty :=
    ⟨weakEmbed 0, by simpa using hC⟩
  obtain ⟨z, hz, hm⟩ := LowerSemicontinuousOn.exists_isMinOn hn
    (isCompact_weakBall C) ((lowerSemicontinuous_weak hf hc).lowerSemicontinuousOn _)
  refine ⟨weakDecode z, hz, ?_⟩
  intro y hy
  have hh := hm (show weakEmbed y ∈ {z : WeakDual ℝ H | ‖weakDecode z‖ ≤ C} by simpa using hy)
  change f (weakDecode z) ≤ f (weakDecode (weakEmbed y)) at hh
  simpa only [weakDecode_embed] using hh

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

lemma tendsto_weakEmbed_map {ι : Type*} {l : Filter ι} {u : ι → H} {x : H}
    (hu : Tendsto (fun i => weakEmbed (u i)) l (𝓝 (weakEmbed x))) (A : H →L[ℝ] K) :
    Tendsto (fun i => weakEmbed (A (u i))) l (𝓝 (weakEmbed (A x))) := by
  rw [tendsto_weakEmbed_iff] at hu ⊢
  intro v
  simpa only [ContinuousLinearMap.adjoint_inner_right] using hu (A.adjoint v)

lemma continuous_weakMap (A : H →L[ℝ] K) :
    Continuous (fun z : WeakDual ℝ H => weakEmbed (A (weakDecode z))) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hu : Tendsto (fun w : WeakDual ℝ H => weakEmbed (weakDecode w))
      (𝓝 z) (𝓝 (weakEmbed (weakDecode z))) := by
    simp only [weakEmbed_decode]
    exact tendsto_id
  exact tendsto_weakEmbed_map hu A

lemma exists_weak_cluster {ι : Type*} {l : Filter ι} [NeBot l] {u : ι → H} {C : ℝ}
    (hu : ∀ᶠ i in l, ‖u i‖ ≤ C) :
    ∃ x : H, ‖x‖ ≤ C ∧ MapClusterPt (weakEmbed x) l (fun i => weakEmbed (u i)) := by
  obtain ⟨z, hz, hc⟩ := (isCompact_weakBall (H := H) C).exists_mapClusterPt
    (Filter.le_principal_iff.mpr (show ∀ᶠ i in l, weakEmbed (u i) ∈
      {z : WeakDual ℝ H | ‖weakDecode z‖ ≤ C} by
      simpa only [Set.mem_ofPred_eq, weakDecode_embed] using hu))
  exact ⟨weakDecode z, hz, by simpa only [weakEmbed_decode] using hc⟩

end GabayApproximationProof
-- END WeakInfrastructure

-- BEGIN WeakMinimum
open Filter Topology Set InertialFB.IFB
namespace GabayApproximationProof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma exists_minimum_of_bounded_sublevel (f : H → EReal)
    (hp : ∀ x, f x ≠ ⊥) (hc : IsConvexFn f) (hl : LowerSemicontinuous f)
    (x0 : H) (hx0 : f x0 ≠ ⊤) (R : ℝ)
    (hR : ∀ x, f x ≤ f x0 → ‖x‖ ≤ R) :
    ∃ x, f x ≠ ⊤ ∧ ∀ y, f x ≤ f y := by
  let S : Set (WeakDual ℝ H) := {z | f (weakDecode z) ≤ f x0}
  have hclosed : IsClosed S :=
    (lowerSemicontinuous_weak_of_epigraph hp hc hl).isClosed_preimage _
  have hcompact : IsCompact S := (isCompact_weakBall R).of_isClosed_subset hclosed
    (fun z hz => hR _ hz)
  have hnonempty : S.Nonempty := ⟨weakEmbed x0, by simp [S]⟩
  obtain ⟨z,hz,hmin⟩ := ((lowerSemicontinuous_weak_of_epigraph hp hc hl).lowerSemicontinuousOn S).exists_isMinOn
    hnonempty hcompact
  refine ⟨weakDecode z, ne_of_lt (lt_of_le_of_lt hz (lt_top_iff_ne_top.mpr hx0)), ?_⟩
  intro y
  by_cases hy : f y ≤ f x0
  · have hh := hmin (by simpa [S] using hy : weakEmbed y ∈ S)
    change f (weakDecode z) ≤ f (weakDecode (weakEmbed y)) at hh
    simpa only [weakDecode_embed] using hh
  · exact hz.trans (le_of_not_ge hy)

end GabayApproximationProof
-- END WeakMinimum

-- BEGIN MinimizerExistence
open Filter Topology Set InertialFB.IFB
open scoped RealInnerProductSpace
namespace GabayApproximationProof

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

omit [CompleteSpace V] in
lemma qObjective_ne_bot (A : V →L[ℝ] Y) (f : Y → EReal) (b : StrongDual ℝ V)
    (hp : IsProperFn f) (v : V) : qObjective A f b v ≠ ⊥ := by
  exact EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _,hp.1 _⟩

lemma qObjective_exists_unique (A : V →L[ℝ] Y) (f : Y → EReal) (b : StrongDual ℝ V)
    (hp : IsProperFn f) (hc : IsConvexFn f) (hl : LowerSemicontinuous f)
    {α : ℝ} (hα : 0<α) (ha : ∀ v, α*‖v‖ ≤ ‖A v‖)
    (hfeas : ∃ v, f (A v) ≠ ⊤) :
    ∃! x, qObjective A f b x ≠ ⊤ ∧ ∀ y, qObjective A f b x ≤ qObjective A f b y := by
  obtain ⟨C,D,_hC,hD,hf⟩ := exists_linear_norm_lower hp hc hl
  obtain ⟨v0,hv0⟩ := hfeas
  obtain ⟨R,_,hR⟩ := quadratic_sublevel_bound (L:=D*‖A‖+‖b‖) (C:=C)
    (B:=qValue A f b v0) (show 0<α^2/2 by positivity)
  have hbdd : ∀ v, qObjective A f b v ≤ qObjective A f b v0 → ‖v‖ ≤ R := by
    intro v hv
    have hfin : f (A v) ≠ ⊤ := qObjective_ne_top_iff.mp
      (ne_of_lt (lt_of_le_of_lt hv (lt_top_iff_ne_top.mpr (qObjective_ne_top_iff.mpr hv0))))
    have hval : qValue A f b v ≤ qValue A f b v0 := by
      rw [qObjective_eq hp hfin,qObjective_eq hp hv0,EReal.coe_le_coe_iff] at hv
      exact hv
    exact hR _ (norm_nonneg _) ((qValue_lower A f b hα.le hD ha A.le_opNorm hf hfin).trans hval)
  obtain ⟨x,hxt,hmin⟩ := exists_minimum_of_bounded_sublevel (qObjective A f b)
    (qObjective_ne_bot A f b hp) (qObjective_convex A f b hp hc) (qObjective_lsc A f b hl)
    v0 (qObjective_ne_top_iff.mpr hv0) R hbdd
  refine ⟨x,⟨hxt,hmin⟩,?_⟩
  intro y hy
  have hx := qObjective_ne_top_iff.mp hxt
  have hyf := qObjective_ne_top_iff.mp hy.1
  have he : qValue A f b x = qValue A f b y := by
    apply EReal.coe_injective
    rw [← qObjective_eq hp hx,← qObjective_eq hp hyf]
    exact le_antisymm (hmin y) (hy.2 x)
  have hm := (hmin ((1/2:ℝ) • x+(1/2:ℝ) • y)).trans (qObjective_midpoint hp hc hx hyf)
  rw [qObjective_eq hp hx,EReal.coe_le_coe_iff] at hm
  have hz : ‖A (x-y)‖=0 := by nlinarith [sq_nonneg ‖A (x-y)‖]
  have hd := ha (x-y)
  have hz' : ‖x-y‖=0 := by nlinarith [norm_nonneg (x-y)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz')).symm

end GabayApproximationProof
-- END MinimizerExistence

-- BEGIN NativeExistence
open Filter Topology Set InertialFB.IFB GabayMercier.Approximation
namespace GabayApproximationProof

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

omit [CompleteSpace Y] in
lemma continuous_exists_unique (A : V →L[ℝ] Y) (f : Y → EReal) (b : StrongDual ℝ V)
    {α : ℝ} {Vh : ℕ → Submodule ℝ V} {Ah : (k : ℕ) → Vh k →L[ℝ] Y} {α' M : ℝ}
    (h : ApproxHyp A f α Vh Ah α' M) :
    ∃! v, GabayMercier.DualAlgorithm.IsSolution A halfSq f b v := by
  have ha : ∀ v, α*‖v‖ ≤ ‖A v‖ := by
    intro v
    apply (sq_le_sq₀ (mul_nonneg h.α_pos.le (norm_nonneg _)) (norm_nonneg _)).mp
    simpa only [mul_pow] using h.bddBelow v
  exact qObjective_exists_unique A f b h.f₂_proper h.f₂_convex h.f₂_lsc h.α_pos ha h.feasible

omit [CompleteSpace V] [CompleteSpace Y] in
lemma recovery_values (A : V →L[ℝ] Y) (f : Y → EReal) (b : StrongDual ℝ V)
    {α : ℝ} {Vh : ℕ → Submodule ℝ V} {Ah : (k : ℕ) → Vh k →L[ℝ] Y} {α' M : ℝ}
    (h : ApproxHyp A f α Vh Ah α' M) (v : V) (hv : f (A v) ≠ ⊤) :
    ∃ w : (k : ℕ) → Vh k, Tendsto (fun k => (w k : V)) atTop (𝓝 v) ∧
      (∀ᶠ k in atTop, f (Ah k (w k)) ≠ ⊤) ∧
      Tendsto (fun k => 1/2*‖Ah k (w k)‖^2-b (w k)+(f (Ah k (w k))).toReal)
        atTop (𝓝 (qValue A f b v)) := by
  obtain ⟨w,hw,hf⟩ := h.h43 v
  refine ⟨w,hw,hf.eventually_ne hv,?_⟩
  have himg := h.iii w v hw
  have hreal := (EReal.tendsto_toReal hv (h.f₂_proper.1 _)).comp hf
  exact ((tendsto_const_nhds.mul (himg.norm.pow 2)).sub (b.continuous.tendsto v |>.comp hw)).add hreal

omit [CompleteSpace V] [CompleteSpace Y] in
lemma discrete_exists_unique (A : V →L[ℝ] Y) (f : Y → EReal) (b : StrongDual ℝ V)
    {α : ℝ} {Vh : ℕ → Submodule ℝ V} [∀ k, FiniteDimensional ℝ (Vh k)]
    {Ah : (k : ℕ) → Vh k →L[ℝ] Y} {α' M : ℝ}
    (h : ApproxHyp A f α Vh Ah α' M) :
    ∀ᶠ k in atTop, ∃! w : Vh k, IsSolutionH (Ah k) f b w := by
  obtain ⟨v,hv⟩ := h.feasible
  obtain ⟨w,_,hw,_⟩ := recovery_values A f b h v hv
  filter_upwards [hw] with k hk
  exact qObjective_exists_unique (Ah k) f (b.comp (Vh k).subtypeL)
    h.f₂_proper h.f₂_convex h.f₂_lsc h.α'_pos (fun u => (h.i k u).1) ⟨w k,hk⟩

end GabayApproximationProof
-- END NativeExistence

-- BEGIN SequenceBounds
open Filter Topology Set InertialFB.IFB
namespace GabayApproximationProof

variable {V : Type*} [SeminormedAddCommGroup V]

lemma forall_norm_bound_of_eventually {u : ℕ → V} {B : ℝ}
    (h : ∀ᶠ k in atTop, ‖u k‖ ≤ B) : ∃ C : ℝ, ∀ k, ‖u k‖ ≤ C := by
  obtain ⟨K,hK⟩ := eventually_atTop.1 h
  refine ⟨max B (∑ i ∈ Finset.range K, ‖u i‖), ?_⟩
  intro k
  by_cases hk : K ≤ k
  · exact (hK k hk).trans (le_max_left _ _)
  · apply le_trans _ (le_max_right _ _)
    exact Finset.single_le_sum (fun i _ => norm_nonneg (u i))
      (Finset.mem_range.mpr (lt_of_not_ge hk))

end GabayApproximationProof
-- END SequenceBounds

-- BEGIN DiscreteBounds
open Filter Topology Set InertialFB.IFB GabayMercier.Approximation
namespace GabayApproximationProof

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

noncomputable def dValue {W : Submodule ℝ V} (B : W →L[ℝ] Y) (f : Y → EReal)
    (b : StrongDual ℝ V) (w : W) : ℝ := qValue B f (b.comp W.subtypeL) w

omit [CompleteSpace V] [CompleteSpace Y] in
lemma discrete_value_le {W : Submodule ℝ V} {B : W →L[ℝ] Y} {f : Y → EReal}
    {b : StrongDual ℝ V} (hp : IsProperFn f) {v w : W}
    (hv : IsSolutionH B f b v) (hw : f (B w) ≠ ⊤) :
    dValue B f b v ≤ dValue B f b w := by
  have hfin : f (B v) ≠ ⊤ := (qObjective_ne_top_iff (b := b.comp W.subtypeL)).mp hv.1
  have hh := hv.2 w
  change qObjective B f (b.comp W.subtypeL) v ≤ qObjective B f (b.comp W.subtypeL) w at hh
  rw [qObjective_eq hp hfin,qObjective_eq hp hw,EReal.coe_le_coe_iff] at hh
  exact hh

omit [CompleteSpace V] [CompleteSpace Y] in
lemma minimizers_eventually_bounded (A : V →L[ℝ] Y) (f : Y → EReal) (b : StrongDual ℝ V)
    {α : ℝ} {Vh : ℕ → Submodule ℝ V} {Ah : (k : ℕ) → Vh k →L[ℝ] Y} {α' M : ℝ}
    (h : ApproxHyp A f α Vh Ah α' M) (vs : V)
    (hvs : GabayMercier.DualAlgorithm.IsSolution A halfSq f b vs)
    (vh : (k : ℕ) → Vh k) (hvh : ∀ᶠ k in atTop, IsSolutionH (Ah k) f b (vh k)) :
    ∃ R : ℝ, ∀ᶠ k in atTop, ‖(vh k : V)‖ ≤ R := by
  have ha' : 0 < α' := h.α'_pos
  have hvsf : f (A vs) ≠ ⊤ := qObjective_ne_top_iff.mp hvs.1
  obtain ⟨w,_,hw,hwv⟩ := recovery_values A f b h vs hvsf
  have hupper : ∀ᶠ k in atTop, dValue (Ah k) f b (w k) < qValue A f b vs+1 :=
    hwv.eventually (eventually_lt_nhds (lt_add_one _))
  obtain ⟨C,D,_hC,hD,hf⟩ := exists_linear_norm_lower h.f₂_proper h.f₂_convex h.f₂_lsc
  obtain ⟨R,_,hR⟩ := quadratic_sublevel_bound (L:=D*M+‖b‖) (C:=C)
    (B:=qValue A f b vs+1) (show 0<α'^2/2 by positivity)
  refine ⟨R,?_⟩
  filter_upwards [hvh,hw,hupper] with k hk hkw hku
  have hfin : f (Ah k (vh k)) ≠ ⊤ := (qObjective_ne_top_iff (b := b.comp (Vh k).subtypeL)).mp hk.1
  have hlower := hf _ hfin
  have hcoe := (h.i k (vh k)).1
  have hup := (h.i k (vh k)).2
  have hb : b (vh k) ≤ ‖b‖*‖(vh k : V)‖ :=
    le_trans (le_abs_self _) (b.le_opNorm _)
  have hs : (α'*‖(vh k : V)‖)^2 ≤ ‖Ah k (vh k)‖^2 :=
    (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 hcoe
  have hval := (discrete_value_le h.f₂_proper hk hkw).trans hku.le
  apply hR _ (norm_nonneg _)
  dsimp [dValue,qValue] at hval
  have hmul := mul_le_mul_of_nonneg_left hup hD
  dsimp [qValue]
  nlinarith

end GabayApproximationProof
-- END DiscreteBounds

-- BEGIN WeakLiminf
open Set Filter Topology InertialFB.IFB
open scoped RealInnerProductSpace
namespace GabayApproximationProof

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

lemma weak_tendsto_of_norm_error {ι : Type*} {l : Filter ι}
    {u : ι → V} {z : ι → Y} {x : V} (A : V →L[ℝ] Y)
    (hu : Tendsto (fun i => weakEmbed (u i)) l (𝓝 (weakEmbed x)))
    (he : Tendsto (fun i => ‖z i - A (u i)‖) l (𝓝 0)) :
    Tendsto (fun i => weakEmbed (z i)) l (𝓝 (weakEmbed (A x))) := by
  have hd : Tendsto (fun i => z i - A (u i)) l (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr he
  have ha := tendsto_weakEmbed_iff.mp (tendsto_weakEmbed_map hu A)
  apply tendsto_weakEmbed_iff.mpr
  intro y
  have hh := (hd.inner (tendsto_const_nhds (x := y))).add (ha y)
  simpa only [inner_sub_left, inner_zero_left, sub_add_cancel, zero_add] using hh

noncomputable def splitObjective (f : Y → EReal) (b : StrongDual ℝ V) (v : V) (y : Y) : EReal :=
  ((1/2*‖y‖^2-b v : ℝ) : EReal)+f y

lemma splitObjective_weak_lsc (f : Y → EReal) (b : StrongDual ℝ V)
    (hp : IsProperFn f) (hc : IsConvexFn f) (hl : LowerSemicontinuous f) :
    LowerSemicontinuous (fun p : WeakDual ℝ V × WeakDual ℝ Y =>
      splitObjective f b (weakDecode p.1) (weakDecode p.2)) := by
  have hnever : ∀ y, qObjective (ContinuousLinearMap.id ℝ Y) f 0 y ≠ ⊥ := by
    intro y
    exact EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, hp.1 _⟩
  have hq := lowerSemicontinuous_weak_of_epigraph hnever
    (qObjective_convex (ContinuousLinearMap.id ℝ Y) f 0 hp hc)
    (qObjective_lsc (ContinuousLinearMap.id ℝ Y) f 0 hl)
  have hb : Continuous (fun p : WeakDual ℝ V × WeakDual ℝ Y =>
      ((-b (weakDecode p.1) : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp ((continuous_dual_decode b).comp continuous_fst).neg
  have hh := hb.lowerSemicontinuous.add' (hq.comp continuous_snd)
    (fun _ => EReal.continuousAt_add (Or.inl (by simp)) (Or.inl (by simp)))
  convert hh using 1
  funext p
  simp [splitObjective, qObjective, sub_eq_add_neg, EReal.coe_add,
    add_assoc, add_comm]

lemma splitObjective_eventually_lower {ι : Type*} {l : Filter ι}
    {u : ι → V} {z : ι → Y} {x : V} (A : V →L[ℝ] Y)
    (f : Y → EReal) (b : StrongDual ℝ V)
    (hp : IsProperFn f) (hc : IsConvexFn f) (hl : LowerSemicontinuous f)
    (hu : Tendsto (fun i => weakEmbed (u i)) l (𝓝 (weakEmbed x)))
    (he : Tendsto (fun i => ‖z i - A (u i)‖) l (𝓝 0))
    {a : EReal} (ha : a < qObjective A f b x) :
    ∀ᶠ i in l, a < splitObjective f b (u i) (z i) := by
  have hz := weak_tendsto_of_norm_error A hu he
  have hpair := hu.prodMk_nhds hz
  have hlocal := splitObjective_weak_lsc f b hp hc hl (weakEmbed x, weakEmbed (A x)) a
    (by simpa only [weakDecode_embed, splitObjective, qObjective] using ha)
  simpa only [weakDecode_embed] using hpair.eventually hlocal

lemma eventually_lower_of_minimum {ι : Type*} {l : Filter ι} [NeBot l]
    {u : ι → V} {z : ι → Y} (A : V →L[ℝ] Y)
    (f : Y → EReal) (b : StrongDual ℝ V)
    (hp : IsProperFn f) (hc : IsConvexFn f) (hl : LowerSemicontinuous f)
    {C : ℝ} (hu : ∀ᶠ i in l, ‖u i‖ ≤ C)
    (he : Tendsto (fun i => ‖z i - A (u i)‖) l (𝓝 0))
    {m a : EReal} (hm : ∀ x, m ≤ qObjective A f b x) (ha : a < m) :
    ∀ᶠ i in l, a < splitObjective f b (u i) (z i) := by
  by_contra hn
  have hfreq : ∃ᶠ i in l, splitObjective f b (u i) (z i) ≤ a := by
    simpa only [Filter.Frequently, not_le] using hn
  let L : Filter ι := l ⊓ 𝓟 {i | splitObjective f b (u i) (z i) ≤ a}
  have : NeBot L := Filter.frequently_iff_neBot.mp hfreq
  obtain ⟨x, _, hx⟩ := exists_weak_cluster (hu.filter_mono (show L ≤ l from inf_le_left))
  let F : Filter ι := Filter.comap (fun i => weakEmbed (u i)) (𝓝 (weakEmbed x)) ⊓ L
  have : NeBot F := Filter.neBot_inf_comap_iff_map'.mpr hx
  have hFl : F ≤ l := inf_le_right.trans inf_le_left
  have hw : Tendsto (fun i => weakEmbed (u i)) F (𝓝 (weakEmbed x)) :=
    Filter.tendsto_comap.mono_left inf_le_left
  have hlow := splitObjective_eventually_lower A f b hp hc hl hw (he.mono_left hFl)
    (ha.trans_le (hm x))
  have hbad : ∀ᶠ i in F, splitObjective f b (u i) (z i) ≤ a :=
    Filter.le_principal_iff.mp (show F ≤ 𝓟 {i | splitObjective f b (u i) (z i) ≤ a} from
      inf_le_right.trans inf_le_right)
  obtain ⟨i, hi, hi'⟩ := (hlow.and hbad).exists
  exact (not_lt_of_ge hi') hi

end GabayApproximationProof
-- END WeakLiminf

-- BEGIN OptimalValues
open Filter Topology Set InertialFB.IFB GabayMercier.Approximation
namespace GabayApproximationProof

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

lemma minimizer_values_tendsto (A : V →L[ℝ] Y) (f : Y → EReal) (b : StrongDual ℝ V)
    {α : ℝ} {Vh : ℕ → Submodule ℝ V} {Ah : (k : ℕ) → Vh k →L[ℝ] Y} {α' M : ℝ}
    (h : ApproxHyp A f α Vh Ah α' M) (vs : V)
    (hvs : GabayMercier.DualAlgorithm.IsSolution A halfSq f b vs)
    (vh : (k : ℕ) → Vh k) (hvh : ∀ᶠ k in atTop, IsSolutionH (Ah k) f b (vh k)) :
    Tendsto (fun k => dValue (Ah k) f b (vh k)) atTop (𝓝 (qValue A f b vs)) := by
  have hvsf : f (A vs) ≠ ⊤ := qObjective_ne_top_iff.mp hvs.1
  obtain ⟨R,hR⟩ := minimizers_eventually_bounded A f b h vs hvs vh hvh
  obtain ⟨C,hC⟩ := forall_norm_bound_of_eventually hR
  have herr := h.iv C vh hC
  have hm : ∀ x, (qValue A f b vs : EReal) ≤ qObjective A f b x := by
    intro x
    rw [← qObjective_eq h.f₂_proper hvsf]
    exact hvs.2 x
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have he := eventually_lower_of_minimum A f b h.f₂_proper h.f₂_convex h.f₂_lsc
      hR herr hm (EReal.coe_lt_coe_iff.mpr ha)
    filter_upwards [he,hvh] with k hk hmin
    have hfin : f (Ah k (vh k)) ≠ ⊤ := (qObjective_ne_top_iff (b := b.comp (Vh k).subtypeL)).mp hmin.1
    change (a : EReal) < qObjective (Ah k) f (b.comp (Vh k).subtypeL) (vh k) at hk
    rw [qObjective_eq h.f₂_proper hfin,EReal.coe_lt_coe_iff] at hk
    exact hk
  · intro a ha
    obtain ⟨w,_,hw,hwv⟩ := recovery_values A f b h vs hvsf
    have hu : ∀ᶠ k in atTop, dValue (Ah k) f b (w k) < a :=
      hwv.eventually (eventually_lt_nhds ha)
    filter_upwards [hvh,hw,hu] with k hk hkw hku
    exact (discrete_value_le h.f₂_proper hk hkw).trans_lt hku

end GabayApproximationProof
-- END OptimalValues

-- BEGIN StrongConvergence
open Filter Topology Set InertialFB.IFB GabayMercier.Approximation
namespace GabayApproximationProof

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

lemma minimizers_tendsto (A : V →L[ℝ] Y) (f : Y → EReal) (b : StrongDual ℝ V)
    {α : ℝ} {Vh : ℕ → Submodule ℝ V} {Ah : (k : ℕ) → Vh k →L[ℝ] Y} {α' M : ℝ}
    (h : ApproxHyp A f α Vh Ah α' M) (vs : V)
    (hvs : GabayMercier.DualAlgorithm.IsSolution A halfSq f b vs)
    (vh : (k : ℕ) → Vh k) (hvh : ∀ᶠ k in atTop, IsSolutionH (Ah k) f b (vh k)) :
    Tendsto (fun k => (vh k : V)) atTop (𝓝 vs) := by
  have ha' : 0 < α' := h.α'_pos
  have hvsf : f (A vs) ≠ ⊤ := qObjective_ne_top_iff.mp hvs.1
  obtain ⟨w,hw,hwf,hwv⟩ := recovery_values A f b h vs hvsf
  change Tendsto (fun k => dValue (Ah k) f b (w k)) atTop (𝓝 (qValue A f b vs)) at hwv
  have hvv := minimizer_values_tendsto A f b h vs hvs vh hvh
  have hbound : ∀ᶠ k in atTop, ‖(vh k : V)-(w k : V)‖^2 ≤
      4*(dValue (Ah k) f b (w k)-dValue (Ah k) f b (vh k))/α'^2 := by
    filter_upwards [hvh,hwf] with k hk hkw
    have hfin : f (Ah k (vh k)) ≠ ⊤ := (qObjective_ne_top_iff (b := b.comp (Vh k).subtypeL)).mp hk.1
    have hmid := hk.2 ((1/2:ℝ) • vh k+(1/2:ℝ) • w k)
    have hg := qObjective_midpoint (b:=b.comp (Vh k).subtypeL) h.f₂_proper h.f₂_convex hfin hkw
    have hh := hmid.trans hg
    change qObjective (Ah k) f (b.comp (Vh k).subtypeL) (vh k) ≤ _ at hh
    rw [qObjective_eq h.f₂_proper hfin,EReal.coe_le_coe_iff] at hh
    have hl := (h.i k (vh k-w k)).1
    have hs : (α'*‖(vh k : V)-(w k : V)‖)^2 ≤ ‖Ah k (vh k-w k)‖^2 :=
      (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 hl
    apply (le_div_iff₀ (sq_pos_of_pos h.α'_pos)).2
    dsimp [dValue]
    nlinarith
  have hrhs : Tendsto (fun k => 4*(dValue (Ah k) f b (w k)-dValue (Ah k) f b (vh k))/α'^2)
      atTop (𝓝 0) := by
    simpa only [sub_self,mul_zero,zero_div] using (tendsto_const_nhds.mul (hwv.sub hvv)).div_const (α'^2)
  have hs := squeeze_zero' (Eventually.of_forall (fun k => sq_nonneg ‖(vh k : V)-(w k : V)‖)) hbound hrhs
  have hn : Tendsto (fun k => ‖(vh k : V)-(w k : V)‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using hs.sqrt
  have hd : Tendsto (fun k => (vh k : V)-(w k : V)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hn
  simpa only [sub_add_cancel,zero_add] using hd.add hw

end GabayApproximationProof
-- END StrongConvergence

-- BEGIN NativeRoot
open Filter Topology InertialFB.IFB

namespace GabayMercier.Approximation

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- Theorem 4.1: eventual unique discrete solutions converge strongly in `V`. -/
theorem theorem_4_1 (A : V →L[ℝ] Y) (f₂ : Y → EReal) (b : StrongDual ℝ V)
    (α : ℝ) (Vh : ℕ → Submodule ℝ V) [∀ k, FiniteDimensional ℝ (Vh k)]
    (Ah : (k : ℕ) → Vh k →L[ℝ] Y) (α' M : ℝ)
    (h : ApproxHyp A f₂ α Vh Ah α' M) :
    (∃! vs : V, GabayMercier.DualAlgorithm.IsSolution A halfSq f₂ b vs) ∧
    ∀ vs : V, GabayMercier.DualAlgorithm.IsSolution A halfSq f₂ b vs →
      (∀ᶠ k in atTop, ∃! w : Vh k, IsSolutionH (Ah k) f₂ b w) ∧
      ∀ vh : (k : ℕ) → Vh k, (∀ᶠ k in atTop, IsSolutionH (Ah k) f₂ b (vh k)) →
        Tendsto (fun k => (vh k : V)) atTop (𝓝 vs) := by
  refine ⟨GabayApproximationProof.continuous_exists_unique A f₂ b h, ?_⟩
  intro vs hvs
  refine ⟨GabayApproximationProof.discrete_exists_unique A f₂ b h, ?_⟩
  intro vh hvh
  exact GabayApproximationProof.minimizers_tendsto A f₂ b h vs hvs vh hvh

end GabayMercier.Approximation
-- END NativeRoot

open Filter Topology InertialFB.IFB GabayMercier.Approximation

theorem solution {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (A : V →L[ℝ] Y) (f₂ : Y → EReal) (b : StrongDual ℝ V)
    (α : ℝ) (Vh : ℕ → Submodule ℝ V) [∀ k, FiniteDimensional ℝ (Vh k)]
    (Ah : (k : ℕ) → Vh k →L[ℝ] Y) (α' M : ℝ)
    (h : ApproxHyp A f₂ α Vh Ah α' M) :
    (∃! vs : V, GabayMercier.DualAlgorithm.IsSolution A halfSq f₂ b vs) ∧
    ∀ vs : V, GabayMercier.DualAlgorithm.IsSolution A halfSq f₂ b vs →
      (∀ᶠ k in atTop, ∃! w : Vh k, IsSolutionH (Ah k) f₂ b w) ∧
      ∀ vh : (k : ℕ) → Vh k, (∀ᶠ k in atTop, IsSolutionH (Ah k) f₂ b (vh k)) →
        Tendsto (fun k => (vh k : V)) atTop (𝓝 vs) :=
  GabayMercier.Approximation.theorem_4_1 A f₂ b α Vh Ah α' M h
