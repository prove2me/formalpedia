-- Prove2me | solution 2 for GabayMercier.DualAlgorithm.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-17T09:22:52.524645+00:00
-- url     : https://prove2.me/submissions/3fff5724-3759-43f2-a9df-e6fc8b276192

-- Licensed under Apache 2.0. Complete Hilbert-space ADMM convergence.
import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_DualAlgorithm_Model

open Filter Topology InertialFB.IFB


open Set InertialFB.IFB
open scoped RealInnerProductSpace

namespace GabayADMMProof

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

lemma subgradient_monotone {f : Y → EReal} (hp : IsProperFn f)
    {x y gx gy : Y} (hx : IsSubgradient f x gx) (hy : IsSubgradient f y gy) :
    0 ≤ inner ℝ (gx-gy) (x-y) := by
  have hxy := hx.2 y
  have hyx := hy.2 x
  rw [← EReal.coe_toReal hx.1 (hp.1 x), ← EReal.coe_toReal hy.1 (hp.1 y),
    ← EReal.coe_add, EReal.coe_le_coe_iff] at hxy hyx
  simp only [inner_sub_left, inner_sub_right] at hxy hyx ⊢
  linarith

lemma convex_finite_value {f : Y → EReal} (_hp : IsProperFn f) (hc : IsConvexFn f)
    {x y : Y} (hx : f x ≠ ⊤) (hy : f y ≠ ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    f (a • x+b • y) ≤ ((a*(f x).toReal+b*(f y).toReal : ℝ) : EReal) := by
  have hfx : f x ≤ ((f x).toReal : EReal) := EReal.le_coe_toReal hx
  have hfy : f y ≤ ((f y).toReal : EReal) := EReal.le_coe_toReal hy
  have hh := hc (show (x,(f x).toReal) ∈ {p : Y × ℝ | f p.1 ≤ (p.2 : EReal)} from hfx)
    (show (y,(f y).toReal) ∈ {p : Y × ℝ | f p.1 ≤ (p.2 : EReal)} from hfy) ha hb hab
  change f (a • x+b • y) ≤ ((a • (f x).toReal+b • (f y).toReal : ℝ) : EReal) at hh
  simpa only [smul_eq_mul] using hh

end GabayADMMProof


open Set Filter Topology InertialFB.IFB

namespace GabayADMMProof

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

omit [InnerProductSpace ℝ Y] in
lemma exists_bounded_patch {f : Y → EReal} (hl : LowerSemicontinuous f)
    (hp : IsProperFn f) {y0 : Y} {R : ℝ} (hR : 0 < R)
    (hdom : ∀ y ∈ Metric.ball y0 R, f y ≠ ⊤) :
    ∃ z ∈ Metric.ball y0 R, ∃ δ > 0, ∃ M : ℝ,
      ∀ y ∈ Metric.ball z δ, f y ≤ (M : EReal) := by
  let B := Metric.ball y0 R
  let : Nonempty B := ⟨⟨y0, Metric.mem_ball_self hR⟩⟩
  let : BaireSpace B := Metric.isOpen_ball.baireSpace
  let S : ℕ → Set B := fun n => {z | f z ≤ ((n : ℝ) : EReal)}
  have hclosed : ∀ n, IsClosed (S n) := by
    intro n
    exact (hl.isClosed_preimage ((n : ℝ) : EReal)).preimage continuous_subtype_val
  have hcover : (⋃ n, S n) = univ := by
    ext z
    simp only [mem_iUnion, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt (f z).toReal
    refine ⟨n, ?_⟩
    change f z ≤ ((n : ℝ) : EReal)
    rw [← EReal.coe_toReal (hdom z z.2) (hp.1 z), EReal.coe_le_coe_iff]
    exact hn.le
  obtain ⟨n, z, hz⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  have ho : IsOpen (Subtype.val '' interior (S n)) :=
    Metric.isOpen_ball.isOpenMap_subtype_val _ isOpen_interior
  obtain ⟨δ, hδ, hd⟩ := Metric.isOpen_iff.mp ho z.1 ⟨z, hz, rfl⟩
  refine ⟨z.1, z.2, δ, hδ, n, ?_⟩
  intro y hy
  obtain ⟨w, hw, rfl⟩ := hd hy
  have hw' : w ∈ S n := interior_subset hw
  exact hw'

lemma local_upper_bound {f : Y → EReal} (hp : IsProperFn f)
    (hc : IsConvexFn f) (hl : LowerSemicontinuous f) {y0 : Y}
    (hy0 : y0 ∈ interior {y | f y ≠ ⊤}) :
    ∃ ε > 0, ∃ M : ℝ, ∀ y ∈ Metric.ball y0 ε, f y ≤ (M : EReal) := by
  obtain ⟨R, hR, hdom⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hy0)
  obtain ⟨z, hz, δ, hδ, M, hM⟩ := exists_bounded_patch hl hp hR (fun y hy => hdom hy)
  let z' := (2:ℝ) • y0-z
  have hz' : z' ∈ Metric.ball y0 R := by
    change dist ((2:ℝ) • y0-z) y0 < R
    have he : (2:ℝ) • y0-z-y0 = -(z-y0) := by module
    simpa only [Metric.mem_ball, dist_eq_norm, he, norm_neg] using hz
  have hfin : f z' ≠ ⊤ := hdom hz'
  refine ⟨δ/2, half_pos hδ, (M+(f z').toReal)/2, ?_⟩
  intro y hy
  let x := z+(2:ℝ) • (y-y0)
  have hx : x ∈ Metric.ball z δ := by
    change dist (z+(2:ℝ) • (y-y0)) z < δ
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
    have hy' : ‖y-y0‖ < δ/2 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hy
    norm_num
    linarith
  have hm := hc (show (x,M) ∈ {p : Y × ℝ | f p.1 ≤ (p.2 : EReal)} from hM x hx)
    (show (z',(f z').toReal) ∈ {p : Y × ℝ | f p.1 ≤ (p.2 : EReal)} from EReal.le_coe_toReal hfin)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2+1/2=1)
  change f ((1/2:ℝ) • x+(1/2:ℝ) • z') ≤ (((1/2:ℝ)*M+(1/2:ℝ)*(f z').toReal : ℝ) : EReal) at hm
  have he : (1/2:ℝ) • x+(1/2:ℝ) • z'=y := by dsimp [x,z']; module
  rw [he] at hm
  convert hm using 1
  congr 1
  ring

end GabayADMMProof


open Set InertialFB.IFB

namespace GabayADMMProof

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

noncomputable def perturbSet (A : V →L[ℝ] Y) (g : Y → EReal)
    (b : StrongDual ℝ V) (c : ℝ) : Set (Y × ℝ) :=
  {q | ∃ v y, ∃ s : ℝ, g y ≤ (s : EReal) ∧ q.1=y-A v ∧ s-b v-c<q.2}

lemma perturbSet_convex (A : V →L[ℝ] Y) {g : Y → EReal}
    (hg : IsConvexFn g) (b : StrongDual ℝ V) (c : ℝ) :
    Convex ℝ (perturbSet A g b c) := by
  intro q hq p hp a d ha hd had
  obtain ⟨v,y,s,hs,hq1,hq2⟩ := hq
  obtain ⟨w,z,t,ht,hp1,hp2⟩ := hp
  refine ⟨a • v+d • w,a • y+d • z,a*s+d*t,?_,?_,?_⟩
  · have hh := hg (show (y,s) ∈ {p : Y × ℝ | g p.1 ≤ (p.2 : EReal)} from hs)
      (show (z,t) ∈ {p : Y × ℝ | g p.1 ≤ (p.2 : EReal)} from ht) ha hd had
    change g (a • y+d • z) ≤ ((a*s+d*t : ℝ) : EReal) at hh
    exact hh
  · simp only [Prod.smul_fst, Prod.fst_add, hq1, hp1, map_add, map_smul]
    module
  · change a*s+d*t-b (a • v+d • w)-c < a*q.2+d*p.2
    simp only [map_add, map_smul, smul_eq_mul]
    by_cases hd0 : d=0
    · subst d
      have ha1 : a=1 := by linarith
      simpa [ha1] using hq2
    · have hdp : 0<d := lt_of_le_of_ne hd (Ne.symm hd0)
      have hsum := add_lt_add_of_le_of_lt
        (mul_le_mul_of_nonneg_left hq2.le ha) (mul_lt_mul_of_pos_left hp2 hdp)
      have hc : a*c+d*c=c := by nlinarith [congrArg (fun x : ℝ => x*c) had]
      linarith

lemma origin_not_perturbSet (A : V →L[ℝ] Y) (g : Y → EReal)
    (b : StrongDual ℝ V) (c : ℝ)
    (hmin : ∀ v, ((c+b v : ℝ) : EReal) ≤ g (A v)) :
    (0 : Y × ℝ) ∉ perturbSet A g b c := by
  rintro ⟨v,y,s,hs,hy,ht⟩
  have hy' : y=A v := by change 0=y-A v at hy; exact (sub_eq_zero.mp hy.symm)
  subst y
  have hh : c+b v ≤ s := EReal.coe_le_coe_iff.mp ((hmin v).trans hs)
  change s-b v-c<0 at ht
  linarith

lemma perturbSet_interior (A : V →L[ℝ] Y) (g : Y → EReal)
    (b : StrongDual ℝ V) (c : ℝ) (v0 : V) {ε M : ℝ} (hε : 0<ε)
    (hb : ∀ y ∈ Metric.ball (A v0) ε, g y ≤ (M : EReal)) :
    (interior (perturbSet A g b c)).Nonempty := by
  let U : Set (Y × ℝ) := Metric.ball (0:Y) ε ×ˢ Ioi (M-b v0-c)
  have ho : IsOpen U := Metric.isOpen_ball.prod isOpen_Ioi
  have hsub : U ⊆ perturbSet A g b c := by
    intro q hq
    refine ⟨v0,q.1+A v0,M,?_,by simp, hq.2⟩
    apply hb
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hq.1
  refine ⟨(0,M-b v0-c+1), interior_mono hsub ?_⟩
  rw [ho.interior_eq]
  exact ⟨Metric.mem_ball_self hε, by simp only [mem_Ioi]; linarith⟩

end GabayADMMProof


open Set

namespace GabayADMMProof

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

lemma functional_product (L : StrongDual ℝ (Y × ℝ)) (y : Y) (t : ℝ) :
    L (y,t) = L (y,0)+t*L (0,1) := by
  have he : (y,t) = (y,0)+t • (0,1) := by ext <;> simp
  rw [he, map_add, map_smul]
  rfl

lemma positive_vertical_coefficient (L : StrongDual ℝ (Y × ℝ)) (hL : L ≠ 0)
    {ε T : ℝ} (hε : 0<ε)
    (hbound : ∀ y ∈ Metric.ball (0:Y) ε, ∀ t, T<t → 0≤L (y,t)) :
    0<L (0,1) := by
  let t := max (T+1) 1
  have ht : T<t := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have htp : 0<t := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hzero := hbound 0 (Metric.mem_ball_self hε) t ht
  rw [functional_product] at hzero
  change 0 ≤ L 0+t*L (0,1) at hzero
  simp only [map_zero, zero_add] at hzero
  have hnonneg : 0≤L (0,1) := nonneg_of_mul_nonneg_right hzero htp
  apply lt_of_le_of_ne hnonneg
  intro he
  have hcoef : L (0,1)=0 := he.symm
  have hlocal : ∀ y ∈ Metric.ball (0:Y) ε, L (y,0)=0 := by
    intro y hy
    have hyneg : -y ∈ Metric.ball (0:Y) ε := by
      simpa only [Metric.mem_ball, dist_zero_right, norm_neg] using hy
    have hp := hbound y hy t ht
    have hn := hbound (-y) hyneg t ht
    rw [functional_product, hcoef, mul_zero, add_zero] at hp hn
    have hn' : L (-y,0) = -L (y,0) := by
      have hev : (-y,(0:ℝ)) = -(y,0) := by simp
      rw [hev, map_neg]
    rw [hn'] at hn
    linarith
  apply hL
  apply ContinuousLinearMap.ext
  intro q
  have hall : L (q.1,0)=0 := by
    let a : ℝ := ε/(2*(‖q.1‖+1))
    have hden : 0<2*(‖q.1‖+1) := by positivity
    have ha : 0<a := div_pos hε hden
    have ham : a*‖q.1‖<ε := by
      dsimp [a]
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ hden).2
      nlinarith [norm_nonneg q.1]
    have hb : a • q.1 ∈ Metric.ball (0:Y) ε := by
      simpa only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos ha] using ham
    have hz := hlocal (a • q.1) hb
    have hev : (a • q.1,(0:ℝ)) = a • (q.1,0) := by simp
    rw [hev, map_smul, smul_eq_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt ha)
  rw [show q=(q.1,q.2) from rfl, functional_product, hall, hcoef]
  simp

end GabayADMMProof


open Set InertialFB.IFB

namespace GabayADMMProof

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

lemma perturbation_support (A : V →L[ℝ] Y) {g : Y → EReal}
    (hg : IsConvexFn g) (b : StrongDual ℝ V) (c : ℝ)
    (hmin : ∀ v, ((c+b v : ℝ) : EReal) ≤ g (A v))
    (v0 : V) {ε M : ℝ} (hε : 0<ε)
    (hb : ∀ y ∈ Metric.ball (A v0) ε, g y ≤ (M : EReal)) :
    ∃ k : StrongDual ℝ Y, ∀ v y, ∀ s : ℝ, g y ≤ (s : EReal) →
      c+b v+k (y-A v) ≤ s := by
  have hnot := origin_not_perturbSet A g b c hmin
  obtain ⟨f,hf,hsep⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (perturbSet_convex A hg b c) (fun h => hnot (interior_subset h))
    (perturbSet_interior A g b c v0 hε hb)
  let L : StrongDual ℝ (Y × ℝ) := -f
  have hL : L≠0 := neg_ne_zero.mpr hf
  have hpos : ∀ q ∈ perturbSet A g b c, 0≤L q := by
    intro q hq
    have hh := hsep q hq
    simpa only [map_zero, neg_apply, neg_nonneg, L] using hh
  have hcylinder : ∀ y ∈ Metric.ball (0:Y) ε,
      ∀ t, M-b v0-c<t → 0≤L (y,t) := by
    intro y hy t ht
    apply hpos
    refine ⟨v0,y+A v0,M,?_,by simp,ht⟩
    apply hb
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hy
  have hβ := positive_vertical_coefficient L hL hε hcylinder
  let k : StrongDual ℝ Y := (-(L (0,1))⁻¹) •
    (L.comp (ContinuousLinearMap.inl ℝ Y ℝ))
  have hk : ∀ y, k y = -(L (y,0))/(L (0,1)) := by
    intro y
    simp only [k, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, smul_eq_mul]
    ring
  refine ⟨k, ?_⟩
  intro v y s hs
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hh := hpos (y-A v,s-b v-c+δ)
    (show (y-A v,s-b v-c+δ) ∈ perturbSet A g b c from
      ⟨v,y,s,hs,rfl,by linarith⟩)
  rw [hk]
  rw [functional_product] at hh
  have he : -(L (y-A v,0))/(L (0,1)) * L (0,1) = -L (y-A v,0) :=
    div_mul_cancel₀ _ (ne_of_gt hβ)
  nlinarith

end GabayADMMProof


open Set Filter Topology InertialFB.IFB

namespace GabayADMMProof

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

noncomputable def totalFn (f : Y → ℝ) (g : Y → EReal) (y : Y) : EReal :=
  (f y : EReal)+g y

omit [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] in
lemma totalFn_finite {f : Y → ℝ} {g : Y → EReal} {y : Y} :
    totalFn f g y ≠ ⊤ ↔ g y ≠ ⊤ :=
  EReal.add_ne_top_iff_ne_top_right (EReal.coe_ne_bot _) (EReal.coe_ne_top _)

omit [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] in
lemma totalFn_value {f : Y → ℝ} {g : Y → EReal} (hp : IsProperFn g)
    {y : Y} (hy : g y ≠ ⊤) :
    totalFn f g y = ((f y+(g y).toReal : ℝ) : EReal) := by
  unfold totalFn
  conv_lhs => rw [← EReal.coe_toReal hy (hp.1 y), ← EReal.coe_add]

lemma totalFn_convex {f : Y → ℝ} {g : Y → EReal}
    (hf : ConvexOn ℝ univ f) (hp : IsProperFn g) (hg : IsConvexFn g) :
    IsConvexFn (totalFn f g) := by
  intro p hp' q hq a b ha hb hab
  have hpf : g p.1 ≠ ⊤ := totalFn_finite.mp
    (ne_of_lt (lt_of_le_of_lt hp' (EReal.coe_lt_top p.2)))
  have hqf : g q.1 ≠ ⊤ := totalFn_finite.mp
    (ne_of_lt (lt_of_le_of_lt hq (EReal.coe_lt_top q.2)))
  have hpv : f p.1+(g p.1).toReal ≤ p.2 := by
    exact EReal.coe_le_coe_iff.mp ((totalFn_value hp hpf) ▸ hp')
  have hqv : f q.1+(g q.1).toReal ≤ q.2 := by
    exact EReal.coe_le_coe_iff.mp ((totalFn_value hp hqf) ▸ hq)
  have hgv := convex_finite_value hp hg hpf hqf ha hb hab
  have hfv := hf.2 (mem_univ p.1) (mem_univ q.1) ha hb hab
  change totalFn f g (a • p.1+b • q.1) ≤ ((a*p.2+b*q.2 : ℝ) : EReal)
  unfold totalFn
  have hs := add_le_add (le_refl (f (a • p.1+b • q.1) : EReal)) hgv
  apply hs.trans
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  have hh := add_le_add (mul_le_mul_of_nonneg_left hpv ha)
    (mul_le_mul_of_nonneg_left hqv hb)
  simp only [smul_eq_mul] at hfv
  nlinarith

lemma totalFn_local_upper [CompleteSpace Y] {f : Y → ℝ} {g : Y → EReal}
    (hf : Continuous f) (hp : IsProperFn g) (hc : IsConvexFn g)
    (hl : LowerSemicontinuous g) {y0 : Y}
    (hy0 : y0 ∈ interior {y | g y ≠ ⊤}) :
    ∃ ε > 0, ∃ M : ℝ, ∀ y ∈ Metric.ball y0 ε, totalFn f g y ≤ (M : EReal) := by
  obtain ⟨ε,hε,M,hM⟩ := local_upper_bound hp hc hl hy0
  have hn : ∀ᶠ y in nhds y0, f y < f y0+1 :=
    hf.continuousAt.eventually (gt_mem_nhds (by linarith))
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨min ε δ, lt_min hε hδ, f y0+1+M, ?_⟩
  intro y hy
  have hym : dist y y0 < min ε δ := Metric.mem_ball.mp hy
  have hye : y ∈ Metric.ball y0 ε := Metric.mem_ball.mpr (lt_of_lt_of_le hym (min_le_left _ _))
  have hyd : y ∈ Metric.ball y0 δ := Metric.mem_ball.mpr (lt_of_lt_of_le hym (min_le_right _ _))
  unfold totalFn
  rw [EReal.coe_add]
  exact add_le_add (EReal.coe_le_coe_iff.mpr (hd hyd).le) (hM y hye)

end GabayADMMProof


open Set Filter Topology InertialFB.IFB
open scoped RealInnerProductSpace

namespace GabayADMMProof

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

lemma split_subgradient {f : Y → ℝ} {g : Y → EReal} (hp : IsProperFn g)
    (hc : IsConvexFn g) {y grad lam : Y} (hf : HasGradientAt f grad y)
    (hy : g y ≠ ⊤)
    (hs : ∀ z, g z ≠ ⊤ →
      f y+(g y).toReal+inner ℝ lam (z-y) ≤ f z+(g z).toReal) :
    IsSubgradient g y (lam-grad) := by
  refine ⟨hy, ?_⟩
  intro z
  by_cases hz : g z=⊤
  · rw [hz]; exact le_top
  rw [← EReal.coe_toReal hy (hp.1 y), ← EReal.coe_toReal hz (hp.1 z),
    ← EReal.coe_add, EReal.coe_le_coe_iff]
  let d := z-y
  have hpath : HasDerivAt (fun t : ℝ => y+t • d) d 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const d |>.const_add y
  have hder : HasDerivAt (fun t : ℝ => f (y+t • d)) (inner ℝ grad d) 0 := by
    have hh := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath (by simp)
    simpa only [Function.comp_def, InnerProductSpace.toDual_apply_apply] using hh
  have hlim := hder.tendsto_slope_zero_right
  have hevent : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0),
      inner ℝ lam d-((g z).toReal-(g y).toReal) ≤
        t⁻¹ * (f (y+t • d)-f y) := by
    have hsmall : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), t<1 :=
      (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with t ht ht1
    have htp : 0<t := ht
    have hgc := convex_finite_value hp hc hy hz (by linarith : 0≤1-t) htp.le
      (by ring : (1-t)+t=1)
    have he : (1-t) • y+t • z = y+t • d := by dsimp [d]; module
    rw [he] at hgc
    have hfinite : g (y+t • d) ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt hgc (EReal.coe_lt_top _))
    have hreal : (g (y+t • d)).toReal ≤ (1-t)*(g y).toReal+t*(g z).toReal := by
      rw [← EReal.coe_toReal hfinite (hp.1 _), EReal.coe_le_coe_iff] at hgc
      exact hgc
    have hsup := hs (y+t • d) hfinite
    simp only [add_sub_cancel_left, inner_smul_right] at hsup
    have hh : t*(inner ℝ lam d-((g z).toReal-(g y).toReal)) ≤
        f (y+t • d)-f y := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr htp.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt htp), one_mul] using hmul
  have hresult : inner ℝ lam d-((g z).toReal-(g y).toReal) ≤ inner ℝ grad d := by
    apply ge_of_tendsto hlim
    simpa only [zero_add, zero_smul, add_zero, smul_eq_mul] using hevent
  rw [inner_sub_left]
  dsimp [d] at hresult
  linarith

end GabayADMMProof


open Set InertialFB.IFB GabayMercier.DualAlgorithm
open scoped RealInnerProductSpace

namespace GabayADMMProof

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

omit [CompleteSpace V] in
lemma exists_multiplier {A : V →L[ℝ] Y} {f₁ : Y → ℝ} {f₁' : Y → Y}
    {f₂ : Y → EReal} {γ α : ℝ} {b : StrongDual ℝ V} {vs : V}
    (h : StandingHyp A f₁ f₁' f₂ γ α) (hq : Qualification A f₂)
    (hvs : IsSolution A f₁ f₂ b vs) :
    ∃ lam : Y, (∀ w, inner ℝ lam (A w)=b w) ∧
      IsSubgradient f₂ (A vs) (lam-f₁' (A vs)) := by
  have hy : f₂ (A vs) ≠ ⊤ := by
    exact (EReal.add_ne_top_iff_ne_top_right (EReal.coe_ne_bot _)
      (EReal.coe_ne_top _)).mp hvs.1
  let c := f₁ (A vs)+(f₂ (A vs)).toReal-b vs
  have hval : objective A f₁ f₂ b vs = (c : EReal) := by
    unfold objective c
    conv_lhs => rw [← EReal.coe_toReal hy (h.f₂_proper.1 _), ← EReal.coe_add]
    congr 1
    ring
  have hmin : ∀ v, ((c+b v : ℝ) : EReal) ≤ totalFn f₁ f₂ (A v) := by
    intro v
    by_cases hv : f₂ (A v)=⊤
    · simp [totalFn, hv]
    have hh := hvs.2 v
    rw [hval] at hh
    unfold objective at hh
    rw [← EReal.coe_toReal hv (h.f₂_proper.1 _), ← EReal.coe_add,
      EReal.coe_le_coe_iff] at hh
    rw [totalFn_value h.f₂_proper hv, EReal.coe_le_coe_iff]
    linarith
  obtain ⟨v0,hv0⟩ := hq
  have hfcont : Continuous f₁ := continuous_iff_continuousAt.mpr
    (fun y => (h.f₁_hasGradient y).differentiableAt.continuousAt)
  obtain ⟨ε,hε,M,hM⟩ := totalFn_local_upper hfcont h.f₂_proper h.f₂_convex h.f₂_lsc hv0
  obtain ⟨k,hk⟩ := perturbation_support A
    (totalFn_convex h.f₁_convex h.f₂_proper h.f₂_convex) b c hmin v0 hε hM
  let s := f₁ (A vs)+(f₂ (A vs)).toReal
  have hs : totalFn f₁ f₂ (A vs) ≤ (s : EReal) := by
    rw [totalFn_value h.f₂_proper hy]
  have hstationary : ∀ w, k (A w)=b w := by
    intro w
    have hp := hk (vs+w) (A vs) s hs
    have hn := hk (vs-w) (A vs) s hs
    simp only [map_add, map_sub, sub_add_cancel_left, map_neg, sub_sub_cancel] at hp hn
    dsimp [c,s] at hp hn
    linarith
  let lam := (InnerProductSpace.toDual ℝ Y).symm k
  have hlam : ∀ y, inner ℝ lam y=k y := by
    intro y
    exact InnerProductSpace.toDual_symm_apply
  refine ⟨lam, fun w => (hlam _).trans (hstationary w), ?_⟩
  apply split_subgradient h.f₂_proper h.f₂_convex (h.f₁_hasGradient (A vs)) hy
  intro z hz
  have hh := hk vs z (f₁ z+(f₂ z).toReal)
    (le_of_eq (totalFn_value h.f₂_proper hz))
  rw [hlam]
  dsimp [c] at hh
  linarith

end GabayADMMProof


open Filter Topology
open scoped RealInnerProductSpace

namespace GabayADMMProof

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

abbrev rangeSpace (A : V →L[ℝ] Y) : Submodule ℝ Y :=
  (LinearMap.range (A : V →ₗ[ℝ] Y)).topologicalClosure

noncomputable def proj (A : V →L[ℝ] Y) : Y →L[ℝ] Y :=
  (rangeSpace A).starProjection

noncomputable def compProj (A : V →L[ℝ] Y) : Y →L[ℝ] Y :=
  (rangeSpace A)ᗮ.starProjection

lemma proj_add_comp (A : V →L[ℝ] Y) (x : Y) : proj A x + compProj A x = x :=
  (rangeSpace A).starProjection_add_starProjection_orthogonal x

lemma proj_image (A : V →L[ℝ] Y) (v : V) : proj A (A v) = A v := by
  apply Submodule.starProjection_eq_self_iff.mpr
  exact (LinearMap.range (A : V →ₗ[ℝ] Y)).le_topologicalClosure ⟨v, rfl⟩

lemma comp_image (A : V →L[ℝ] Y) (v : V) : compProj A (A v) = 0 := by
  have h := proj_add_comp A (A v)
  rw [proj_image] at h
  exact add_left_cancel (h.trans (add_zero _).symm)

lemma norm_decomposition (A : V →L[ℝ] Y) (x : Y) :
    ‖x‖ ^ 2 = ‖proj A x‖ ^ 2 + ‖compProj A x‖ ^ 2 :=
  Submodule.norm_sq_eq_add_norm_sq_starProjection x (rangeSpace A)

lemma inner_proj_comp (A : V →L[ℝ] Y) (x y : Y) :
    inner ℝ (proj A x) (compProj A y) = 0 := by
  exact ((rangeSpace A).mem_orthogonal _).mp
    ((rangeSpace A)ᗮ.starProjection_apply_mem y) _
    ((rangeSpace A).starProjection_apply_mem x)

lemma inner_proj_right (A : V →L[ℝ] Y) (x y : Y) :
    inner ℝ (proj A x) y = inner ℝ (proj A x) (proj A y) := by
  conv_lhs => rw [← proj_add_comp A y]
  rw [inner_add_right, inner_proj_comp, add_zero]

lemma inner_comp_right (A : V →L[ℝ] Y) (x y : Y) :
    inner ℝ (compProj A x) y = inner ℝ (compProj A x) (compProj A y) := by
  have h : inner ℝ (compProj A x) (proj A y) = 0 := by
    rw [real_inner_comm, inner_proj_comp]
  conv_lhs => rw [← proj_add_comp A y]
  rw [inner_add_right, h, zero_add]

lemma proj_eq_zero_of_inner_image (A : V →L[ℝ] Y) (x : Y)
    (h : ∀ v, inner ℝ x (A v) = 0) : proj A x = 0 := by
  apply (Submodule.starProjection_apply_eq_zero_iff (K := rangeSpace A)).mpr
  change x ∈ (LinearMap.range (A : V →ₗ[ℝ] Y)).topologicalClosureᗮ
  rw [Submodule.orthogonal_closure]
  intro y hy
  obtain ⟨v, rfl⟩ := hy
  rw [real_inner_comm]
  exact h v

end GabayADMMProof


open Filter Topology

namespace GabayADMMProof

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma stable_recurrence {x e : ℕ → Y} {c : ℝ} (hc : |c| < 1)
    (he : Tendsto e atTop (𝓝 0))
    (hx : ∀ n, x (n + 1) = c • x n + e n) : Tendsto x atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hd : 0 < (1 - |c|) * (ε / 2) := mul_pos (sub_pos.mpr hc) (half_pos hε)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp he ((1 - |c|) * (ε / 2)) hd
  have hb (m : ℕ) : ‖x (N + m)‖ ≤ |c| ^ m * ‖x N‖ + ε / 2 := by
    induction m with
    | zero => simp; positivity
    | succ m ih =>
      have he' : ‖e (N + m)‖ < (1 - |c|) * (ε / 2) := by
        simpa only [dist_zero_right] using hN (N + m) (Nat.le_add_right N m)
      calc
        ‖x (N + (m + 1))‖ = ‖c • x (N + m) + e (N + m)‖ := by rw [← Nat.add_assoc, hx]
        _ ≤ |c| * ‖x (N + m)‖ + ‖e (N + m)‖ := by
          simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le (c • x (N + m)) (e (N + m))
        _ ≤ |c| * (|c| ^ m * ‖x N‖ + ε / 2) + (1 - |c|) * (ε / 2) :=
          add_le_add (mul_le_mul_of_nonneg_left ih (abs_nonneg c)) he'.le
        _ = |c| ^ (m + 1) * ‖x N‖ + ε / 2 := by rw [pow_succ]; ring
  have hp : Tendsto (fun m : ℕ => |c| ^ m * ‖x N‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg c) hc).mul_const ‖x N‖
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hp (ε / 2) (half_pos hε)
  refine ⟨N + M, ?_⟩
  intro n hn
  have hNm : N + (n - N) = n := Nat.add_sub_of_le (le_trans (Nat.le_add_right N M) hn)
  have hm : M ≤ n - N := by omega
  have hpow := hM (n - N) hm
  have hb' := hb (n - N)
  rw [hNm] at hb'
  simp only [dist_zero_right, Real.norm_eq_abs] at hpow ⊢
  have hpow' : |c| ^ (n - N) * ‖x N‖ < ε / 2 := (le_abs_self _).trans_lt hpow
  linarith

end GabayADMMProof


open Filter Topology InertialFB.IFB GabayMercier.DualAlgorithm
open scoped RealInnerProductSpace

namespace GabayADMMProof

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {A : V →L[ℝ] Y} {f₁ : Y → ℝ} {f₁' : Y → Y} {f₂ : Y → EReal}
  {b : StrongDual ℝ V} {γ α r ρ : ℝ} {v : ℕ → V} {y lam : ℕ → Y} {vs : V} {ls : Y}

lemma run_projected_step (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (hs : ∀ w, inner ℝ ls (A w) = b w) (n : ℕ) :
    r • (A (v (n + 1)) - A vs) =
      r • proj A (y n - A vs) - proj A (lam n - ls) := by
  have hz : proj A ((lam n - ls) + r • (A (v (n + 1)) - A vs) -
      r • (y n - A vs)) = 0 := by
    apply proj_eq_zero_of_inner_image
    intro w
    have ht := (hrun n).1 w
    have hb := hs w
    simp only [inner_add_left, inner_sub_left, inner_smul_left, RCLike.conj_to_real] at ht ⊢
    linarith
  have hu : proj A (A (v (n + 1)) - A vs) = A (v (n + 1)) - A vs := by
    rw [map_sub, proj_image, proj_image]
  rw [map_sub, map_add, map_smul, map_smul, hu] at hz
  calc
    r • (A (v (n + 1)) - A vs) =
        (proj A (lam n - ls) + r • (A (v (n + 1)) - A vs) - r • proj A (y n - A vs)) +
        (r • proj A (y n - A vs) - proj A (lam n - ls)) := by abel
    _ = _ := by rw [hz, zero_add]

lemma run_variational (h : StandingHyp A f₁ f₁' f₂ γ α)
    (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (hs : IsSubgradient f₂ (A vs) (ls - f₁' (A vs))) (n : ℕ) :
    γ * ‖y (n + 1) - A vs‖ ^ 2 ≤
      inner ℝ ((lam n - ls) + r • (A (v (n + 1)) - A vs) -
        r • (y (n + 1) - A vs)) (y (n + 1) - A vs) := by
  have hm := subgradient_monotone h.f₂_proper (hrun n).2.1 hs
  have he : (lam n + r • A (v (n + 1)) - r • y (n + 1) - f₁' (y (n + 1))) -
      (ls - f₁' (A vs)) =
      ((lam n - ls) + r • (A (v (n + 1)) - A vs) - r • (y (n + 1) - A vs)) -
      (f₁' (y (n + 1)) - f₁' (A vs)) := by module
  rw [he, inner_sub_left] at hm
  exact (h.strongMono (y (n + 1)) (A vs)).trans (by linarith)

end GabayADMMProof


open scoped RealInnerProductSpace

namespace GabayADMMProof

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

lemma quadratic_energy {r ρ γ : ℝ} (hρ : 0 ≤ ρ) (d p q l z : Y)
    (hn : ‖z‖ ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2)
    (hv : γ * ‖z‖ ^ 2 ≤ inner ℝ l q + r * inner ℝ d p - r * ‖z‖ ^ 2) :
    (‖l - ρ • q‖ ^ 2 + ρ * r * ‖p‖ ^ 2) + 2 * ρ * γ * ‖z‖ ^ 2 +
      ρ * r * ‖d - p‖ ^ 2 + ρ * (2 * r - ρ) * ‖q‖ ^ 2 ≤
      ‖l‖ ^ 2 + ρ * r * ‖d‖ ^ 2 := by
  have hh := mul_le_mul_of_nonneg_left hv (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hρ)
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [norm_sub_sq_real]
  rw [hn] at hh ⊢
  nlinarith

lemma energy_summable {E a : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hE : ∀ n, 0 ≤ E n) (ha : ∀ n, 0 ≤ a n)
    (hstep : ∀ n, E (n + 1) + c * a n ≤ E n) :
    Summable a ∧ ∀ n, E n ≤ E 0 := by
  have hsum (N : ℕ) : E N + c * ∑ n ∈ Finset.range N, a n ≤ E 0 := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hs := hstep N
      nlinarith
  constructor
  · apply summable_of_sum_range_le ha (c := E 0 / c)
    intro N
    apply (le_div_iff₀ hc).mpr
    have hs := hsum N
    nlinarith [hE N]
  · intro N
    have hs := hsum N
    have ha' : 0 ≤ ∑ n ∈ Finset.range N, a n := Finset.sum_nonneg fun n _ => ha n
    nlinarith

end GabayADMMProof


open Filter Topology InertialFB.IFB GabayMercier.DualAlgorithm
open scoped RealInnerProductSpace

namespace GabayADMMProof

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {A : V →L[ℝ] Y} {f₁ : Y → ℝ} {f₁' : Y → Y} {f₂ : Y → EReal}
  {b : StrongDual ℝ V} {γ α r ρ : ℝ} {v : ℕ → V} {y lam : ℕ → Y} {vs : V} {ls : Y}

noncomputable def runEnergy (A : V →L[ℝ] Y) (r ρ : ℝ) (ys ls : Y)
    (y lam : ℕ → Y) (n : ℕ) : ℝ :=
  ‖compProj A (lam n - ls)‖ ^ 2 + ρ * r * ‖proj A (y n - ys)‖ ^ 2

lemma run_primal_error (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (hs : ∀ w, inner ℝ ls (A w) = b w) (hr : r ≠ 0) (n : ℕ) :
    A (v (n + 1)) - A vs = proj A (y n - A vs) - r⁻¹ • proj A (lam n - ls) := by
  have he := congrArg (fun z : Y => r⁻¹ • z) (run_projected_step hrun hs n (vs := vs))
  simpa only [smul_sub, inv_smul_smul₀ hr] using he

lemma run_comp_update (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam) (n : ℕ) :
    compProj A (lam (n + 1) - ls) =
      compProj A (lam n - ls) - ρ • compProj A (y (n + 1) - A vs) := by
  rw [(hrun n).2.2]
  simp only [map_sub, map_add, map_smul, comp_image]
  module

lemma run_proj_update (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (hs : ∀ w, inner ℝ ls (A w) = b w) (hr : r ≠ 0) (n : ℕ) :
    proj A (lam (n + 1) - ls) = (1 - ρ / r) • proj A (lam n - ls) +
      ρ • proj A ((y n - A vs) - (y (n + 1) - A vs)) := by
  have hu := run_primal_error hrun hs hr n (vs := vs)
  have hAv : A (v (n + 1)) = A vs + (proj A (y n - A vs) - r⁻¹ • proj A (lam n - ls)) := by
    rw [← hu]; abel
  rw [(hrun n).2.2]
  simp only [map_sub, map_add, map_smul, proj_image]
  rw [hAv]
  simp only [map_sub, proj_image]
  simp only [div_eq_mul_inv]
  module

lemma run_energy_step (h : StandingHyp A f₁ f₁' f₂ γ α)
    (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (hs : ∀ w, inner ℝ ls (A w) = b w)
    (hsg : IsSubgradient f₂ (A vs) (ls - f₁' (A vs)))
    (hr : 0 < r) (hρ : 0 < ρ) (hρr : ρ < 2 * r) (n : ℕ) :
    runEnergy A r ρ (A vs) ls y lam (n + 1) +
      (2 * ρ * γ) * ‖y (n + 1) - A vs‖ ^ 2 ≤ runEnergy A r ρ (A vs) ls y lam n := by
  have hv := run_variational h hrun hsg n
  have hp := run_projected_step hrun hs n (vs := vs)
  have he : (lam n - ls) + r • (A (v (n + 1)) - A vs) - r • (y (n + 1) - A vs) =
      compProj A (lam n - ls) + r • proj A (y n - A vs) - r • (y (n + 1) - A vs) := by
    rw [hp]
    have hh := proj_add_comp A (lam n - ls)
    nth_rw 1 [← hh]
    abel
  rw [he, inner_sub_left, inner_add_left, inner_smul_left, inner_smul_left,
    inner_comp_right, inner_proj_right, real_inner_self_eq_norm_sq, RCLike.conj_to_real] at hv
  have hh := quadratic_energy hρ.le (proj A (y n - A vs)) (proj A (y (n + 1) - A vs))
    (compProj A (y (n + 1) - A vs)) (compProj A (lam n - ls)) (y (n + 1) - A vs)
    (norm_decomposition A _) hv
  unfold runEnergy
  rw [run_comp_update hrun n (vs := vs)]
  have h1 : 0 ≤ ρ * r * ‖proj A (y n - A vs) - proj A (y (n + 1) - A vs)‖ ^ 2 := by positivity
  have h2 : 0 ≤ ρ * (2 * r - ρ) * ‖compProj A (y (n + 1) - A vs)‖ ^ 2 := by positivity
  linarith

end GabayADMMProof


open Filter Topology InertialFB.IFB GabayMercier.DualAlgorithm

namespace GabayADMMProof

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {A : V →L[ℝ] Y} {f₁ : Y → ℝ} {f₁' : Y → Y} {f₂ : Y → EReal}
  {b : StrongDual ℝ V} {γ α r ρ : ℝ} {v : ℕ → V} {y lam : ℕ → Y} {vs : V} {ls : Y}

lemma run_y_converges (h : StandingHyp A f₁ f₁' f₂ γ α)
    (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (hs : ∀ w, inner ℝ ls (A w) = b w)
    (hsg : IsSubgradient f₂ (A vs) (ls - f₁' (A vs)))
    (hr : 0 < r) (hρ : 0 < ρ) (hρr : ρ < 2 * r) :
    Tendsto y atTop (𝓝 (A vs)) ∧
      ∀ n, runEnergy A r ρ (A vs) ls y lam n ≤ runEnergy A r ρ (A vs) ls y lam 0 := by
  have hn (n : ℕ) : 0 ≤ runEnergy A r ρ (A vs) ls y lam n := by
    unfold runEnergy; positivity
  obtain ⟨hsum, hbound⟩ := energy_summable (mul_pos (mul_pos (by norm_num) hρ) h.γ_pos)
    hn (fun n => sq_nonneg ‖y (n + 1) - A vs‖)
    (run_energy_step h hrun hs hsg hr hρ hρr)
  refine ⟨?_, hbound⟩
  have ht := hsum.tendsto_atTop_zero
  have ht' : Tendsto (fun n => ‖y (n + 1) - A vs‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht.sqrt
  apply (tendsto_add_atTop_iff_nat 1).mp
  exact tendsto_iff_norm_sub_tendsto_zero.mpr ht'

lemma run_projected_multiplier_converges (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (hs : ∀ w, inner ℝ ls (A w) = b w)
    (hr : 0 < r) (hρ : 0 < ρ) (hρr : ρ < 2 * r)
    (hy : Tendsto y atTop (𝓝 (A vs))) :
    Tendsto (fun n => proj A (lam n - ls)) atTop (𝓝 0) := by
  have hc : |1 - ρ / r| < 1 := by
    rw [abs_lt]
    constructor
    · have hh : ρ / r < 2 := (div_lt_iff₀ hr).mpr (by linarith)
      linarith
    · have hh : 0 < ρ / r := div_pos hρ hr
      linarith
  have hy' : Tendsto (fun n => y (n + 1)) atTop (𝓝 (A vs)) :=
    (tendsto_add_atTop_iff_nat 1).mpr hy
  have he : Tendsto (fun n => ρ • proj A ((y n - A vs) - (y (n + 1) - A vs)))
      atTop (𝓝 0) := by
    have hz : Tendsto (fun n => (y n - A vs) - (y (n + 1) - A vs)) atTop (𝓝 0) := by
      simpa using (hy.sub_const (A vs)).sub (hy'.sub_const (A vs))
    have hh := (proj A).continuous.tendsto 0 |>.comp hz
    simpa using hh.const_smul ρ
  exact stable_recurrence hc he (run_proj_update hrun hs hr.ne')

lemma run_v_converges (h : StandingHyp A f₁ f₁' f₂ γ α)
    (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (hs : ∀ w, inner ℝ ls (A w) = b w) (hr : 0 < r)
    (hy : Tendsto y atTop (𝓝 (A vs)))
    (hl : Tendsto (fun n => proj A (lam n - ls)) atTop (𝓝 0)) :
    Tendsto v atTop (𝓝 vs) := by
  have hAv : Tendsto (fun n => A (v (n + 1)) - A vs) atTop (𝓝 0) := by
    have hz : Tendsto (fun n => y n - A vs) atTop (𝓝 0) := by simpa using hy.sub_const (A vs)
    have hh := ((proj A).continuous.tendsto 0 |>.comp hz).sub (hl.const_smul r⁻¹)
    simpa only [Function.comp_def, sub_self, map_zero, smul_zero, sub_zero, ← run_primal_error hrun hs hr.ne'] using hh
  have hn := hAv.norm
  have hn' : Tendsto (fun n => ‖v (n + 1) - vs‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => ?_) (by simpa using hn.div_const α)
    apply (le_div_iff₀ h.α_pos).mpr
    have hh := h.bddBelow (v (n + 1) - vs)
    rw [map_sub] at hh
    nlinarith [norm_nonneg (v (n + 1) - vs), norm_nonneg (A (v (n + 1)) - A vs)]
  apply (tendsto_add_atTop_iff_nat 1).mp
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn'

lemma run_multiplier_bounded (hr : 0 < r) (hρ : 0 < ρ)
    (hl : Tendsto (fun n => proj A (lam n - ls)) atTop (𝓝 0))
    (hb : ∀ n, runEnergy A r ρ (A vs) ls y lam n ≤ runEnergy A r ρ (A vs) ls y lam 0) :
    Bornology.IsBounded (Set.range lam) := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hl).exists_norm_le
  let E := runEnergy A r ρ (A vs) ls y lam 0
  have hE : 0 ≤ E := by dsimp [E, runEnergy]; positivity
  have hq (n : ℕ) : ‖compProj A (lam n - ls)‖ ≤ E + 1 := by
    have he := hb n
    have ht : 0 ≤ ρ * r * ‖proj A (y n - A vs)‖ ^ 2 := by positivity
    change ‖compProj A (lam n - ls)‖ ^ 2 + _ ≤ E at he
    nlinarith [sq_nonneg (‖compProj A (lam n - ls)‖ - 1)]
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨‖ls‖ + C + (E + 1), ?_⟩
  rintro _ ⟨n, rfl⟩
  have he : lam n = ls + (proj A (lam n - ls) + compProj A (lam n - ls)) := by
    rw [proj_add_comp]; abel
  rw [he]
  calc
    ‖ls + (proj A (lam n - ls) + compProj A (lam n - ls))‖ ≤
        ‖ls‖ + (‖proj A (lam n - ls)‖ + ‖compProj A (lam n - ls)‖) :=
      (norm_add_le _ _).trans (add_le_add (le_refl _) (norm_add_le _ _))
    _ ≤ ‖ls‖ + C + (E + 1) := by linarith [hC _ ⟨n, rfl⟩, hq n]

end GabayADMMProof


open Filter Topology InertialFB.IFB GabayMercier.DualAlgorithm

namespace GabayADMMProof

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- Theorem 3.1, p. 19: for every stepsize `0 < ρ < 2r`, every run of the modified dual algorithm
(3.4) converges strongly in `V × Y` to `(v*, Av*)`, where `v*` is the solution of (𝒫), and the
multipliers `λⁿ` stay bounded. The qualification hypothesis strengthens the paper's (2.4). -/
theorem full_admm_convergence [CompleteSpace V] (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (γ α : ℝ) (h : StandingHyp A f₁ f₁' f₂ γ α)
    (hq : Qualification A f₂) (r ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) (hρr : ρ < 2 * r)
    (v : ℕ → V) (y lam : ℕ → Y) (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (vs : V) (hvs : IsSolution A f₁ f₂ b vs) :
    Tendsto v atTop (𝓝 vs) ∧ Tendsto y atTop (𝓝 (A vs)) ∧
      Bornology.IsBounded (Set.range lam) := by
  obtain ⟨ls, hs, hsg⟩ := exists_multiplier h hq hvs
  obtain ⟨hy, hb⟩ := run_y_converges h hrun hs hsg hr hρ hρr
  have hl := run_projected_multiplier_converges hrun hs hr hρ hρr hy
  exact ⟨run_v_converges h hrun hs hr hy hl, hy, run_multiplier_bounded hr hρ hl hb⟩

end GabayADMMProof


open Filter Topology InertialFB.IFB

namespace GabayMercier.DualAlgorithm

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- Theorem 3.1, p. 19: for every stepsize `0 < ρ < 2r`, every run of the modified dual algorithm
(3.4) converges strongly in `V × Y` to `(v*, Av*)`, where `v*` is the solution of (𝒫), and the
multipliers `λⁿ` stay bounded. The qualification hypothesis strengthens the paper's (2.4). -/
theorem theorem_3_1 (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (γ α : ℝ) (h : StandingHyp A f₁ f₁' f₂ γ α)
    (hq : Qualification A f₂) (r ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) (hρr : ρ < 2 * r)
    (v : ℕ → V) (y lam : ℕ → Y) (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (vs : V) (hvs : IsSolution A f₁ f₂ b vs) :
    Tendsto v atTop (𝓝 vs) ∧ Tendsto y atTop (𝓝 (A vs)) ∧
      Bornology.IsBounded (Set.range lam) := by
  exact GabayADMMProof.full_admm_convergence A f₁ f₁' f₂ b γ α h hq r ρ hr hρ hρr v y lam hrun vs hvs

end GabayMercier.DualAlgorithm

open GabayMercier.DualAlgorithm

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]


theorem solution (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (γ α : ℝ) (h : StandingHyp A f₁ f₁' f₂ γ α)
    (hq : Qualification A f₂) (r ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) (hρr : ρ < 2 * r)
    (v : ℕ → V) (y lam : ℕ → Y) (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (vs : V) (hvs : IsSolution A f₁ f₂ b vs) :
    Tendsto v atTop (𝓝 vs) ∧ Tendsto y atTop (𝓝 (A vs)) ∧
      Bornology.IsBounded (Set.range lam) := GabayMercier.DualAlgorithm.theorem_3_1 A f₁ f₁' f₂ b γ α h hq r ρ hr hρ hρr v y lam hrun vs hvs
