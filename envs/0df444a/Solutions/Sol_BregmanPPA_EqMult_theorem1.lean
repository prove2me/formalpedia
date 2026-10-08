-- Prove2me | solution 1 for BregmanPPA.EqMult.theorem1
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T18:04:09.677218+00:00
-- url     : https://prove2.me/submissions/0b3494a9-a662-4aa7-bb38-45a5f2330da8

import Definitions.Def_BregmanPPA_Convergence_Model
import Mathlib
set_option autoImplicit false
section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- First-order support at a point in the original open zone, including boundary test points. -/
theorem gradient_support (S : Set H) (h : H → ℝ) (hh : IsBregmanFunction S h)
    {y z : H} (hy : y ∈ S) (hz : z ∈ closure S) :
    inner ℝ (gradient h y) (z-y) ≤ h z-h y := by
  have hd : DifferentiableAt ℝ h y :=
    ((hh.contDiffOn.differentiableOn (by simp)) y hy).differentiableAt (hh.isOpen.mem_nhds hy)
  let l : ℝ →ᵃ[ℝ] H := AffineMap.lineMap y z
  have hcv := hh.strictConvexOn.convexOn.comp_affineMap l
  have h0 : (0 : ℝ) ∈ l ⁻¹' closure S := by simpa [l] using subset_closure hy
  have h1 : (1 : ℝ) ∈ l ⁻¹' closure S := by simpa [l] using hz
  have hder : HasDerivAt (h ∘ l) (fderiv ℝ h y (z-y)) 0 := by
    apply hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      (AffineMap.hasDerivAt_lineMap (a := y) (b := z) (x := (0 : ℝ)))
    simp [l]
  have hs := hcv.le_slope_of_hasDerivAt h0 h1 (by norm_num) hder
  simpa [l,slope,inner_gradient_left] using hs

theorem bregman_nonneg (S : Set H) (h : H → ℝ) (hh : IsBregmanFunction S h)
    {x y : H} (hx : x ∈ closure S) (hy : y ∈ S) : 0 ≤ bregmanD h x y := by
  have hs := gradient_support S h hh hy hx
  dsimp [bregmanD]; linarith
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem three_point_identity (h : H → ℝ) (v y p : H) :
    bregmanD h v y-bregmanD h v p-bregmanD h p y =
      inner ℝ (p-v) (gradient h y-gradient h p) := by
  have he : v-y = (v-p)+(p-y) := by abel
  have hi : inner ℝ (gradient h y) (v-y) =
      inner ℝ (gradient h y) (v-p)+inner ℝ (gradient h y) (p-y) := by
    rw [he,inner_add_right]
  have hc1 : inner ℝ (p-v) (gradient h y) = inner ℝ (gradient h y) (p-v) :=
    real_inner_comm _ _
  have hc2 : inner ℝ (p-v) (gradient h p) = inner ℝ (gradient h p) (p-v) :=
    real_inner_comm _ _
  rw [inner_sub_right,hc1,hc2,← neg_sub v p,inner_neg_right,inner_neg_right]
  dsimp [bregmanD]
  linarith

theorem weighted_graph_comparison (T : H → Set H) (h : H → ℝ) (hT : IsMonotoneOp T)
    (v w y p : H) (c : ℝ) (hc : 0 < c) (hw : w ∈ T v)
    (hp : c⁻¹ • (gradient h y-gradient h p) ∈ T p) :
    c*inner ℝ w (p-v) ≤ bregmanD h v y-bregmanD h v p-bregmanD h p y := by
  have hm := hT p v _ w hp hw
  rw [inner_sub_right,inner_smul_right] at hm
  change 0 ≤ c⁻¹*inner ℝ (p-v) (gradient h y-gradient h p)-inner ℝ (p-v) w at hm
  have hm' : inner ℝ (p-v) w ≤ c⁻¹*inner ℝ (p-v) (gradient h y-gradient h p) := by linarith
  have ht := mul_le_mul_of_nonneg_left hm' hc.le
  simp only [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul] at ht
  rw [three_point_identity]
  have he : inner ℝ (p-v) w = inner ℝ w (p-v) := real_inner_comm _ _
  rwa [he] at ht

theorem weighted_descent (T : H → Set H) (h : H → ℝ) (hT : IsMonotoneOp T)
    (z y p : H) (c : ℝ) (hc : 0 < c) (hz : z ∈ zer T)
    (hp : c⁻¹ • (gradient h y-gradient h p) ∈ T p) :
    bregmanD h z p ≤ bregmanD h z y-bregmanD h p y := by
  have ht := weighted_graph_comparison T h hT z 0 y p c hc hz hp
  simp only [inner_zero_left,mul_zero] at ht
  linarith
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem zero_mem_closure (T : H → Set H) (S : Set H) (hdom : dom T ⊆ closure S)
    {z : H} (hz : z ∈ zer T) : z ∈ closure S := hdom ⟨0,hz⟩

theorem run_descent (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMonotoneOp T) (hc : ∀ k, 0 < c k) (hx : IsBregmanPPARun S h T c x)
    (z : H) (hz : z ∈ zer T) (k : ℕ) :
    bregmanD h z (x (k+1)) ≤ bregmanD h z (x k)-bregmanD h (x (k+1)) (x k) :=
  weighted_descent T h hT z (x k) (x (k+1)) (c k) (hc k) hz (hx k).2

theorem distance_antitone (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMonotoneOp T) (hh : IsBregmanFunction S h)
    (hc : ∀ k, 0 < c k) (hx : IsBregmanPPARun S h T c x) (z : H) (hz : z ∈ zer T) :
    Antitone (fun k => bregmanD h z (x k)) := by
  apply antitone_nat_of_succ_le
  intro k
  have hd := run_descent T S h c x hT hc hx z hz k
  have hn := bregman_nonneg S h hh (subset_closure (hx (k+1)).1) (hx k).1
  linarith

theorem step1 (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hx : IsBregmanPPARun S h T c x) (z : H) (hz : z ∈ zer T) :
    (∀ k, bregmanD h z (x (k+1)) ≤ bregmanD h z (x k)-bregmanD h (x (k+1)) (x k)) ∧
    (∃ δ : ℝ, 0 ≤ δ ∧ Tendsto (fun k => bregmanD h z (x k)) atTop (𝓝 δ)) ∧
    Bornology.IsBounded (Set.range x) := by
  have hzc := zero_mem_closure T S hdom hz
  have hnonneg (k : ℕ) : 0 ≤ bregmanD h z (x k) := bregman_nonneg S h hh hzc (hx k).1
  have hanti := distance_antitone T S h c x hT.1 hh hc hx z hz
  have hbelow : BddBelow (Set.range (fun k => bregmanD h z (x k))) := by
    refine ⟨0, ?_⟩; rintro _ ⟨k,rfl⟩; exact hnonneg k
  have ht := tendsto_atTop_ciInf hanti hbelow
  have hδ : 0 ≤ ⨅ k, bregmanD h z (x k) :=
    (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ))).mem_of_tendsto ht
      (Eventually.of_forall hnonneg)
  refine ⟨run_descent T S h c x hT.1 hc hx z hz,⟨_,hδ,ht⟩, ?_⟩
  apply (hh.bounded_L₂ (bregmanD h z (x 0)) z hzc).subset
  rintro _ ⟨k,rfl⟩
  exact ⟨(hx k).1,hanti (Nat.zero_le k)⟩
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology Finset
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem step_distance_sum (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMonotoneOp T) (hc : ∀ k, 0 < c k) (hx : IsBregmanPPARun S h T c x)
    (z : H) (hz : z ∈ zer T) (N : ℕ) :
    (∑ k ∈ range N, bregmanD h (x (k+1)) (x k))+bregmanD h z (x N) ≤ bregmanD h z (x 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have hd := run_descent T S h c x hT hc hx z hz N
    linarith

theorem step_distance_zero (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMonotoneOp T) (hh : IsBregmanFunction S h) (hdom : dom T ⊆ closure S)
    (hc : ∀ k, 0 < c k) (hx : IsBregmanPPARun S h T c x) (z : H) (hz : z ∈ zer T) :
    Tendsto (fun k => bregmanD h (x (k+1)) (x k)) atTop (𝓝 0) := by
  have hzc := zero_mem_closure T S hdom hz
  have hs : Summable (fun k => bregmanD h (x (k+1)) (x k)) := by
    apply summable_of_sum_range_le
      (fun k => bregman_nonneg S h hh (subset_closure (hx (k+1)).1) (hx k).1)
      (c := bregmanD h z (x 0))
    intro N
    have hsum := step_distance_sum T S h c x hT hc hx z hz N
    have hn := bregman_nonneg S h hh hzc (hx N).1
    linarith
  exact hs.tendsto_atTop_zero

theorem successor_subsequence_limit (T : H → Set H) (S : Set H) (h : H → ℝ)
    (c : ℕ → ℝ) (x : ℕ → H) (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k) (hx : IsBregmanPPARun S h T c x)
    (hz : (zer T).Nonempty) (φ : ℕ → ℕ) (hφ : StrictMono φ) (p : H)
    (hlim : Tendsto (x ∘ φ) atTop (𝓝 p)) :
    Tendsto (fun k => x (φ k+1)) atTop (𝓝 p) := by
  obtain ⟨z,hz⟩ := hz
  have hb := (step1 T S h c x hT hh hdom hc hcinf hx z hz).2.2
  have hfirst : Bornology.IsBounded (Set.range (fun k => x (φ k+1))) := hb.subset (by
    rintro _ ⟨k,rfl⟩; exact ⟨φ k+1,rfl⟩)
  have hpc : p ∈ closure S := isClosed_closure.mem_of_tendsto hlim
    (Eventually.of_forall (fun k => subset_closure (hx (φ k)).1))
  have hD : Tendsto (fun k => bregmanD h (x (φ k+1)) ((x ∘ φ) k)) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (step_distance_zero T S h c x hT.1 hh hdom hc hx z hz).comp hφ.tendsto_atTop
  exact hh.tendsto_of_zero (fun k => x (φ k+1)) (x ∘ φ) p
    (fun k => subset_closure (hx (φ k+1)).1) (fun k => (hx (φ k)).1)
    hlim hpc hfirst hD
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open ThreeOpSplitting.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Adjoining a related point to the exact original graph cannot extend a maximal operator. -/
theorem maximal_related_point (T : H → Set H) (hT : IsMaximalMonotone T) (z u : H)
    (hrel : ∀ v w : H, w ∈ T v → 0 ≤ inner ℝ (z-v) (u-w)) : u ∈ T z := by
  let U : H → Set H := fun x => T x ∪ {v | x=z ∧ v=u}
  have hU : IsMonotoneOp U := by
    intro x y v w hv hw
    rcases hv with hv | ⟨hx,hv⟩
    · rcases hw with hw | ⟨hy,hw⟩
      · exact hT.1 x y v w hv hw
      · rw [hy,hw]
        have he : inner ℝ (x-z) (v-u) = inner ℝ (z-x) (u-v) := by
          rw [← neg_sub z x,← neg_sub u v,inner_neg_left,inner_neg_right,neg_neg]
        rw [he]; exact hrel x v hv
    · rcases hw with hw | ⟨hy,hw⟩
      · rw [hx,hv]; exact hrel y w hw
      · rw [hx,hv,hy,hw]; simp
  have hEq : U=T := hT.2 U hU (fun x => Set.subset_union_left)
  have hu : u ∈ U z := Or.inr ⟨rfl,rfl⟩
  rwa [hEq] at hu

/-- Norm limits of graph points remain in the exact original maximal monotone graph. -/
theorem maximal_graph_limit (T : H → Set H) (hT : IsMaximalMonotone T)
    (x u : ℕ → H) (z v : H) (hx : Tendsto x atTop (𝓝 z)) (hu : Tendsto u atTop (𝓝 v))
    (hmem : ∀ k, u k ∈ T (x k)) : v ∈ T z := by
  apply maximal_related_point T hT z v
  intro y w hw
  have ht : Tendsto (fun k => inner ℝ (x k-y) (u k-w)) atTop (𝓝 (inner ℝ (z-y) (v-w))) :=
    (hx.sub_const y).inner (hu.sub_const w)
  exact (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ))).mem_of_tendsto ht
    (Eventually.of_forall (fun k => hT.1 (x k) y (u k) w (hmem k) hw))
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem gradient_continuous_in_zone (S : Set H) (h : H → ℝ) (hh : IsBregmanFunction S h)
    {p : H} (hp : p ∈ S) : ContinuousAt (gradient h) p := by
  have hf := (hh.contDiffOn.contDiffAt (hh.isOpen.mem_nhds hp)).continuousAt_fderiv (by simp)
  change ContinuousAt (fun y => (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ h y)) p
  simpa only [Function.comp_def] using
    (InnerProductSpace.toDual ℝ H).symm.continuous.continuousAt.comp hf

theorem bounded_inverse_residual (a : ℕ → H) (c : ℕ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hc : ∀ k, 0 < c k) (hle : ∀ k, ε ≤ c k)
    (ha : Tendsto a atTop (𝓝 0)) : Tendsto (fun k => (c k)⁻¹ • a k) atTop (𝓝 0) := by
  have hbound (k : ℕ) : ‖(c k)⁻¹ • a k‖ ≤ ‖a k‖/ε := by
    rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr (hc k)).le]
    simpa only [div_eq_mul_inv,mul_comm] using
      div_le_div_of_nonneg_left (norm_nonneg (a k)) hε (hle k)
  have ht : Tendsto (fun k => ‖a k‖/ε) atTop (𝓝 0) := by simpa using ha.norm.div_const ε
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun k => norm_nonneg _) hbound ht)

theorem interior_cluster_zero (T : H → Set H) (S : Set H) (h : H → ℝ)
    (c : ℕ → ℝ) (x : ℕ → H) (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k) (hx : IsBregmanPPARun S h T c x)
    (hz : (zer T).Nonempty) (hC1 : closure (dom T) ⊆ S)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (p : H) (hlim : Tendsto (x ∘ φ) atTop (𝓝 p)) :
    p ∈ zer T := by
  have hnext := successor_subsequence_limit T S h c x hT hh hdom hc hcinf hx hz φ hφ p hlim
  have hpdom : p ∈ closure (dom T) := isClosed_closure.mem_of_tendsto hnext
    (Eventually.of_forall (fun k => subset_closure ⟨_,(hx (φ k)).2⟩))
  have hgrad := (gradient_continuous_in_zone S h hh (hC1 hpdom)).tendsto
  have hdiff : Tendsto (fun k => gradient h (x (φ k))-gradient h (x (φ k+1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,sub_self] using (hgrad.comp hlim).sub (hgrad.comp hnext)
  obtain ⟨ε,hε,hle⟩ := hcinf
  have hres := bounded_inverse_residual _ (c ∘ φ) ε hε (fun k => hc (φ k))
    (fun k => hle (φ k)) hdiff
  exact maximal_graph_limit T hT (fun k => x (φ k+1))
    (fun k => (c (φ k))⁻¹ • (gradient h (x (φ k))-gradient h (x (φ k+1)))) p 0
    hnext hres (fun k => (hx (φ k)).2)
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open InertialFB.IFB
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Transport the original extended-real subgradient inequality only at verified finite points. -/
theorem subgradient_real_comparison (f : H → EReal) (hproper : IsProperFn f)
    {u v g : H} (hu : IsSubgradient f u g) (hv : f v ≠ ⊤) :
    (f u).toReal+inner ℝ g (v-u) ≤ (f v).toReal := by
  have heu := EReal.coe_toReal hu.1 (hproper.1 u)
  have hev := EReal.coe_toReal hv (hproper.1 v)
  have hg := hu.2 v
  rw [← heu,← hev,← EReal.coe_add] at hg
  exact EReal.coe_le_coe_iff.mp hg

theorem zero_subgradient_real_min (f : H → EReal) (hproper : IsProperFn f)
    {z v : H} (hz : IsSubgradient f z 0) (hv : f v ≠ ⊤) :
    (f z).toReal ≤ (f v).toReal := by
  simpa using subgradient_real_comparison f hproper hz hv

theorem zero_subgradient_of_min (f : H → EReal) {p : H} (hp : f p ≠ ⊤)
    (hmin : ∀ v : H, f p ≤ f v) : IsSubgradient f p 0 := by
  exact ⟨hp,fun v => by simpa using hmin v⟩

/-- Lower semicontinuity passes a verified objective-value limit to a boundary point. -/
theorem lsc_objective_limit (f : H → EReal) (hf : LowerSemicontinuous f)
    (x : ℕ → H) (p : H) (m : EReal) (hx : Tendsto x atTop (𝓝 p))
    (hm : Tendsto (fun k => f (x k)) atTop (𝓝 m)) : f p ≤ m := by
  by_contra hn
  have hmp : m < f p := lt_of_not_ge hn
  obtain ⟨a,hma,hap⟩ := exists_between hmp
  have hl : ∀ᶠ k in atTop, a < f (x k) := hx.eventually (hf p a hap)
  have hu : ∀ᶠ k in atTop, f (x k) < a := hm.eventually (Iio_mem_nhds hma)
  obtain ⟨k,hk⟩ := (hl.and hu).exists
  exact lt_asymm hk.1 hk.2
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence InertialFB.IFB
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem bregman_self (h : H → ℝ) (y : H) : bregmanD h y y = 0 := by simp [bregmanD]

theorem symmetrized_bregman (h : H → ℝ) (y p : H) :
    inner ℝ (gradient h y-gradient h p) (y-p) = bregmanD h y p+bregmanD h p y := by
  have hid := three_point_identity h y y p
  simp only [bregman_self] at hid
  have he : inner ℝ (p-y) (gradient h y-gradient h p) =
      -inner ℝ (gradient h y-gradient h p) (y-p) := by
    rw [← neg_sub y p,inner_neg_left]
    have hc : inner ℝ (y-p) (gradient h y-gradient h p) =
        inner ℝ (gradient h y-gradient h p) (y-p) := real_inner_comm _ _
    rw [hc]
  rw [he] at hid
  linarith

theorem subgradient_step_decrease (S : Set H) (h : H → ℝ) (hh : IsBregmanFunction S h)
    (f : H → EReal) (hproper : IsProperFn f) (y p : H) (c : ℝ) (hc : 0 < c)
    (hy : y ∈ S) (hp : p ∈ S) (hfy : f y ≠ ⊤)
    (hsub : IsSubgradient f p (c⁻¹ • (gradient h y-gradient h p))) :
    (f p).toReal ≤ (f y).toReal := by
  have hg := subgradient_real_comparison f hproper hsub hfy
  rw [real_inner_smul_left,symmetrized_bregman] at hg
  have hD1 := bregman_nonneg S h hh (subset_closure hy) hp
  have hD2 := bregman_nonneg S h hh (subset_closure hp) hy
  have hn := mul_nonneg (inv_pos.mpr hc).le (add_nonneg hD1 hD2)
  linarith

theorem subgradient_step_gap (S : Set H) (h : H → ℝ) (hh : IsBregmanFunction S h)
    (f : H → EReal) (hproper : IsProperFn f) (z y p : H) (c : ℝ) (hc : 0 < c)
    (hy : y ∈ S) (hp : p ∈ S) (hfz : f z ≠ ⊤)
    (hsub : IsSubgradient f p (c⁻¹ • (gradient h y-gradient h p))) :
    c*((f p).toReal-(f z).toReal) ≤ bregmanD h z y-bregmanD h z p := by
  have hg := subgradient_real_comparison f hproper hsub hfz
  rw [real_inner_smul_left] at hg
  have he : inner ℝ (gradient h y-gradient h p) (z-p) =
      -inner ℝ (p-z) (gradient h y-gradient h p) := by
    rw [← neg_sub p z,inner_neg_right]
    have he' : inner ℝ (gradient h y-gradient h p) (p-z) =
        inner ℝ (p-z) (gradient h y-gradient h p) := real_inner_comm _ _
    rw [he']
  rw [he] at hg
  have hg' : (f p).toReal-(f z).toReal ≤ c⁻¹*inner ℝ (p-z) (gradient h y-gradient h p) := by
    linarith
  have ht := mul_le_mul_of_nonneg_left hg' hc.le
  simp only [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul] at ht
  rw [← three_point_identity h z y p] at ht
  have hn := bregman_nonneg S h hh (subset_closure hp) hy
  linarith
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology Finset
namespace BregmanPPACodex

/-- Real gap telescoping follows the checked objective-rate pattern from the preceding Martinet lane. -/
theorem real_gap_sum_bound (v d : ℕ → ℝ) (m ε : ℝ)
    (hstep : ∀ k, ε*(v (k+1)-m) ≤ d k-d (k+1)) (N : ℕ) :
    (∑ k ∈ range N, ε*(v (k+1)-m))+d N ≤ d 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have hs := hstep N
    linarith

theorem real_gap_rate (v d : ℕ → ℝ) (m ε : ℝ) (hε : 0 < ε)
    (hanti : Antitone v) (hd : ∀ k, 0 ≤ d k)
    (hstep : ∀ k, ε*(v (k+1)-m) ≤ d k-d (k+1)) (N : ℕ) (hN : 0 < N) :
    v N-m ≤ (d 0/ε)/(N : ℝ) := by
  have hsum := real_gap_sum_bound v d m ε hstep N
  have hlower : (N : ℝ)*ε*(v N-m) ≤ ∑ k ∈ range N, ε*(v (k+1)-m) := by
    calc
      _ = ∑ k ∈ range N, ε*(v N-m) := by simp <;> ring
      _ ≤ _ := sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left
        (sub_le_sub_right (hanti (by have := mem_range.mp hk; omega)) m) hε.le)
  apply (le_div_iff₀ (by exact_mod_cast hN : 0 < (N : ℝ))).mpr
  apply (le_div_iff₀ hε).mpr
  nlinarith [hd N]

theorem real_gap_tendsto (v d : ℕ → ℝ) (m ε : ℝ) (hε : 0 < ε)
    (hanti : Antitone v) (hlower : ∀ k, m ≤ v k) (hd : ∀ k, 0 ≤ d k)
    (hstep : ∀ k, ε*(v (k+1)-m) ≤ d k-d (k+1)) : Tendsto v atTop (𝓝 m) := by
  have ht : Tendsto (fun N : ℕ => m+(d 0/ε)/(N : ℝ)) atTop (𝓝 m) := by
    have hm : Tendsto (fun _ : ℕ => m) atTop (𝓝 m) := tendsto_const_nhds
    simpa using hm.add (tendsto_const_div_atTop_nhds_zero_nat (d 0/ε))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Eventually.of_forall hlower
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hrate := real_gap_rate v d m ε hε hanti hd hstep N (by omega)
    linarith
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence InertialFB.IFB
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Objective convergence begins at x1, allowing the original x0 objective to be infinite. -/
theorem subgradient_objective_limit (T : H → Set H) (S : Set H) (h : H → ℝ)
    (c : ℕ → ℝ) (x : ℕ → H) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k) (hx : IsBregmanPPARun S h T c x)
    (f : H → EReal) (hproper : IsProperFn f) (hTeq : T = subdiffOp f)
    (z : H) (hz : z ∈ zer T) : Tendsto (fun k => f (x k)) atTop (𝓝 (f z)) := by
  have hsub (k : ℕ) : IsSubgradient f (x (k+1))
      ((c k)⁻¹ • (gradient h (x k)-gradient h (x (k+1)))) := by
    have hu := (hx k).2
    rw [hTeq] at hu
    exact hu
  have hzero : IsSubgradient f z 0 := by
    simpa only [hTeq,zer,subdiffOp,Set.mem_ofPred_eq] using hz
  let v : ℕ → ℝ := fun k => (f (x (k+1))).toReal
  let d : ℕ → ℝ := fun k => bregmanD h z (x (k+1))
  let m : ℝ := (f z).toReal
  obtain ⟨ε,hε,hle⟩ := hcinf
  have hlower (k : ℕ) : m ≤ v k :=
    zero_subgradient_real_min f hproper hzero (hsub k).1
  have hanti : Antitone v := by
    apply antitone_nat_of_succ_le
    intro k
    exact subgradient_step_decrease S h hh f hproper (x (k+1)) (x ((k+1)+1))
      (c (k+1)) (hc (k+1)) (hx (k+1)).1 (hx ((k+1)+1)).1 (hsub k).1 (hsub (k+1))
  have hd (k : ℕ) : 0 ≤ d k :=
    bregman_nonneg S h hh (zero_mem_closure T S hdom hz) (hx (k+1)).1
  have hstep (k : ℕ) : ε*(v (k+1)-m) ≤ d k-d (k+1) := by
    have hgap := subgradient_step_gap S h hh f hproper z (x (k+1)) (x ((k+1)+1))
      (c (k+1)) (hc (k+1)) (hx (k+1)).1 (hx ((k+1)+1)).1 hzero.1 (hsub (k+1))
    have hmul := mul_le_mul_of_nonneg_right (hle (k+1)) (sub_nonneg.mpr (hlower (k+1)))
    exact hmul.trans hgap
  have hreal := real_gap_tendsto v d m ε hε hanti hlower hd hstep
  have hE := (continuous_coe_real_ereal.tendsto m).comp hreal
  have hF (k : ℕ) : (v k : EReal) = f (x (k+1)) :=
    EReal.coe_toReal (hsub k).1 (hproper.1 _)
  have hM : (m : EReal) = f z := EReal.coe_toReal hzero.1 (hproper.1 z)
  change Tendsto (fun k => (v k : EReal)) atTop (𝓝 (m : EReal)) at hE
  simp_rw [hF,hM] at hE
  exact (tendsto_add_atTop_iff_nat 1).mp hE

/-- The original C2 cluster case permits a limit on the boundary of the open zone. -/
theorem subgradient_cluster_zero (T : H → Set H) (S : Set H) (h : H → ℝ)
    (c : ℕ → ℝ) (x : ℕ → H) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k) (hx : IsBregmanPPARun S h T c x)
    (f : H → EReal) (hproper : IsProperFn f) (hf : LowerSemicontinuous f)
    (hTeq : T = subdiffOp f) (hz : (zer T).Nonempty)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (p : H) (hlim : Tendsto (x ∘ φ) atTop (𝓝 p)) :
    p ∈ zer T := by
  obtain ⟨z,hz⟩ := hz
  have hm := subgradient_objective_limit T S h c x hh hdom hc hcinf hx f hproper hTeq z hz
  have hbound : f p ≤ f z := lsc_objective_limit f hf (x ∘ φ) p (f z) hlim
    (by simpa only [Function.comp_def] using hm.comp hφ.tendsto_atTop)
  have hzero : IsSubgradient f z 0 := by
    simpa only [hTeq,zer,subdiffOp,Set.mem_ofPred_eq] using hz
  have hmin (v : H) : f z ≤ f v := by simpa using hzero.2 v
  have hp := zero_subgradient_of_min f (ne_top_of_le_ne_top hzero.1 hbound)
    (fun v => hbound.trans (hmin v))
  change (0 : H) ∈ T p
  rw [hTeq]
  exact hp
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence InertialFB.IFB
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem step2 (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hx : IsBregmanPPARun S h T c x)
    (hC : closure (dom T) ⊆ S ∨ ∃ f : H → EReal,
      IsProperFn f ∧ IsConvexFn f ∧ LowerSemicontinuous f ∧ T = subdiffOp f)
    (hz : (zer T).Nonempty) :
    ∀ (p : H) (φ : ℕ → ℕ), StrictMono φ → Tendsto (x ∘ φ) atTop (𝓝 p) → p ∈ zer T := by
  intro p φ hφ hlim
  rcases hC with hC1 | ⟨f,hproper,hconv,hf,hTeq⟩
  · exact interior_cluster_zero T S h c x hT hh hdom hc hcinf hx hz hC1 φ hφ p hlim
  · exact subgradient_cluster_zero T S h c x hh hdom hc hcinf hx f hproper hf hTeq hz φ hφ p hlim
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence InertialFB.IFB
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem step3 (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hx : IsBregmanPPARun S h T c x)
    (hC : closure (dom T) ⊆ S ∨ ∃ f : H → EReal,
      IsProperFn f ∧ IsConvexFn f ∧ LowerSemicontinuous f ∧ T = subdiffOp f)
    (x' : H) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (x ∘ φ) atTop (𝓝 x')) (hzero : x' ∈ zer T) :
    Tendsto x atTop (𝓝 x') := by
  have hzc := zero_mem_closure T S hdom hzero
  have hanti := distance_antitone T S h c x hT.1 hh hc hx x' hzero
  have hDφ := hh.tendsto_zero (x ∘ φ) x' (fun k => (hx (φ k)).1) hlim
  have hD : Tendsto (fun k => bregmanD h x' (x k)) atTop (𝓝 0) := by
    apply (tendsto_iff_tendsto_subseq_of_antitone hanti hφ.tendsto_atTop).mpr
    simpa only [Function.comp_def] using hDφ
  have hb := (step1 T S h c x hT hh hdom hc hcinf hx x' hzero).2.2
  apply hb.isCompact_closure.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall (fun k => subset_closure (Set.mem_range_self k)))
  intro u _ hu
  obtain ⟨ψ,hψ,hψlim⟩ := hu.tendsto_subseq
  have huc : u ∈ closure S := isClosed_closure.mem_of_tendsto hψlim
    (Eventually.of_forall (fun k => subset_closure (hx (ψ k)).1))
  have hDψ : Tendsto (fun k => bregmanD h x' ((x ∘ ψ) k)) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using hD.comp hψ.tendsto_atTop
  have hconst : Tendsto (fun _ : ℕ => x') atTop (𝓝 u) :=
    hh.tendsto_of_zero (fun _ => x') (x ∘ ψ) u (fun _ => hzc)
      (fun k => (hx (ψ k)).1) hψlim huc (by simp) hDψ
  exact tendsto_nhds_unique hconst tendsto_const_nhds
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence InertialFB.IFB
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- The exact first conclusion of the original root, with both original hC alternatives. -/
theorem convergence_when_zero (T : H → Set H) (S : Set H) (h : H → ℝ)
    (c : ℕ → ℝ) (x : ℕ → H) (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k) (hx : IsBregmanPPARun S h T c x)
    (hC : closure (dom T) ⊆ S ∨ ∃ f : H → EReal,
      IsProperFn f ∧ IsConvexFn f ∧ LowerSemicontinuous f ∧ T = subdiffOp f) :
    (zer T).Nonempty → ∃ z : H, z ∈ zer T ∧ Tendsto x atTop (𝓝 z) := by
  intro hz
  obtain ⟨z,hz0⟩ := hz
  have hb := (step1 T S h c x hT hh hdom hc hcinf hx z hz0).2.2
  obtain ⟨p,_,φ,hφ,hlim⟩ := tendsto_subseq_of_bounded hb (fun k => Set.mem_range_self k)
  have hp := step2 T S h c x hT hh hdom hc hcinf hx hC ⟨z,hz0⟩ p φ hφ hlim
  exact ⟨p,hp,step3 T S h c x hT hh hdom hc hcinf hx hC p φ hφ hlim hp⟩
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology Finset
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
noncomputable def prefix_weight (c : ℕ → ℝ) (N : ℕ) : ℝ := ∑ k ∈ range N, c k
noncomputable def weighted_mean (c : ℕ → ℝ) (x : ℕ → H) (N : ℕ) : H :=
  (prefix_weight c N)⁻¹ • ∑ k ∈ range N, c k • x (k+1)

theorem prefix_weight_lower (c : ℕ → ℝ) (ε : ℝ) (hle : ∀ k, ε ≤ c k) (N : ℕ) :
    ε*(N : ℝ) ≤ prefix_weight c N := by
  calc
    _ = ∑ k ∈ range N, ε := by simp <;> ring
    _ ≤ _ := sum_le_sum (fun k _ => hle k)

theorem prefix_weight_pos (c : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hle : ∀ k, ε ≤ c k) (N : ℕ) (hN : 0 < N) : 0 < prefix_weight c N :=
  lt_of_lt_of_le (mul_pos hε (by exact_mod_cast hN)) (prefix_weight_lower c ε hle N)

theorem weighted_mean_norm_bound (c : ℕ → ℝ) (x : ℕ → H) (ε R : ℝ)
    (hc : ∀ k, 0 < c k) (hε : 0 < ε) (hle : ∀ k, ε ≤ c k) (hR : 0 ≤ R)
    (hx : ∀ k, ‖x (k+1)‖ ≤ R) (N : ℕ) : ‖weighted_mean c x N‖ ≤ R := by
  by_cases hN : N=0
  · subst N; simpa [weighted_mean,prefix_weight] using hR
  have hW := prefix_weight_pos c ε hε hle N (by omega)
  have hs : ‖∑ k ∈ range N, c k • x (k+1)‖ ≤ prefix_weight c N*R := by
    calc
      _ ≤ ∑ k ∈ range N, ‖c k • x (k+1)‖ := norm_sum_le _ _
      _ = ∑ k ∈ range N, c k*‖x (k+1)‖ := sum_congr rfl (fun k _ => by
        rw [norm_smul,Real.norm_of_nonneg (hc k).le])
      _ ≤ ∑ k ∈ range N, c k*R := sum_le_sum (fun k _ =>
        mul_le_mul_of_nonneg_left (hx k) (hc k).le)
      _ = prefix_weight c N*R := by simp only [prefix_weight,sum_mul]
  rw [weighted_mean,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hW).le]
  calc
    _ ≤ (prefix_weight c N)⁻¹*(prefix_weight c N*R) :=
      mul_le_mul_of_nonneg_left hs (inv_pos.mpr hW).le
    _ = R := by rw [← mul_assoc,inv_mul_cancel₀ hW.ne',one_mul]

theorem graph_prefix_energy (T : H → Set H) (S : Set H) (h : H → ℝ)
    (c : ℕ → ℝ) (x : ℕ → H) (hT : IsMonotoneOp T) (hh : IsBregmanFunction S h)
    (hc : ∀ k, 0 < c k) (hx : IsBregmanPPARun S h T c x)
    (v w : H) (hw : w ∈ T v) (N : ℕ) :
    (∑ k ∈ range N, c k*inner ℝ w (x (k+1)-v))+bregmanD h v (x N) ≤ bregmanD h v (x 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have ht := weighted_graph_comparison T h hT v w (x N) (x (N+1)) (c N) (hc N) hw (hx N).2
    have hn := bregman_nonneg S h hh (subset_closure (hx (N+1)).1) (hx N).1
    linarith

theorem weighted_mean_pairing (c : ℕ → ℝ) (x : ℕ → H) (v w : H) (N : ℕ)
    (hW : 0 < prefix_weight c N) :
    prefix_weight c N*inner ℝ w (weighted_mean c x N-v) =
      ∑ k ∈ range N, c k*inner ℝ w (x (k+1)-v) := by
  simp only [weighted_mean,inner_sub_right,inner_smul_right,inner_sum,mul_sub,
    sum_sub_distrib,← sum_mul]
  rw [← mul_assoc,mul_inv_cancel₀ hW.ne',one_mul]
  rfl

theorem weighted_mean_graph_bound (T : H → Set H) (S : Set H) (h : H → ℝ)
    (c : ℕ → ℝ) (x : ℕ → H) (hT : IsMonotoneOp T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k) (hx : IsBregmanPPARun S h T c x)
    (ε : ℝ) (hε : 0 < ε) (hle : ∀ k, ε ≤ c k) (v w : H) (hw : w ∈ T v)
    (N : ℕ) (hN : 0 < N) :
    inner ℝ w (weighted_mean c x N-v) ≤ (bregmanD h v (x 0)/ε)/(N : ℝ) := by
  have hW := prefix_weight_pos c ε hε hle N hN
  have hvc : v ∈ closure S := hdom ⟨w,hw⟩
  have hB := bregman_nonneg S h hh hvc (hx 0).1
  have hBN := bregman_nonneg S h hh hvc (hx N).1
  have hsum := graph_prefix_energy T S h c x hT hh hc hx v w hw N
  have hpair := weighted_mean_pairing c x v w N hW
  have hfirst : inner ℝ w (weighted_mean c x N-v) ≤ bregmanD h v (x 0)/prefix_weight c N := by
    apply (le_div_iff₀ hW).mpr
    nlinarith
  have hden := div_le_div_of_nonneg_left hB (mul_pos hε (by exact_mod_cast hN))
    (prefix_weight_lower c ε hle N)
  exact hfirst.trans (by simpa only [div_div] using hden)

theorem zero_of_bounded_run (T : H → Set H) (S : Set H) (h : H → ℝ)
    (c : ℕ → ℝ) (x : ℕ → H) (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k) (hx : IsBregmanPPARun S h T c x)
    (hb : Bornology.IsBounded (Set.range x)) : (zer T).Nonempty := by
  obtain ⟨ε,hε,hle⟩ := hcinf
  obtain ⟨R,hR,hRx⟩ := hb.exists_pos_norm_le
  have hbmean : Bornology.IsBounded (Set.range (weighted_mean c x)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨R, ?_⟩
    rintro _ ⟨N,rfl⟩
    exact weighted_mean_norm_bound c x ε R hc hε hle hR.le
      (fun k => hRx _ (Set.mem_range_self (k+1))) N
  obtain ⟨u,_,φ,hφ,hlim⟩ := tendsto_subseq_of_bounded hbmean (fun k => Set.mem_range_self k)
  refine ⟨u, ?_⟩
  apply maximal_related_point T hT u 0
  intro v w hw
  have hev : ∀ᶠ N in atTop, inner ℝ w (weighted_mean c x N-v) ≤
      (bregmanD h v (x 0)/ε)/(N : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact weighted_mean_graph_bound T S h c x hT.1 hh hdom hc hx ε hε hle v w hw N (by omega)
  have hi : Tendsto (fun k => inner ℝ w (weighted_mean c x (φ k)-v)) atTop
      (𝓝 (inner ℝ w (u-v))) := tendsto_const_nhds.inner (hlim.sub_const v)
  have hz : Tendsto (fun k => (bregmanD h v (x 0)/ε)/(φ k : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat _).comp hφ.tendsto_atTop
  have hu : inner ℝ w (u-v) ≤ 0 := le_of_tendsto_of_tendsto hi hz
    (hφ.tendsto_atTop.eventually hev)
  rw [zero_sub,inner_neg_right]
  have he : inner ℝ (u-v) w = inner ℝ w (u-v) := real_inner_comm _ _
  rw [he]
  linarith
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence InertialFB.IFB
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem theorem1 (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hx : IsBregmanPPARun S h T c x)
    (hC : closure (dom T) ⊆ S ∨ ∃ f : H → EReal,
      IsProperFn f ∧ IsConvexFn f ∧ LowerSemicontinuous f ∧ T = subdiffOp f) :
    ((zer T).Nonempty → ∃ z : H, z ∈ zer T ∧ Tendsto x atTop (𝓝 z)) ∧
    (zer T = ∅ → closure (dom T) ⊆ S → ¬ Bornology.IsBounded (Set.range x)) := by
  constructor
  · exact convergence_when_zero T S h c x hT hh hdom hc hcinf hx hC
  · intro hnone hC1 hb
    obtain ⟨u,hu⟩ := zero_of_bounded_run T S h c x hT hh hdom hc hcinf hx hb
    simpa [hnone] using hu
end BregmanPPACodex

end

set_option autoImplicit false
open BregmanPPA.Convergence ThreeOpSplitting.Convergence InertialFB.IFB Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Theorem 1: convergence to a zero, or unboundedness when there are no zeros under (C1). -/
theorem solution (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hx : IsBregmanPPARun S h T c x)
    (hC : closure (dom T) ⊆ S ∨ ∃ f : H → EReal,
      IsProperFn f ∧ IsConvexFn f ∧ LowerSemicontinuous f ∧ T = subdiffOp f) :
    ((zer T).Nonempty → ∃ z : H, z ∈ zer T ∧ Tendsto x atTop (𝓝 z)) ∧
    (zer T = ∅ → closure (dom T) ⊆ S → ¬ Bornology.IsBounded (Set.range x)) := by
  exact BregmanPPACodex.theorem1 T S h c x hT hh hdom hc hcinf hx hC



#print axioms solution
