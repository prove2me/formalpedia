-- Prove2me | solution 1 for BregmanPPA.EqMult.theorem6
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T19:35:37.964354+00:00
-- url     : https://prove2.me/submissions/71f4e174-5c83-4488-8134-00c548172071

import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_EqMult_EqConstrainedProgram
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_fenchelConjugate
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
open ConvexOptimization
namespace BregmanEqMultCodex
variable {m : ℕ}

theorem conjugate_at_gradient (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : BregmanPPA.Convergence.IsBregmanFunction Set.univ h)
    (x : EuclideanSpace ℝ (Fin m)) :
    fenchelConjugate h (gradient h x)=((inner ℝ x (gradient h x)-h x : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro z
    apply EReal.coe_le_coe_iff.mpr
    have hs := BregmanPPACodex.gradient_support Set.univ h hh
      (y := x) (z := z) (by trivial) (by simp)
    rw [inner_sub_right,real_inner_comm] at hs
    have hc : inner ℝ (gradient h x) x=inner ℝ x (gradient h x) := real_inner_comm _ _
    rw [hc] at hs
    linarith
  · exact le_iSup_of_le x le_rfl

theorem conjugate_finite (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : BregmanPPA.Convergence.IsBregmanFunction Set.univ h)
    (him : Function.Surjective (gradient h)) (w : EuclideanSpace ℝ (Fin m)) :
    fenchelConjugate h w ≠ ⊥ ∧ fenchelConjugate h w ≠ ⊤ := by
  obtain ⟨x,rfl⟩ := him w
  rw [conjugate_at_gradient h hh x]
  exact ⟨EReal.coe_ne_bot _,EReal.coe_ne_top _⟩
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open ConvexOptimization
namespace BregmanEqMultCodex
variable {m : ℕ}

noncomputable def conjugate_real (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (w : EuclideanSpace ℝ (Fin m)) : ℝ := (fenchelConjugate h w).toReal

theorem conjugate_real_at_gradient (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : BregmanPPA.Convergence.IsBregmanFunction Set.univ h)
    (x : EuclideanSpace ℝ (Fin m)) :
    conjugate_real h (gradient h x)=inner ℝ x (gradient h x)-h x := by
  simp only [conjugate_real,conjugate_at_gradient h hh x,EReal.toReal_coe]

theorem conjugate_real_bound (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : BregmanPPA.Convergence.IsBregmanFunction Set.univ h)
    (him : Function.Surjective (gradient h)) (x w : EuclideanSpace ℝ (Fin m)) :
    inner ℝ x w-h x ≤ conjugate_real h w := by
  obtain ⟨z,rfl⟩ := him w
  have he : ((inner ℝ x (gradient h z)-h x : ℝ) : EReal) ≤
      fenchelConjugate h (gradient h z) := le_iSup_of_le x le_rfl
  rw [conjugate_at_gradient h hh z] at he
  rw [conjugate_real_at_gradient h hh z]
  exact EReal.coe_le_coe_iff.mp he

theorem conjugate_real_convex (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : BregmanPPA.Convergence.IsBregmanFunction Set.univ h)
    (him : Function.Surjective (gradient h)) : ConvexOn ℝ Set.univ (conjugate_real h) := by
  refine ⟨convex_univ,?_⟩
  intro u _ v _ a b ha hb hab
  obtain ⟨z,hz⟩ := him (a • u+b • v)
  have he : conjugate_real h (a • u+b • v)=inner ℝ z (a • u+b • v)-h z := by
    rw [← hz,conjugate_real_at_gradient h hh z]
  have h1 := conjugate_real_bound h hh him z u
  have h2 := conjugate_real_bound h hh him z v
  have ha1 := mul_le_mul_of_nonneg_left h1 ha
  have hb2 := mul_le_mul_of_nonneg_left h2 hb
  rw [he,inner_add_right,inner_smul_right,inner_smul_right]
  simp only [smul_eq_mul]
  nlinarith [show (a+b)*h z=h z by rw [hab,one_mul]]

theorem conjugate_real_continuous (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : BregmanPPA.Convergence.IsBregmanFunction Set.univ h)
    (him : Function.Surjective (gradient h)) : Continuous (conjugate_real h) := by
  exact continuousOn_univ.mp ((conjugate_real_convex h hh him).continuousOn isOpen_univ)
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open Filter Topology BregmanPPA.Convergence
namespace BregmanEqMultCodex
variable {m : ℕ}

theorem inverse_gradient_local_bound (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) (him : Function.Surjective (gradient h))
    (w₀ : EuclideanSpace ℝ (Fin m)) :
    ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ x : EuclideanSpace ℝ (Fin m),
      gradient h x ∈ Metric.ball w₀ δ → ‖x‖ ≤ R := by
  have ht := (conjugate_real_continuous h hh him).continuousAt.tendsto (x := w₀)
  have hb : ∀ᶠ w in 𝓝 w₀, conjugate_real h w < conjugate_real h w₀+1 :=
    ht.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hb
  obtain ⟨R,hR,hbound⟩ := (hh.bounded_L₂ (h 0+conjugate_real h w₀+1) 0 (by simp)).exists_pos_norm_le
  refine ⟨δ,R,hδ,hR,?_⟩
  intro x hx
  apply hbound x
  refine ⟨by trivial,?_⟩
  have he : bregmanD h 0 x=h 0+conjugate_real h (gradient h x) := by
    rw [conjugate_real_at_gradient h hh x]
    simp only [bregmanD,zero_sub,inner_neg_right]
    rw [real_inner_comm]
    ring
  rw [he]
  have hb' : conjugate_real h (gradient h x) < conjugate_real h w₀+1 := hball hx
  linarith
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open BregmanPPA.Convergence
namespace BregmanEqMultCodex
variable {m : ℕ}

theorem original_gradient_injective (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) : Function.Injective (gradient h) := by
  intro x y hxy
  let F : EuclideanSpace ℝ (Fin m) → ℝ := fun z => h z-inner ℝ (gradient h x) z
  have hs : StrictConvexOn ℝ Set.univ h := by simpa only [closure_univ] using hh.strictConvexOn
  have hl : ConcaveOn ℝ Set.univ (fun z => inner ℝ (gradient h x) z) := by
    refine ⟨convex_univ,?_⟩
    intro u _ v _ a b _ _ _
    simp only [inner_add_right,inner_smul_right,smul_eq_mul]
    exact le_rfl
  have hf : StrictConvexOn ℝ Set.univ F := hs.sub_concaveOn hl
  have hx : IsMinOn F Set.univ x := by
    intro z _
    have hi := BregmanPPACodex.gradient_support Set.univ h hh
      (y := x) (z := z) (by trivial) (by simp)
    rw [inner_sub_right] at hi
    dsimp [F]; linarith
  have hy : IsMinOn F Set.univ y := by
    intro z _
    have hi := BregmanPPACodex.gradient_support Set.univ h hh
      (y := y) (z := z) (by trivial) (by simp)
    rw [← hxy,inner_sub_right] at hi
    dsimp [F]; linarith
  exact hf.eq_of_isMinOn hx hy (by trivial) (by trivial)

noncomputable def inverse_gradient (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (him : Function.Surjective (gradient h)) (w : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) := Classical.choose (him w)

theorem gradient_inverse (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (him : Function.Surjective (gradient h)) (w : EuclideanSpace ℝ (Fin m)) :
    gradient h (inverse_gradient h him w)=w := Classical.choose_spec (him w)

theorem inverse_gradient_gradient (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) (him : Function.Surjective (gradient h))
    (x : EuclideanSpace ℝ (Fin m)) : inverse_gradient h him (gradient h x)=x :=
  original_gradient_injective h hh (gradient_inverse h him (gradient h x))
end BregmanEqMultCodex

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
open Filter Topology BregmanPPA.Convergence
namespace BregmanEqMultCodex
variable {m : ℕ}

theorem inverse_gradient_continuous (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) (him : Function.Surjective (gradient h)) :
    Continuous (inverse_gradient h him) := by
  apply continuous_iff_continuousAt.mpr
  intro w₀
  obtain ⟨δ,R,hδ,_,hbound⟩ := inverse_gradient_local_bound h hh him w₀
  change Tendsto (inverse_gradient h him) (𝓝 w₀) (𝓝 (inverse_gradient h him w₀))
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) R).tendsto_nhds_of_unique_mapClusterPt
  · filter_upwards [Metric.isOpen_ball.mem_nhds (show w₀ ∈ Metric.ball w₀ δ by
        simpa only [Metric.mem_ball,dist_self] using hδ)] with w hw
    rw [Metric.mem_closedBall,dist_zero_right]
    apply hbound (inverse_gradient h him w)
    rwa [gradient_inverse]
  · intro x _ hx
    have hg := (BregmanPPACodex.gradient_continuous_in_zone Set.univ h hh
      (p := x) (by trivial)).tendsto
    have hc := hx.tendsto_comp hg
    have hid : gradient h ∘ inverse_gradient h him=id := funext (gradient_inverse h him)
    rw [hid] at hc
    have he : gradient h x=w₀ := eq_of_nhds_neBot (by
      simpa only [MapClusterPt,Filter.map_id,ClusterPt] using hc)
    apply original_gradient_injective h hh
    rwa [gradient_inverse]
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open Filter Topology BregmanPPA.Convergence
namespace BregmanEqMultCodex
variable {m : ℕ}

theorem conjugate_inverse_value (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) (him : Function.Surjective (gradient h))
    (w : EuclideanSpace ℝ (Fin m)) :
    conjugate_real h w=inner ℝ (inverse_gradient h him w) w-h (inverse_gradient h him w) := by
  have he := conjugate_real_at_gradient h hh (inverse_gradient h him w)
  rwa [gradient_inverse] at he

theorem conjugate_support (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) (him : Function.Surjective (gradient h))
    (w v : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (inverse_gradient h him w) (v-w) ≤ conjugate_real h v-conjugate_real h w := by
  have hb := conjugate_real_bound h hh him (inverse_gradient h him w) v
  rw [conjugate_inverse_value h hh him w,inner_sub_right]
  linarith

theorem conjugate_hasFDerivAt (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) (him : Function.Surjective (gradient h))
    (w : EuclideanSpace ℝ (Fin m)) :
    HasFDerivAt (conjugate_real h) ((InnerProductSpace.toDual ℝ _) (inverse_gradient h him w)) w := by
  apply hasFDerivAt_iff_isLittleO.mpr
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hj : Tendsto (inverse_gradient h him) (𝓝 w) (𝓝 (inverse_gradient h him w)) :=
    (inverse_gradient_continuous h hh him).continuousAt.tendsto
  have ht : Tendsto (fun v => ‖inverse_gradient h him v-inverse_gradient h him w‖)
      (𝓝 w) (𝓝 0) := by
    simpa only [sub_self,norm_zero] using
      (hj.sub_const (inverse_gradient h him w)).norm
  filter_upwards [ht.eventually (Iio_mem_nhds hε)] with v hv
  have hl := conjugate_support h hh him w v
  have hu := conjugate_support h hh him v w
  rw [← neg_sub v w,inner_neg_right] at hu
  have hp : 0 ≤ conjugate_real h v-conjugate_real h w-inner ℝ (inverse_gradient h him w) (v-w) := by
    linarith
  have hb : conjugate_real h v-conjugate_real h w-inner ℝ (inverse_gradient h him w) (v-w) ≤
      inner ℝ (inverse_gradient h him v-inverse_gradient h him w) (v-w) := by
    rw [inner_sub_left]; linarith
  simp only [InnerProductSpace.toDual_apply_apply]
  rw [Real.norm_of_nonneg hp]
  exact hb.trans ((real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right hv.le (norm_nonneg _)))

theorem gradient_conjugate_inverse (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) (him : Function.Surjective (gradient h))
    (w : EuclideanSpace ℝ (Fin m)) :
    gradient (conjugate_real h) w=inverse_gradient h him w := by
  have hd := (conjugate_hasFDerivAt h hh him w).fderiv
  change (InnerProductSpace.toDual ℝ _).symm (fderiv ℝ (conjugate_real h) w)=_
  rw [hd]
  exact (InnerProductSpace.toDual ℝ _).symm_apply_apply _
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.EqMult
namespace BregmanEqMultCodex
variable {n : ℕ}

theorem original_primal_extension_proper (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (hP : IsEqProgram X f) : IsProperFn (fX X f) := by
  classical
  constructor
  · intro x
    apply EReal.add_ne_bot_iff.mpr
    refine ⟨hP.ne_bot x,?_⟩
    simp only [indicatorE]
    split <;> simp
  · obtain ⟨x,hx,hf⟩ := hP.finite_on_X
    refine ⟨x,?_⟩
    simpa only [fX,indicatorE,if_pos hx,add_zero] using hf

theorem original_primal_extension_convex (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (hP : IsEqProgram X f) : IsConvexFn (fX X f) := by
  classical
  have he (u : EuclideanSpace ℝ (Fin n) × ℝ) :
      fX X f u.1 ≤ (u.2 : EReal) ↔ u.1 ∈ X ∧ f u.1 ≤ (u.2 : EReal) := by
    by_cases hx : u.1 ∈ X
    · simp [fX,indicatorE,hx]
    · simp [fX,indicatorE,hx,EReal.add_top_of_ne_bot (hP.ne_bot u.1),top_le_iff]
  intro u hu v hv a b ha hb hab
  change fX X f u.1 ≤ (u.2 : EReal) at hu
  change fX X f v.1 ≤ (v.2 : EReal) at hv
  change fX X f (a • u+b • v).1 ≤ ((a • u+b • v).2 : EReal)
  rw [he] at hu hv ⊢
  exact ⟨hP.convex hu.1 hv.1 ha hb hab,hP.convexFn hu.2 hv.2 ha hb hab⟩
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB
namespace BregmanEqMultCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Necessary subgradient condition for the original extended-real convex objective. -/
theorem convex_smooth_min_subgradient (F : H → EReal) (hp : IsProperFn F)
    (hc : IsConvexFn F) (G : H → ℝ) (z g : H)
    (hd : HasFDerivAt G ((InnerProductSpace.toDual ℝ H) g) z)
    (hmin : ∀ y, F z+(G z : EReal) ≤ F y+(G y : EReal)) :
    IsSubgradient F z (-g) := by
  have hz : F z ≠ ⊤ := by
    obtain ⟨y,hy⟩ := hp.2
    have hey := EReal.coe_toReal hy (hp.1 y)
    intro hzt
    have hm := hmin y
    rw [hzt,EReal.top_add_coe,← hey,← EReal.coe_add] at hm
    exact EReal.coe_ne_top _ (top_le_iff.mp hm)
  refine ⟨hz,?_⟩
  intro y
  by_cases hy : F y=⊤
  · rw [hy]; exact le_top
  have ez := EReal.coe_toReal hz (hp.1 z)
  have ey := EReal.coe_toReal hy (hp.1 y)
  rw [← ez,← ey,← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  let l : ℝ →ᵃ[ℝ] H := AffineMap.lineMap z y
  have hder : HasDerivAt (G ∘ l) (inner ℝ g (y-z)) 0 := by
    simpa only [l,InnerProductSpace.toDual_apply_apply] using
      hd.comp_hasDerivAt_of_eq (0 : ℝ)
        (AffineMap.hasDerivAt_lineMap (a := z) (b := y) (x := (0 : ℝ))) (by simp)
  have hb : ∀ t : ℝ, 0 < t → t < 1 →
      (F z).toReal-(F y).toReal ≤ t⁻¹*(G (l t)-G z) := by
    intro t ht ht1
    have hez : (z,(F z).toReal) ∈ {p : H × ℝ | F p.1 ≤ (p.2 : EReal)} := by
      change F z ≤ ((F z).toReal : EReal); rw [ez]
    have hey : (y,(F y).toReal) ∈ {p : H × ℝ | F p.1 ≤ (p.2 : EReal)} := by
      change F y ≤ ((F y).toReal : EReal); rw [ey]
    have hcv := hc hez hey (show 0 ≤ 1-t by linarith) ht.le (show (1-t)+t=1 by ring)
    change F ((1-t) • z+t • y) ≤ (((1-t)*(F z).toReal+t*(F y).toReal : ℝ) : EReal) at hcv
    have hl : l t=(1-t) • z+t • y := by simp [l,AffineMap.lineMap_apply_module]
    rw [← hl] at hcv
    have hft : F (l t) ≠ ⊤ := ne_of_lt (hcv.trans_lt (EReal.coe_lt_top _))
    have eft := EReal.coe_toReal hft (hp.1 (l t))
    have hm := hmin (l t)
    rw [← ez,← eft,← EReal.coe_add,← EReal.coe_add] at hm
    have hmr := EReal.coe_le_coe_iff.mp hm
    rw [← eft] at hcv
    have hcvr := EReal.coe_le_coe_iff.mp hcv
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ ht).mpr
    change ((F z).toReal-(F y).toReal)*t ≤ G (l t)-G z
    nlinarith
  have hs := hder.tendsto_slope_zero_right
  have hlow : (F z).toReal-(F y).toReal ≤ inner ℝ g (y-z) := by
    apply ge_of_tendsto hs
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
    simpa only [l,Function.comp_def,zero_add,smul_eq_mul,AffineMap.lineMap_apply_zero] using hb t ht ht1
  rw [inner_neg_left]
  linarith
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.Convergence BregmanPPA.EqMult
namespace BregmanEqMultCodex
variable {n m : ℕ}

noncomputable def augmented_cost
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b p : EuclideanSpace ℝ (Fin m)) (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (c : ℝ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
    c⁻¹*conjugate_real h (gradient h p+c • (A z-b))

theorem augmented_cost_hasFDerivAt
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b p : EuclideanSpace ℝ (Fin m)) (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) (him : Function.Surjective (gradient h))
    (c : ℝ) (hc : 0 < c) (z : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (augmented_cost A b p h c)
      ((InnerProductSpace.toDual ℝ _) (ContinuousLinearMap.adjoint A
        (inverse_gradient h him (gradient h p+c • (A z-b))))) z := by
  let w := gradient h p+c • (A z-b)
  have hi : HasFDerivAt (fun y => gradient h p+c • (A y-b)) (c • A) z :=
    ((A.hasFDerivAt.sub_const b).const_smul c).const_add (gradient h p)
  have hd := ((conjugate_hasFDerivAt h hh him w).comp z hi).const_mul c⁻¹
  have he : c⁻¹ • (((InnerProductSpace.toDual ℝ _) (inverse_gradient h him w)).comp (c • A)) =
      (InnerProductSpace.toDual ℝ _) (ContinuousLinearMap.adjoint A (inverse_gradient h him w)) := by
    ext v
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
      smul_eq_mul,InnerProductSpace.toDual_apply_apply,inner_smul_right,
      ContinuousLinearMap.adjoint_inner_left]
    rw [← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul]
  rw [he] at hd
  exact hd

theorem original_primal_subgradient
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (hP : IsEqProgram X f)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (hh : IsBregmanFunction Set.univ h)
    (him : Function.Surjective (gradient h)) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (p : ℕ → EuclideanSpace ℝ (Fin m))
    (hrun : IsEqMultRun A b X f h c x p) (k : ℕ) :
    -(ContinuousLinearMap.adjoint A (p (k+1))) ∈ subdiffOp (fX X f) (x (k+1)) := by
  classical
  let G := augmented_cost A b (p k) h (c k)
  have hx := (hrun k).1
  have hmin : ∀ y, fX X f (x (k+1))+(G (x (k+1)) : EReal) ≤ fX X f y+(G y : EReal) := by
    intro y
    by_cases hy : y ∈ X
    · simpa only [fX,indicatorE,if_pos hx,if_pos hy,add_zero,G,augmented_cost,
        conjugate_real,EReal.toReal_mul,EReal.toReal_coe] using (hrun k).2.1 y hy
    · simp only [fX,indicatorE,if_neg hy,EReal.add_top_of_ne_bot (hP.ne_bot y),EReal.top_add_coe]
      exact le_top
  have hd := augmented_cost_hasFDerivAt A b (p k) h hh him (c k) (hc k) (x (k+1))
  have he := (hrun k).2.2
  change p (k+1)=gradient (conjugate_real h) _ at he
  rw [gradient_conjugate_inverse h hh him] at he
  rw [← he] at hd
  exact convex_smooth_min_subgradient (fX X f) (original_primal_extension_proper X f hP)
    (original_primal_extension_convex X f hP) G (x (k+1))
    (ContinuousLinearMap.adjoint A (p (k+1))) hd hmin
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open Filter Topology BregmanPPA.Convergence BregmanPPA.EqMult
namespace BregmanEqMultCodex
variable {n m : ℕ}

theorem original_gradient_update
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) (him : Function.Surjective (gradient h))
    (c : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (p : ℕ → EuclideanSpace ℝ (Fin m))
    (hrun : IsEqMultRun A b X f h c x p) (k : ℕ) :
    gradient h (p (k+1))-gradient h (p k)=c k • (A (x (k+1))-b) := by
  have he := (hrun k).2.2
  change p (k+1)=gradient (conjugate_real h) _ at he
  rw [gradient_conjugate_inverse h hh him] at he
  rw [he,gradient_inverse]
  abel

theorem original_asymptotic_feasibility
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) (him : Function.Surjective (gradient h))
    (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (p : ℕ → EuclideanSpace ℝ (Fin m))
    (hrun : IsEqMultRun A b X f h c x p) (pstar : EuclideanSpace ℝ (Fin m))
    (hp : Tendsto p atTop (𝓝 pstar)) : Tendsto (fun k => A (x k)) atTop (𝓝 b) := by
  have hg := (BregmanPPACodex.gradient_continuous_in_zone Set.univ h hh
    (p := pstar) (by trivial)).tendsto
  have hgp := hg.comp hp
  have hdiff : Tendsto (fun k => gradient h (p (k+1))-gradient h (p k)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,sub_self] using
      (hgp.comp (tendsto_add_atTop_nat 1)).sub hgp
  obtain ⟨ε,hε,hle⟩ := hcinf
  have hr := BregmanPPACodex.bounded_inverse_residual _ c ε hε hc hle hdiff
  have he (k : ℕ) : (c k)⁻¹ • (gradient h (p (k+1))-gradient h (p k))=A (x (k+1))-b := by
    rw [original_gradient_update A b X f h hh him c x p hrun k,
      smul_smul,inv_mul_cancel₀ (hc k).ne',one_smul]
  simp_rw [he] at hr
  have hs : Tendsto (fun k => A (x (k+1))) atTop (𝓝 b) := by
    simpa only [sub_add_cancel,zero_add] using hr.add_const b
  exact (tendsto_add_atTop_iff_nat 1).mp hs
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.Convergence BregmanPPA.EqMult
namespace BregmanEqMultCodex
variable {n m : ℕ}

theorem dual_subgradient_of_primal
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (hP : IsEqProgram X f)
    (z : EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin m)) (hz : z ∈ X)
    (hs : -(ContinuousLinearMap.adjoint A u) ∈ subdiffOp (fX X f) z) :
    b-A z ∈ subdiffOp (negDual A b X f) u := by
  classical
  have hfz : f z ≠ ⊤ := by
    simpa only [fX,indicatorE,if_pos hz,add_zero] using hs.1
  have ez := EReal.coe_toReal hfz (hP.ne_bot z)
  have hmin (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ X) :
      f z+((inner ℝ u (A z-b) : ℝ) : EReal) ≤ f y+((inner ℝ u (A y-b) : ℝ) : EReal) := by
    have hi := hs.2 y
    simp only [fX,indicatorE,if_pos hz,if_pos hy,add_zero] at hi
    have he : inner ℝ (-(ContinuousLinearMap.adjoint A u)) (y-z)+inner ℝ u (A y-b)=
        inner ℝ u (A z-b) := by
      simp only [inner_neg_left,ContinuousLinearMap.adjoint_inner_left,inner_sub_right]
      ring
    have hh := add_le_add hi (le_refl ((inner ℝ u (A y-b) : ℝ) : EReal))
    rw [add_assoc,← EReal.coe_add,he] at hh
    exact hh
  have hdu : dualEq A b X f u=((f z).toReal+inner ℝ u (A z-b) : ℝ) := by
    apply le_antisymm
    · have hi : dualEq A b X f u ≤ f z+((inner ℝ u (A z-b) : ℝ) : EReal) :=
        iInf_le_of_le z (iInf_le_of_le hz le_rfl)
      rwa [← ez,← EReal.coe_add] at hi
    · rw [EReal.coe_add,ez]
      exact le_iInf (fun y => le_iInf (fun hy => hmin y hy))
  have hn : negDual A b X f u ≠ ⊤ := by
    rw [negDual,hdu,← EReal.coe_neg]
    exact EReal.coe_ne_top _
  refine ⟨hn,?_⟩
  intro q
  have hq : dualEq A b X f q ≤ (((f z).toReal+inner ℝ q (A z-b) : ℝ) : EReal) := by
    have hi : dualEq A b X f q ≤ f z+((inner ℝ q (A z-b) : ℝ) : EReal) :=
      iInf_le_of_le z (iInf_le_of_le hz le_rfl)
    rwa [← ez,← EReal.coe_add] at hi
  by_cases hqb : dualEq A b X f q=⊥
  · simp only [negDual,hqb,EReal.neg_bot]; exact le_top
  have hqt : dualEq A b X f q ≠ ⊤ := ne_of_lt (hq.trans_lt (EReal.coe_lt_top _))
  have eq := EReal.coe_toReal hqt hqb
  rw [← eq] at hq
  have hqr := EReal.coe_le_coe_iff.mp hq
  change -(dualEq A b X f u)+((inner ℝ (b-A z) (q-u) : ℝ) : EReal) ≤ -(dualEq A b X f q)
  rw [hdu,← eq,← EReal.coe_neg,← EReal.coe_neg,← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  have he : inner ℝ (b-A z) (q-u)=inner ℝ u (A z-b)-inner ℝ q (A z-b) := by
    rw [← neg_sub (A z) b,inner_neg_left,inner_sub_right]
    rw [show inner ℝ (A z-b) q=inner ℝ q (A z-b) from real_inner_comm _ _,
      show inner ℝ (A z-b) u=inner ℝ u (A z-b) from real_inner_comm _ _]
    ring
  rw [he]
  linarith

theorem original_dual_ppa_run
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (hP : IsEqProgram X f)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (hh : IsBregmanFunction Set.univ h)
    (him : Function.Surjective (gradient h)) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (p : ℕ → EuclideanSpace ℝ (Fin m))
    (hrun : IsEqMultRun A b X f h c x p) :
    IsBregmanPPARun Set.univ h (subdiffOp (negDual A b X f)) c p := by
  intro k
  refine ⟨by trivial,?_⟩
  have hs := original_primal_subgradient A b X f hP h hh him c hc x p hrun k
  have hd := dual_subgradient_of_primal A b X f hP (x (k+1)) (p (k+1)) (hrun k).1 hs
  have he : (c k)⁻¹ • (gradient h (p k)-gradient h (p (k+1)))=b-A (x (k+1)) := by
    rw [← neg_sub (gradient h (p (k+1))) (gradient h (p k)),
      original_gradient_update A b X f h hh him c x p hrun k,smul_neg,smul_smul,
      inv_mul_cancel₀ (hc k).ne',one_smul,neg_sub]
  rw [he]
  exact hd
end BregmanEqMultCodex

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
open InertialFB.IFB BregmanPPA.EqMult BregmanPPA.Convergence
namespace BregmanEqMultCodex
variable {n m : ℕ}

theorem original_negdual_le_iff
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (p : EuclideanSpace ℝ (Fin m)) (a : EReal) :
    negDual A b X f p ≤ a ↔ ∀ x ∈ X, -a ≤ f x + ((inner ℝ p (A x-b) : ℝ) : EReal) := by
  simp only [negDual,EReal.neg_le,dualEq,le_iInf_iff]

theorem original_dual_ne_top
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (hP : IsEqProgram X f)
    (p : EuclideanSpace ℝ (Fin m)) : dualEq A b X f p ≠ ⊤ := by
  obtain ⟨z,hz,hzt⟩ := hP.finite_on_X
  have ht : f z + ((inner ℝ p (A z-b) : ℝ) : EReal) < ⊤ := by
    rw [← EReal.coe_toReal hzt (hP.ne_bot z),← EReal.coe_add]
    exact EReal.coe_lt_top _
  exact ne_of_lt ((iInf_le_of_le z (iInf_le_of_le hz le_rfl)).trans_lt ht)

theorem original_negdual_proper
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (hP : IsEqProgram X f)
    (hd : ∃ p, dualEq A b X f p ≠ ⊥) : IsProperFn (negDual A b X f) := by
  refine ⟨fun p hp => original_dual_ne_top A b X f hP p ?_,?_⟩
  · have he := congrArg (fun v : EReal => -v) hp
    simpa only [negDual,neg_neg,EReal.neg_bot] using he
  · obtain ⟨p,hp⟩ := hd
    refine ⟨p,fun ht => hp ?_⟩
    have he := congrArg (fun v : EReal => -v) ht
    simpa only [negDual,neg_neg,EReal.neg_top] using he

theorem original_negdual_lsc
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (hP : IsEqProgram X f) :
    LowerSemicontinuous (negDual A b X f) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  have he : (negDual A b X f) ⁻¹' Set.Iic a =
      ⋂ x, ⋂ (_ : x ∈ X), {p | -a ≤ f x + ((inner ℝ p (A x-b) : ℝ) : EReal)} := by
    ext p
    simp only [Set.mem_preimage,Set.mem_Iic,Set.mem_iInter,Set.mem_setOf_eq]
    exact original_negdual_le_iff A b X f p a
  rw [he]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro hx
  by_cases hxt : f x=⊤
  · simp only [hxt,EReal.top_add_coe,le_top,Set.setOf_true]
    exact isClosed_univ
  · rw [← EReal.coe_toReal hxt (hP.ne_bot x)]
    have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin m) =>
        (((f x).toReal+inner ℝ p (A x-b) : ℝ) : EReal)) :=
      continuous_coe_real_ereal.comp (continuous_const.add (continuous_id.inner continuous_const))
    simp only [← EReal.coe_add]
    exact isClosed_le continuous_const hcont

theorem original_negdual_convex
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (hP : IsEqProgram X f) :
    IsConvexFn (negDual A b X f) := by
  intro u hu v hv α β hα hβ hab
  change negDual A b X f (α • u.1+β • v.1) ≤ ((α*u.2+β*v.2 : ℝ) : EReal)
  apply (original_negdual_le_iff A b X f _ _).mpr
  intro z hz
  by_cases hzt : f z=⊤
  · rw [hzt,EReal.top_add_coe]; exact le_top
  have eu := (original_negdual_le_iff A b X f u.1 (u.2 : EReal)).mp hu z hz
  have ev := (original_negdual_le_iff A b X f v.1 (v.2 : EReal)).mp hv z hz
  have ef := EReal.coe_toReal hzt (hP.ne_bot z)
  rw [← ef,← EReal.coe_add,← EReal.coe_neg] at eu ev ⊢
  have ru := EReal.coe_le_coe_iff.mp eu
  have rv := EReal.coe_le_coe_iff.mp ev
  apply EReal.coe_le_coe_iff.mpr
  simp only [inner_add_left,real_inner_smul_left]
  have hfcomb : α*(f z).toReal+β*(f z).toReal=(f z).toReal := by
    rw [← add_mul,hab,one_mul]
  nlinarith [hfcomb,mul_nonneg hα (sub_nonneg.mpr ru),mul_nonneg hβ (sub_nonneg.mpr rv)]

theorem original_negdual_zero_iff
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hd : ∃ q, dualEq A b X f q ≠ ⊥) (p : EuclideanSpace ℝ (Fin m)) :
    0 ∈ subdiffOp (negDual A b X f) p ↔ IsOptimalMultiplier A b X f p := by
  constructor
  · intro hp q
    have hi := hp.2 q
    simpa only [negDual,inner_zero_left,EReal.coe_zero,add_zero,EReal.neg_le_neg_iff] using hi
  · intro hp
    apply BregmanPPACodex.zero_subgradient_of_min
    · intro ht
      obtain ⟨q,hq⟩ := hd
      have he := congrArg (fun v : EReal => -v) ht
      have hb : dualEq A b X f p=⊥ := by
        simpa only [negDual,neg_neg,EReal.neg_top] using he
      have hi := hp q
      rw [hb] at hi
      exact hq (le_bot_iff.mp hi)
    · intro q
      exact EReal.neg_le_neg_iff.mpr (hp q)
end BregmanEqMultCodex

end

section

namespace RockafellarMaxMono.Shared

/-- Rockafellar (1970), p. 209: a *proper convex function* on a real normed space `V` is a
function `f : V → (−∞, +∞]`, not identically `+∞`, such that
`f((1 − λ)x + λy) ≤ (1 − λ)f(x) + λf(y)` whenever `x, y ∈ V` and `0 < λ < 1`.
The value set `(−∞, +∞]` is encoded as `EReal` together with the requirement that `f`
never takes the value `⊥ = −∞`. -/
def ProperConvex {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : V → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ (∃ x, f x ≠ ⊤) ∧
    ∀ (x y : V) (t : ℝ), 0 < t → t < 1 →
      f ((1 - t) • x + t • y) ≤ ((1 - t : ℝ) : EReal) * f x + ((t : ℝ) : EReal) * f y

end RockafellarMaxMono.Shared


namespace RockafellarMaxMono.Shared

/-- Rockafellar (1970), p. 209: the *subdifferential* of `f : V → (−∞, +∞]` at `x` is
`∂f(x) = {x* ∈ V* | f(y) ≥ f(x) + ⟨y − x, x*⟩ for all y ∈ V}`, a subset of the
(strong) dual `V* = StrongDual ℝ V`; the pairing `⟨y − x, x*⟩` is `x' (y - x)`. -/
def subdiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : V → EReal) (x : V) :
    Set (StrongDual ℝ V) :=
  {x' | ∀ y : V, f x + ((x' (y - x) : ℝ) : EReal) ≤ f y}

end RockafellarMaxMono.Shared


namespace RockafellarMaxMono.Maximality

/-- Rockafellar (1970), p. 209: a multivalued mapping `T : V → V*` (encoded as
`V → Set (StrongDual ℝ V)`) is a *monotone operator* if
`⟨x₀ − x₁, x₀* − x₁*⟩ ≥ 0` whenever `x₀* ∈ T(x₀)` and `x₁* ∈ T(x₁)`. -/
def IsMonotoneOp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V → Set (StrongDual ℝ V)) : Prop :=
  ∀ (x₀ x₁ : V) (x₀' x₁' : StrongDual ℝ V), x₀' ∈ T x₀ → x₁' ∈ T x₁ →
    0 ≤ (x₀' - x₁') (x₀ - x₁)

/-- Rockafellar (1970), p. 209: a monotone operator `T : V → V*` is *maximal monotone* if its
graph `G(T) = {(x, x*) | x* ∈ T(x)}` is not properly contained in the graph of any other
monotone operator `T' : V → V*`; equivalently, every monotone `T'` whose graph contains the
graph of `T` coincides with `T`. -/
def IsMaximalMonotone {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V → Set (StrongDual ℝ V)) : Prop :=
  IsMonotoneOp T ∧
    ∀ T' : V → Set (StrongDual ℝ V), IsMonotoneOp T' → (∀ x, T x ⊆ T' x) → ∀ x, T' x = T x

end RockafellarMaxMono.Maximality

set_option autoImplicit false

/-- Ekeland's variational principle (weak form, with control of the value). -/
theorem rmm_ekeland {X : Type*} [MetricSpace X] [CompleteSpace X] (H : X → ℝ)
    (hH : LowerSemicontinuous H) (m : ℝ) (hm : ∀ x, m ≤ H x) (δ : ℝ) (hδ : 0 < δ) (x₁ : X) :
    ∃ x, H x ≤ H x₁ ∧ ∀ y, H x ≤ H y + δ * dist y x := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : X → Set X, ∀ z y, y ∈ S z ↔ H y + δ * dist y z ≤ H z :=
    ⟨fun z => {y | H y + δ * dist y z ≤ H z}, fun _ _ => Iff.rfl⟩
  have hself : ∀ z, z ∈ S z := by intro z; rw [hS]; simp
  have htrans : ∀ z y w, y ∈ S z → w ∈ S y → w ∈ S z := by
    intro z y w hy hw
    rw [hS] at hy hw ⊢
    have := dist_triangle w y z
    nlinarith
  have hclosed : ∀ z, IsClosed (S z) := by
    intro z
    have h1 : LowerSemicontinuous (fun y => H y + δ * dist y z) :=
      hH.add (Continuous.lowerSemicontinuous (by fun_prop))
    have h2 : S z = (fun y => H y + δ * dist y z) ⁻¹' Set.Iic (H z) := by
      ext y; rw [hS]; rfl
    rw [h2]
    exact h1.isClosed_preimage (H z)
  have hnext : ∀ z, ∃ y ∈ S z, ∀ w ∈ S y, δ * dist w y ≤ H z - H y := by
    intro z
    have hne : (H '' S z).Nonempty := ⟨H z, z, hself z, rfl⟩
    have hbdd : BddBelow (H '' S z) := ⟨m, by rintro _ ⟨y, -, rfl⟩; exact hm y⟩
    have hμ : sInf (H '' S z) ≤ H z := csInf_le hbdd ⟨z, hself z, rfl⟩
    obtain ⟨y, hy, hyμ⟩ : ∃ y ∈ S z, 2 * H y - H z ≤ sInf (H '' S z) := by
      rcases eq_or_lt_of_le hμ with h | h
      · exact ⟨z, hself z, by linarith⟩
      · obtain ⟨_, ⟨y, hy, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne
          (show sInf (H '' S z) < (H z + sInf (H '' S z)) / 2 by linarith)
        exact ⟨y, hy, by linarith⟩
    refine ⟨y, hy, fun w hw => ?_⟩
    have hwz : w ∈ S z := htrans z y w hy hw
    have hw' : sInf (H '' S z) ≤ H w := csInf_le hbdd ⟨w, hwz, rfl⟩
    rw [hS] at hw
    linarith
  choose nxt hnxtS hnxt using hnext
  obtain ⟨z, hz0, hzs⟩ : ∃ z : ℕ → X, z 0 = x₁ ∧ ∀ n, z (n + 1) = nxt (z n) :=
    ⟨fun n => Nat.rec x₁ (fun _ p => nxt p) n, rfl, fun _ => rfl⟩
  have hstep : ∀ n, z (n + 1) ∈ S (z n) := fun n => by rw [hzs]; exact hnxtS _
  have hnest : ∀ n k, n ≤ k → S (z k) ⊆ S (z n) := by
    intro n k hnk
    induction k, hnk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hnk ih => exact fun w hw => ih (htrans _ _ _ (hstep k) hw)
  have hmem : ∀ n k, n ≤ k → z k ∈ S (z n) := fun n k hnk => hnest n k hnk (hself _)
  have hanti : Antitone (fun n => H (z n)) := by
    refine antitone_nat_of_succ_le fun n => ?_
    have h1 := hstep n
    rw [hS] at h1
    have := dist_nonneg (x := z (n + 1)) (y := z n)
    nlinarith
  have hbddz : BddBelow (Set.range fun n => H (z n)) := ⟨m, by rintro _ ⟨n, rfl⟩; exact hm _⟩
  have hlimH := tendsto_atTop_ciInf hanti hbddz
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = ⨅ n, H (z n) := ⟨_, rfl⟩
  rw [← hL] at hlimH
  have hLle : ∀ n, L ≤ H (z n) := fun n => hL ▸ ciInf_le hbddz n
  have hgap : ∀ n, ∀ w ∈ S (z (n + 1)), δ * dist w (z (n + 1)) ≤ H (z n) - L := by
    intro n w hw
    have h1 := hnxt (z n) w (by rw [← hzs]; exact hw)
    rw [← hzs] at h1
    linarith [hLle (n + 1)]
  have he : Filter.Tendsto (fun n => H (z n) - L) Filter.atTop (nhds 0) := by
    simpa using hlimH.sub_const L
  have hcauchy : CauchySeq z := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hev := he.eventually (gt_mem_nhds (show (0:ℝ) < δ * ε by positivity))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    refine ⟨N + 1, fun n hn => ?_⟩
    have h1 := hgap N (z n) (hmem (N + 1) n hn)
    have h2 := hN N le_rfl
    have h3 : δ * dist (z n) (z (N + 1)) < δ * ε := by linarith
    exact lt_of_mul_lt_mul_left h3 hδ.le
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hxS : ∀ n, x ∈ S (z n) := fun n =>
    (hclosed _).mem_of_tendsto hx (Filter.eventually_atTop.2 ⟨n, fun k hk => hmem n k hk⟩)
  refine ⟨x, ?_, fun y => ?_⟩
  · have h1 := hxS 0
    rw [hS, hz0] at h1
    have := dist_nonneg (x := x) (y := x₁)
    nlinarith
  · by_contra hlt
    push Not at hlt
    have hyx : y ∈ S x := by rw [hS]; exact hlt.le
    have hbound : ∀ n, δ * dist y x ≤ 2 * (H (z n) - L) := by
      intro n
      have h1 := hgap n y (htrans _ _ _ (hxS (n + 1)) hyx)
      have h2 := hgap n x (hxS (n + 1))
      have h3 := dist_triangle y (z (n + 1)) x
      rw [dist_comm (z (n + 1)) x] at h3
      nlinarith
    have h0 : δ * dist y x ≤ 0 := by
      have h4 := he.const_mul 2
      simp only [mul_zero] at h4
      exact ge_of_tendsto' h4 hbound
    have hd : dist y x = 0 :=
      le_antisymm (by nlinarith [dist_nonneg (x := y) (y := x)]) dist_nonneg
    rw [dist_eq_zero] at hd
    subst hd
    simp at hlt

open RockafellarMaxMono in
theorem rmm_le_coe {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (y : E) (r : ℝ) :
    f y ≤ (r : EReal) ↔ f y ≠ ⊤ ∧ (f y).toReal ≤ r := by
  constructor
  · intro h
    have hne : f y ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top r) h
    refine ⟨hne, ?_⟩
    rw [← EReal.coe_le_coe_iff, EReal.coe_toReal hne (hf.1 y)]
    exact h
  · rintro ⟨hne, h⟩
    rw [← EReal.coe_toReal hne (hf.1 y)]
    exact EReal.coe_le_coe_iff.2 h

open RockafellarMaxMono in
theorem rmm_conv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (x y : E) (r s a b : ℝ) (hx : f x ≤ (r : EReal))
    (hy : f y ≤ (s : EReal)) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    f (a • x + b • y) ≤ ((a * r + b * s : ℝ) : EReal) := by
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · subst hb0
    have ha1 : a = 1 := by linarith
    subst ha1
    simpa using hx
  rcases eq_or_lt_of_le (show b ≤ 1 by linarith) with hb1 | hb1
  · subst hb1
    have ha0 : a = 0 := by linarith
    subst ha0
    simpa using hy
  have ha' : a = 1 - b := by linarith
  subst ha'
  obtain ⟨hx1, hx2⟩ := (rmm_le_coe f hf x r).1 hx
  obtain ⟨hy1, hy2⟩ := (rmm_le_coe f hf y s).1 hy
  obtain ⟨p, hp, hpr⟩ : ∃ p : ℝ, f x = p ∧ p ≤ r :=
    ⟨_, (EReal.coe_toReal hx1 (hf.1 x)).symm, hx2⟩
  obtain ⟨q, hq, hqs⟩ : ∃ q : ℝ, f y = q ∧ q ≤ s :=
    ⟨_, (EReal.coe_toReal hy1 (hf.1 y)).symm, hy2⟩
  have hc := hf.2.2 x y b hbpos hb1
  rw [hp, hq, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hc
  refine hc.trans (EReal.coe_le_coe_iff.2 ?_)
  have h1 : 0 ≤ 1 - b := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hpr h1, mul_le_mul_of_nonneg_left hqs hbpos.le]

open RockafellarMaxMono in
theorem rmm_epi_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (ψ : StrongDual ℝ E) (κ : ℝ) :
    Convex ℝ {p : E × ℝ | f p.1 ≤ ((p.2 + ψ p.1 + κ : ℝ) : EReal)} := by
  intro p hp q hq a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hp hq ⊢
  have h := rmm_conv_le f hf p.1 q.1 _ _ a b hp hq ha hb hab
  have heq : (a • p + b • q).2 + ψ (a • p + b • q).1 + κ
      = a * (p.2 + ψ p.1 + κ) + b * (q.2 + ψ q.1 + κ) := by
    simp only [Prod.snd_add, Prod.fst_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_add,
      map_smul]
    linear_combination (-κ) * hab
  rw [heq]
  simpa only [Prod.fst_add, Prod.smul_fst] using h

theorem rmm_epi_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hlsc : LowerSemicontinuous f) :
    IsClosed {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
  have h := hlsc.isClosed_epigraph
  exact h.preimage (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))

open RockafellarMaxMono in
theorem rmm_minorant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    ∃ (a : StrongDual ℝ E) (b : ℝ), ∀ x, f x ≠ ⊤ → a x + b ≤ (f x).toReal := by
  obtain ⟨x1, hx1⟩ := hf.2.1
  have hconv : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    have := rmm_epi_convex f hf 0 0
    simpa using this
  have hnot : ((x1, (f x1).toReal - 1) : E × ℝ) ∉ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    intro h
    simp only [Set.mem_ofPred_eq] at h
    rw [rmm_le_coe f hf] at h
    linarith [h.2]
  obtain ⟨ℓ, u, hℓ0, hℓ⟩ := geometric_hahn_banach_point_closed hconv (rmm_epi_closed f hlsc) hnot
  have hdec : ∀ (y : E) (r : ℝ), ℓ (y, r) = ℓ (y, 0) + r * ℓ (0, 1) := by
    intro y r
    have : ((y, r) : E × ℝ) = (y, 0) + r • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  have hmem : ∀ y, f y ≠ ⊤ →
      ((y, (f y).toReal) : E × ℝ) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    intro y hy
    simp only [Set.mem_ofPred_eq]
    rw [EReal.coe_toReal hy (hf.1 y)]
  have h1 := hℓ _ (hmem x1 hx1)
  rw [hdec] at h1 hℓ0
  have hc : 0 < ℓ (0, 1) := by nlinarith
  refine ⟨-(ℓ (0, 1))⁻¹ • ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ), u / ℓ (0, 1), fun x hx => ?_⟩
  have h2 := hℓ _ (hmem x hx)
  rw [hdec] at h2
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, smul_eq_mul]
  have e : -(ℓ (0, 1))⁻¹ * ℓ (x, 0) + u / ℓ (0, 1) = (u - ℓ (x, 0)) / ℓ (0, 1) := by
    field_simp
    ring
  rw [e, div_le_iff₀ hc]
  linarith

open RockafellarMaxMono in
theorem rmm_subdiff_fin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (x : E) (x' : StrongDual ℝ E) (h : x' ∈ Shared.subdiff f x) :
    f x ≠ ⊤ := by
  intro hx
  obtain ⟨z, hz⟩ := hf.2.1
  have h1 := (show ∀ y, f x + ((x' (y - x) : ℝ) : EReal) ≤ f y from h) z
  rw [hx, EReal.top_add_coe] at h1
  exact hz (top_le_iff.1 h1)

open RockafellarMaxMono in
theorem rmm_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f)
    (x0 : E) (x0' : StrongDual ℝ E)
    (hrel : ∀ x, ∀ u ∈ Shared.subdiff f x, 0 ≤ (u - x0') (x - x0))
    (η : ℝ) (hη : 0 < η) :
    f x0 ≠ ⊤ ∧ ∀ y, f y ≠ ⊤ →
      (f x0).toReal + x0' (y - x0) - η * (2 * ‖y - x0‖ + ‖y - x0‖ ^ 2) ≤ (f y).toReal := by
  classical
  obtain ⟨a, b, hab⟩ := rmm_minorant f hf hlsc
  obtain ⟨x1, hx1⟩ := hf.2.1
  have hfF : ∀ x, f x ≠ ⊤ → f x = (((f x).toReal : ℝ) : EReal) :=
    fun x hx => (EReal.coe_toReal hx (hf.1 x)).symm
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = η / 2 := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨k, hk⟩ : ∃ k : E → ℝ, ∀ x, k x = η * ‖x - x0‖ + η * ‖x - x0‖ ^ 2 :=
    ⟨_, fun _ => rfl⟩
  have hkcont : Continuous k := by
    have : k = fun x => η * ‖x - x0‖ + η * ‖x - x0‖ ^ 2 := funext hk
    rw [this]; fun_prop
  obtain ⟨g, hg⟩ : ∃ g : E → ℝ, ∀ x, g x = (f x).toReal - x0' (x - x0) := ⟨_, fun _ => rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = g x1 + k x1 + 1 := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : E → ℝ, ∀ x, H x = if f x = ⊤ then M else min (g x + k x) M :=
    ⟨_, fun _ => rfl⟩
  -- lower semicontinuity of the truncated function
  have hHlsc : LowerSemicontinuous H := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro c
    by_cases hc : M ≤ c
    · have : H ⁻¹' Set.Iic c = Set.univ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
        rw [hH]
        split_ifs
        · exact hc
        · exact (min_le_right _ _).trans hc
      rw [this]; exact isClosed_univ
    · push Not at hc
      have : H ⁻¹' Set.Iic c = (fun x => ((x, c + x0' (x - x0) - k x) : E × ℝ)) ⁻¹'
          {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_ofPred_eq]
        rw [rmm_le_coe f hf, hH]
        split_ifs with hx
        · simp only [hx, ne_eq, not_true_eq_false, false_and, iff_false, not_le]
          exact hc
        · rw [min_le_iff, hg]
          constructor
          · rintro (h | h)
            · exact ⟨hx, by linarith⟩
            · linarith
          · rintro ⟨-, h⟩
            left; linarith
      rw [this]
      exact (rmm_epi_closed f hlsc).preimage (continuous_id.prodMk
        ((continuous_const.add (x0'.continuous.comp (continuous_id.sub continuous_const))).sub
          hkcont))
  -- lower bound
  have hHbdd : ∀ x, min (a x0 + b - ‖a - x0'‖ ^ 2 / (4 * η)) M ≤ H x := by
    intro x
    rw [hH x]
    split_ifs with hx
    · exact min_le_right _ _
    · refine min_le_min_right _ ?_
      have h1 := hab x hx
      rw [hg, hk]
      have h2 := (a - x0').le_opNorm (x - x0)
      have h3 := neg_abs_le ((a - x0') (x - x0))
      rw [← Real.norm_eq_abs] at h3
      have h4 : (a - x0') (x - x0) = a x - a x0 - x0' (x - x0) := by
        rw [ContinuousLinearMap.sub_apply, map_sub]
      have hβ : ‖a - x0'‖ ^ 2 / (4 * η) * (4 * η) = ‖a - x0'‖ ^ 2 := by
        field_simp
      have ht := norm_nonneg (x - x0)
      have hC := norm_nonneg (a - x0')
      nlinarith [sq_nonneg (2 * η * ‖x - x0‖ - ‖a - x0'‖), mul_nonneg hη.le ht]
  -- Ekeland point
  obtain ⟨x, hxH, hxE⟩ := rmm_ekeland H hHlsc _ hHbdd δ hδpos x1
  have hH1 : H x1 = g x1 + k x1 := by
    rw [hH, if_neg hx1, min_eq_left (by rw [hM]; linarith)]
  rw [hH1] at hxH
  have hxfin : f x ≠ ⊤ := by
    intro hx
    rw [hH, if_pos hx] at hxH
    rw [hM] at hxH
    linarith
  have hHx : H x = g x + k x := by
    have hxH' := hxH
    rw [hH, if_neg hxfin] at hxH' ⊢
    rcases min_choice (g x + k x) M with h | h
    · exact h
    · rw [h] at hxH'; rw [hM] at hxH'; linarith
  have hEk : ∀ y, f y ≠ ⊤ → g x + k x ≤ g y + k y + δ * ‖y - x‖ := by
    intro y hy
    have h1 := hxE y
    rw [hHx, dist_eq_norm] at h1
    have h2 : H y ≤ g y + k y := by rw [hH, if_neg hy]; exact min_le_left _ _
    linarith
  -- the perturbation
  obtain ⟨K, hK⟩ : ∃ K : E → ℝ, ∀ y, K y = k y + δ * ‖y - x‖ := ⟨_, fun _ => rfl⟩
  have hKcont : Continuous K := by
    have : K = fun y => k y + δ * ‖y - x‖ := funext hK
    rw [this]; fun_prop
  have hKx : K x = k x := by rw [hK, sub_self, norm_zero, mul_zero, add_zero]
  have hnc : ∀ (u v : E) (s t : ℝ), 0 ≤ s → 0 ≤ t → ‖s • u + t • v‖ ≤ s * ‖u‖ + t * ‖v‖ := by
    intro u v s t hs ht
    calc ‖s • u + t • v‖ ≤ ‖s • u‖ + ‖t • v‖ := norm_add_le _ _
      _ = s * ‖u‖ + t * ‖v‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
  have hKconv : ∀ (y z : E) (s t : ℝ), 0 ≤ s → 0 ≤ t → s + t = 1 →
      K (s • y + t • z) ≤ s * K y + t * K z := by
    intro y z s t hs ht hst
    have e1 : s • y + t • z - x0 = s • (y - x0) + t • (z - x0) := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hst, one_smul]
    have e2 : s • y + t • z - x = s • (y - x) + t • (z - x) := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hst, one_smul]
    rw [hK, hK, hK, hk, hk, hk, e1, e2]
    have n1 := hnc (y - x0) (z - x0) s t hs ht
    have n2 := hnc (y - x) (z - x) s t hs ht
    have n0 := norm_nonneg (s • (y - x0) + t • (z - x0))
    have hsq : ‖s • (y - x0) + t • (z - x0)‖ ^ 2 ≤ s * ‖y - x0‖ ^ 2 + t * ‖z - x0‖ ^ 2 := by
      have h1 : ‖s • (y - x0) + t • (z - x0)‖ ^ 2 ≤ (s * ‖y - x0‖ + t * ‖z - x0‖) ^ 2 :=
        pow_le_pow_left₀ n0 n1 2
      have h2 : (s * ‖y - x0‖ + t * ‖z - x0‖) ^ 2 ≤ s * ‖y - x0‖ ^ 2 + t * ‖z - x0‖ ^ 2 := by
        have ht' : t = 1 - s := by linarith
        subst ht'
        nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg (‖y - x0‖ - ‖z - x0‖))]
      linarith
    have m1 := mul_le_mul_of_nonneg_left n1 hη.le
    have m2 := mul_le_mul_of_nonneg_left hsq hη.le
    have m3 := mul_le_mul_of_nonneg_left n2 hδpos.le
    nlinarith
  -- the two convex sets
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = g x - x0' x0 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Set (E × ℝ), A = {p : E × ℝ | f p.1 ≤ ((p.2 + x0' p.1 + κ : ℝ) : EReal)} :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Set (E × ℝ), B = {p : E × ℝ | p.2 < -(K p.1 - K x)} := ⟨_, rfl⟩
  have hAconv : Convex ℝ A := hA ▸ rmm_epi_convex f hf x0' κ
  have hBopen : IsOpen B := by
    rw [hB]
    exact isOpen_lt continuous_snd (((hKcont.comp continuous_fst).sub continuous_const).neg)
  have hBconv : Convex ℝ B := by
    rw [hB]
    intro p hp q hq s t hs ht hst
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hp hq ⊢
    have hc := hKconv p.1 q.1 s t hs ht hst
    have hd1 : 0 < -(K p.1 - K x) - p.2 := by linarith
    have hd2 : 0 < -(K q.1 - K x) - q.2 := by linarith
    have hkey : 0 < s * (-(K p.1 - K x) - p.2) + t * (-(K q.1 - K x) - q.2) := by
      rcases eq_or_lt_of_le hs with hs0 | hspos
      · subst hs0
        have ht1 : t = 1 := by linarith
        subst ht1
        linarith
      · have := mul_pos hspos hd1
        have := mul_nonneg ht hd2.le
        linarith
    have hKx' : K x = s * K x + t * K x := by rw [← add_mul, hst, one_mul]
    nlinarith
  have hdisj : Disjoint B A := by
    rw [Set.disjoint_left]
    intro p hpB hpA
    rw [hB] at hpB
    rw [hA] at hpA
    simp only [Set.mem_ofPred_eq] at hpB hpA
    rw [rmm_le_coe f hf] at hpA
    obtain ⟨hp1, hp2⟩ := hpA
    have h1 := hEk p.1 hp1
    rw [hK p.1, hKx] at hpB
    rw [hg p.1, hg x] at h1
    rw [hκ, hg x] at hp2
    simp only [map_sub] at h1 hp2
    linarith
  obtain ⟨ℓ, u, hℓB, hℓA⟩ := geometric_hahn_banach_open hBconv hBopen hAconv hdisj
  have hdec : ∀ (y : E) (r : ℝ), ℓ (y, r) = ℓ (y, 0) + r * ℓ (0, 1) := by
    intro y r
    have : ((y, r) : E × ℝ) = (y, 0) + r • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  have hlin : ∀ y z : E, ℓ (y - z, 0) = ℓ (y, 0) - ℓ (z, 0) := by
    intro y z
    have : ((y - z, (0 : ℝ)) : E × ℝ) = (y, 0) - (z, 0) := by ext <;> simp
    rw [this, map_sub]
  have hxA : ((x, 0) : E × ℝ) ∈ A := by
    rw [hA]
    simp only [Set.mem_ofPred_eq]
    rw [rmm_le_coe f hf]
    refine ⟨hxfin, ?_⟩
    rw [hκ, hg, map_sub]
    linarith
  have hxB : ((x, -1) : E × ℝ) ∈ B := by
    rw [hB]
    simp only [Set.mem_ofPred_eq, sub_self, neg_zero]
    norm_num
  have hu1 := hℓA _ hxA
  have hu2 := hℓB _ hxB
  rw [hdec] at hu2
  have hc : 0 < ℓ (0, 1) := by linarith
  have hu : u = ℓ (x, 0) := by
    by_contra hne
    have hlt : u < ℓ (x, 0) := lt_of_le_of_ne hu1 hne
    have hB' : ((x, (u - ℓ (x, 0)) / ℓ (0, 1)) : E × ℝ) ∈ B := by
      rw [hB]
      simp only [Set.mem_ofPred_eq, sub_self, neg_zero]
      exact div_neg_of_neg_of_pos (by linarith) hc
    have h1 := hℓB _ hB'
    rw [hdec, div_mul_cancel₀ _ hc.ne'] at h1
    linarith
  obtain ⟨ψ, hψ⟩ : ∃ ψ : StrongDual ℝ E, ∀ v, ψ v = -(ℓ (v, 0)) / ℓ (0, 1) :=
    ⟨-(ℓ (0, 1))⁻¹ • ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ), fun v => by
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inl_apply, smul_eq_mul]
      field_simp⟩
  have hS1 : ∀ y, f y ≠ ⊤ → ψ (y - x) ≤ g y - g x := by
    intro y hy
    have hyA : ((y, g y - g x) : E × ℝ) ∈ A := by
      rw [hA]
      simp only [Set.mem_ofPred_eq]
      rw [rmm_le_coe f hf]
      refine ⟨hy, ?_⟩
      rw [hκ, hg y, hg x, map_sub, map_sub]
      linarith
    have h1 := hℓA _ hyA
    rw [hdec] at h1
    rw [hψ, hlin, div_le_iff₀ hc]
    linarith
  have hS2 : ∀ y, -ψ (y - x) ≤ K y - K x := by
    intro y
    by_contra hlt
    push Not at hlt
    have hyB : ((y, ψ (y - x)) : E × ℝ) ∈ B := by
      rw [hB]
      simp only [Set.mem_ofPred_eq]
      linarith
    have h1 := hℓB _ hyB
    rw [hdec, hψ, hlin, div_mul_cancel₀ _ hc.ne'] at h1
    linarith
  have hsub : ψ + x0' ∈ Shared.subdiff f x := by
    show ∀ y, f x + (((ψ + x0') (y - x) : ℝ) : EReal) ≤ f y
    intro y
    by_cases hy : f y = ⊤
    · rw [hy]; exact le_top
    · rw [hfF x hxfin, hfF y hy, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have h1 := hS1 y hy
      rw [hg, hg] at h1
      simp only [ContinuousLinearMap.add_apply, map_sub] at h1 ⊢
      linarith
  have hmono := hrel x _ hsub
  simp only [add_sub_cancel_right] at hmono
  have hx0 : x = x0 := by
    have h := hS2 x0
    have e1 : K x0 = δ * ‖x - x0‖ := by
      rw [hK, hk, sub_self, norm_zero, norm_sub_rev]; ring
    have e2 : K x = η * ‖x - x0‖ + η * ‖x - x0‖ ^ 2 := by rw [hKx, hk]
    rw [e1, e2, map_sub] at h
    rw [map_sub] at hmono
    have ht := norm_nonneg (x - x0)
    have h0 : ‖x - x0‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖x - x0‖ := lt_of_le_of_ne ht (Ne.symm hne)
      have := mul_pos hη hpos
      nlinarith [sq_nonneg ‖x - x0‖]
    rwa [norm_eq_zero, sub_eq_zero] at h0
  refine ⟨hx0 ▸ hxfin, fun y hy => ?_⟩
  have h1 := hS1 y hy
  have h2 := hS2 y
  rw [hK y, hKx, hk, hk] at h2
  rw [hx0] at h1 h2
  rw [hg, hg, sub_self, map_zero, sub_zero] at h1
  rw [sub_self, norm_zero] at h2
  have hw := norm_nonneg (y - x0)
  nlinarith [mul_nonneg hη.le hw]

open RockafellarMaxMono in
theorem rmm_key {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f)
    (x0 : E) (x0' : StrongDual ℝ E)
    (hrel : ∀ x, ∀ u ∈ Shared.subdiff f x, 0 ≤ (u - x0') (x - x0)) :
    x0' ∈ Shared.subdiff f x0 := by
  have hfin := (rmm_step f hf hlsc x0 x0' hrel 1 one_pos).1
  show ∀ y, f x0 + ((x0' (y - x0) : ℝ) : EReal) ≤ f y
  intro y
  by_cases hy : f y = ⊤
  · rw [hy]; exact le_top
  rw [← EReal.coe_toReal hfin (hf.1 x0), ← EReal.coe_toReal hy (hf.1 y), ← EReal.coe_add,
    EReal.coe_le_coe_iff]
  apply le_of_forall_pos_le_add
  intro ε hε
  have hw : 0 ≤ ‖y - x0‖ := norm_nonneg _
  have hden : 0 < 2 * ‖y - x0‖ + ‖y - x0‖ ^ 2 + 1 := by positivity
  have h := (rmm_step f hf hlsc x0 x0' hrel (ε / (2 * ‖y - x0‖ + ‖y - x0‖ ^ 2 + 1))
    (div_pos hε hden)).2 y hy
  have h3 : ε / (2 * ‖y - x0‖ + ‖y - x0‖ ^ 2 + 1) * (2 * ‖y - x0‖ + ‖y - x0‖ ^ 2) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith
  linarith

open RockafellarMaxMono RockafellarMaxMono.Maximality in
theorem bregman_existence_accepted_subdiff_maximal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    IsMaximalMonotone (Shared.subdiff f) := by
  have hmono : IsMonotoneOp (Shared.subdiff f) := by
    intro x₀ x₁ x₀' x₁' h0 h1
    have hfin0 := rmm_subdiff_fin f hf x₀ x₀' h0
    have hfin1 := rmm_subdiff_fin f hf x₁ x₁' h1
    have a0 := (show ∀ y, f x₀ + ((x₀' (y - x₀) : ℝ) : EReal) ≤ f y from h0) x₁
    have a1 := (show ∀ y, f x₁ + ((x₁' (y - x₁) : ℝ) : EReal) ≤ f y from h1) x₀
    rw [← EReal.coe_toReal hfin0 (hf.1 x₀), ← EReal.coe_toReal hfin1 (hf.1 x₁),
      ← EReal.coe_add, EReal.coe_le_coe_iff] at a0 a1
    simp only [ContinuousLinearMap.sub_apply, map_sub] at a0 a1 ⊢
    linarith
  refine ⟨hmono, fun T' hT' hsub x => ?_⟩
  ext x'
  constructor
  · intro hx'
    exact rmm_key f hf hlsc x x' fun z u hu => hT' z x u x' (hsub z hu) hx'
  · intro hx'
    exact hsub x hx'


end

section
set_option autoImplicit false
open InertialFB.IFB ThreeOpSplitting.Convergence
namespace BregmanExistenceCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

lemma positive_coe_mul_ne_bot (a : ℝ) (ha : 0 ≤ a) (v : EReal) (hv : v ≠ ⊥) :
    (a : EReal)*v ≠ ⊥ :=
  (EReal.mul_ne_bot _ _).mpr ⟨Or.inl (EReal.coe_ne_bot _),Or.inr hv,
    Or.inl (EReal.coe_ne_top _),Or.inl (EReal.coe_nonneg.mpr ha)⟩

/-- Bridge the original epigraph predicate to the inspected convex-combination helper. -/
theorem epigraph_proper_convex (f : H → EReal) (hp : IsProperFn f) (hc : IsConvexFn f) :
    RockafellarMaxMono.Shared.ProperConvex f := by
  refine ⟨hp.1,hp.2,?_⟩
  intro x y t ht ht1
  by_cases hx : f x=⊤
  · rw [hx,EReal.coe_mul_top_of_pos (sub_pos.mpr ht1),
      EReal.top_add_of_ne_bot (positive_coe_mul_ne_bot t ht.le (f y) (hp.1 y))]
    exact le_top
  by_cases hy : f y=⊤
  · rw [hy,EReal.coe_mul_top_of_pos ht,
      EReal.add_top_of_ne_bot (positive_coe_mul_ne_bot (1-t) (sub_nonneg.mpr ht1.le) (f x) (hp.1 x))]
    exact le_top
  have hxe : (x,(f x).toReal) ∈ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    change f x ≤ ((f x).toReal : EReal)
    rw [EReal.coe_toReal hx (hp.1 x)]
  have hye : (y,(f y).toReal) ∈ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    change f y ≤ ((f y).toReal : EReal)
    rw [EReal.coe_toReal hy (hp.1 y)]
  have hm := hc hxe hye (a := 1-t) (b := t) (sub_nonneg.mpr ht1.le) ht.le (by ring)
  change f ((1-t) • x+t • y) ≤ (((1-t)*(f x).toReal+t*(f y).toReal : ℝ) : EReal) at hm
  rw [EReal.coe_add,EReal.coe_mul,EReal.coe_mul,
    EReal.coe_toReal hx (hp.1 x),EReal.coe_toReal hy (hp.1 y)] at hm
  exact hm

/-- The original Hilbert subgradient is exactly the inspected dual predicate under Riesz. -/
theorem subgradient_riesz_iff (f : H → EReal)
    (hf : RockafellarMaxMono.Shared.ProperConvex f) (x g : H) :
    IsSubgradient f x g ↔ (InnerProductSpace.toDual ℝ H) g ∈ RockafellarMaxMono.Shared.subdiff f x := by
  constructor
  · intro h
    simpa only [RockafellarMaxMono.Shared.subdiff,Set.mem_setOf_eq,
      InnerProductSpace.toDual_apply_apply] using h.2
  · intro h
    refine ⟨rmm_subdiff_fin f hf x ((InnerProductSpace.toDual ℝ H) g) h,?_⟩
    simpa only [RockafellarMaxMono.Shared.subdiff,Set.mem_setOf_eq,
      InnerProductSpace.toDual_apply_apply] using h

/-- Maximal subdifferentials, with the exact original graph-inclusion and epigraph predicates. -/
theorem original_subdiff_maximal (f : H → EReal) (hp : IsProperFn f)
    (hc : IsConvexFn f) (hl : LowerSemicontinuous f) :
    IsMaximalMonotone (BregmanPPA.Convergence.subdiffOp f) := by
  have hf := epigraph_proper_convex f hp hc
  have hmono : IsMonotoneOp (BregmanPPA.Convergence.subdiffOp f) := by
    intro x y g v hg hv
    have h1 := BregmanPPACodex.subgradient_real_comparison f hp hg hv.1
    have h2 := BregmanPPACodex.subgradient_real_comparison f hp hv hg.1
    simp only [inner_sub_left,inner_sub_right] at h1 h2 ⊢
    simp only [real_inner_comm] at h1 h2 ⊢
    linarith
  refine ⟨hmono,?_⟩
  intro T' hT' hsub
  funext x
  ext g
  constructor
  · intro hg
    have hdual : (InnerProductSpace.toDual ℝ H) g ∈ RockafellarMaxMono.Shared.subdiff f x := by
      apply rmm_key f hf hl x ((InnerProductSpace.toDual ℝ H) g)
      intro z u hu
      have huf : IsSubgradient f z ((InnerProductSpace.toDual ℝ H).symm u) :=
        (subgradient_riesz_iff f hf z _).mpr (by simpa using hu)
      have hpair := hT' z x ((InnerProductSpace.toDual ℝ H).symm u) g (hsub z huf) hg
      have he : (u-(InnerProductSpace.toDual ℝ H) g) (z-x) =
          inner ℝ (z-x) ((InnerProductSpace.toDual ℝ H).symm u-g) := by
        rw [ContinuousLinearMap.sub_apply,← InnerProductSpace.toDual_symm_apply,
          InnerProductSpace.toDual_apply_apply]
        rw [← inner_sub_left,real_inner_comm]
      rw [he]
      exact hpair
    exact (subgradient_riesz_iff f hf x g).mpr hdual
  · intro hg; exact hsub x hg
end BregmanExistenceCodex

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

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.EqMult
namespace BregmanEqMultCodex
variable {n : ℕ}

theorem original_primal_extension_lsc (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (hP : IsEqProgram X f) :
    LowerSemicontinuous (fX X f) := by
  classical
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  by_cases ha : a=⊤
  · subst a; simp
  have he : (fX X f) ⁻¹' Set.Iic a = X ∩ f ⁻¹' Set.Iic a := by
    ext x
    by_cases hx : x ∈ X
    · simp [fX,indicatorE,hx]
    · simp [fX,indicatorE,hx,EReal.add_top_of_ne_bot (hP.ne_bot x),top_le_iff,ha]
  rw [he]
  exact hP.closed.inter (lowerSemicontinuous_iff_isClosed_preimage.mp hP.lsc a)

theorem original_subgradient_graph_limit {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (F : H → EReal) (hp : IsProperFn F)
    (hl : LowerSemicontinuous F) (zseq gseq : ℕ → H) (z g : H)
    (hz : Tendsto zseq atTop (𝓝 z)) (hg : Tendsto gseq atTop (𝓝 g))
    (hs : ∀ k, IsSubgradient F (zseq k) (gseq k)) : IsSubgradient F z g := by
  have hbound (y : H) (hy : F y ≠ ⊤) :
      F z ≤ (((F y).toReal-inner ℝ g (y-z) : ℝ) : EReal) := by
    have ey := EReal.coe_toReal hy (hp.1 y)
    have ht : Tendsto (fun k => (F y).toReal-inner ℝ (gseq k) (y-zseq k)) atTop
        (𝓝 ((F y).toReal-inner ℝ g (y-z))) :=
      tendsto_const_nhds.sub (hg.inner (tendsto_const_nhds.sub hz))
    have he := (continuous_coe_real_ereal.tendsto _).comp ht
    change (z,(((F y).toReal-inner ℝ g (y-z) : ℝ) : EReal)) ∈ {p : H × EReal | F p.1 ≤ p.2}
    apply hl.isClosed_epigraph.mem_of_tendsto (hz.prodMk_nhds he)
    apply Eventually.of_forall
    intro k
    have hi := (hs k).2 y
    have ek := EReal.coe_toReal (hs k).1 (hp.1 (zseq k))
    rw [← ek,← ey,← EReal.coe_add] at hi
    have hir := EReal.coe_le_coe_iff.mp hi
    change F (zseq k) ≤ (((F y).toReal-inner ℝ (gseq k) (y-zseq k) : ℝ) : EReal)
    rw [← ek]
    apply EReal.coe_le_coe_iff.mpr
    linarith
  have hzt : F z ≠ ⊤ := by
    obtain ⟨y,hy⟩ := hp.2
    exact ne_of_lt ((hbound y hy).trans_lt (EReal.coe_lt_top _))
  refine ⟨hzt,?_⟩
  intro y
  by_cases hy : F y=⊤
  · rw [hy]; exact le_top
  have hb := hbound y hy
  have ez := EReal.coe_toReal hzt (hp.1 z)
  have ey := EReal.coe_toReal hy (hp.1 y)
  rw [← ez] at hb
  have hbr := EReal.coe_le_coe_iff.mp hb
  rw [← ez,← ey,← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  linarith
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open Filter Topology BregmanPPA.Convergence BregmanPPA.EqMult
namespace BregmanEqMultCodex
variable {n m : ℕ}

theorem original_limit_feasibility
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (hP : IsEqProgram X f)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (hh : IsBregmanFunction Set.univ h)
    (him : Function.Surjective (gradient h))
    (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (p : ℕ → EuclideanSpace ℝ (Fin m))
    (hrun : IsEqMultRun A b X f h c x p) (pstar : EuclideanSpace ℝ (Fin m))
    (hp : Tendsto p atTop (𝓝 pstar)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (x' : EuclideanSpace ℝ (Fin n)) (hx' : Tendsto (x ∘ φ) atTop (𝓝 x')) :
    Tendsto (fun k => A (x k)) atTop (𝓝 b) ∧ A x'=b ∧ x' ∈ X := by
  have hA := original_asymptotic_feasibility A b X f h hh him c hc hcinf x p hrun pstar hp
  have hb := hA.comp hφ.tendsto_atTop
  have ha := A.continuous.continuousAt.tendsto.comp hx'
  have he : A x'=b := tendsto_nhds_unique ha hb
  have hX : ∀ᶠ k in atTop, x k ∈ X := by
    rw [eventually_atTop]
    refine ⟨1,?_⟩
    intro k hk
    cases k with
    | zero => omega
    | succ j => exact (hrun j).1
  exact ⟨hA,he,hP.closed.mem_of_tendsto hx' (hφ.tendsto_atTop.eventually hX)⟩
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.Convergence BregmanPPA.EqMult
namespace BregmanEqMultCodex
variable {n m : ℕ}

theorem original_limit_points
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (hP : IsEqProgram X f)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (hh : IsBregmanFunction Set.univ h)
    (him : Function.Surjective (gradient h)) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (p : ℕ → EuclideanSpace ℝ (Fin m))
    (hrun : IsEqMultRun A b X f h c x p) (pstar : EuclideanSpace ℝ (Fin m))
    (hp : Tendsto p atTop (𝓝 pstar)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (x' : EuclideanSpace ℝ (Fin n)) (hx' : Tendsto (x ∘ φ) atTop (𝓝 x')) :
    Tendsto (fun k => A (x k)) atTop (𝓝 b) ∧ A x'=b ∧
    -(ContinuousLinearMap.adjoint A pstar) ∈ subdiffOp (fX X f) x' ∧
    IsSolution7 A b X f x' := by
  have hf := original_limit_feasibility A b X f hP h hh him c hc hcinf x p hrun pstar hp φ hφ x' hx'
  have hshift := tendsto_add_atTop_nat 1
  have hz : Tendsto (fun k => x (φ (k+1))) atTop (𝓝 x') := hx'.comp hshift
  have hg : Tendsto (fun k => -(ContinuousLinearMap.adjoint A (p (φ (k+1))))) atTop
      (𝓝 (-(ContinuousLinearMap.adjoint A pstar))) :=
    (ContinuousLinearMap.adjoint A).continuous.neg.continuousAt.tendsto.comp
      (hp.comp (hφ.tendsto_atTop.comp hshift))
  have hgraphs (k : ℕ) : IsSubgradient (fX X f) (x (φ (k+1)))
      (-(ContinuousLinearMap.adjoint A (p (φ (k+1))))) := by
    have hpos : 0 < φ (k+1) := lt_of_lt_of_le (Nat.zero_lt_succ k) (hφ.id_le (k+1))
    have he : φ (k+1)-1+1=φ (k+1) := by omega
    simpa only [he,subdiffOp,Set.mem_setOf_eq] using
      original_primal_subgradient A b X f hP h hh him c hc x p hrun (φ (k+1)-1)
  have hs := original_subgradient_graph_limit (fX X f) (original_primal_extension_proper X f hP)
    (original_primal_extension_lsc X f hP) _ _ x' (-(ContinuousLinearMap.adjoint A pstar)) hz hg hgraphs
  refine ⟨hf.1,hf.2.1,hs,hf.2.2,hf.2.1,?_⟩
  intro y hy hAy
  have hb := hs.2 y
  have he : inner ℝ (-(ContinuousLinearMap.adjoint A pstar)) (y-x')=0 := by
    simp only [inner_neg_left,ContinuousLinearMap.adjoint_inner_left,map_sub,
      hAy,hf.2.1,sub_self,inner_zero_right,neg_zero]
  simpa only [fX,indicatorE,if_pos hf.2.2,if_pos hy,add_zero,he,EReal.coe_zero] using hb
end BregmanEqMultCodex

end

set_option autoImplicit false
open InertialFB.IFB BregmanPPA.EqMult Filter Topology
theorem solution {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hP : IsEqProgram X f) (hd : ∃ p, dualEq A b X f p ≠ ⊥)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (hh : BregmanPPA.Convergence.IsBregmanFunction Set.univ h)
    (him : Function.Surjective (gradient h))
    (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (hcinf : ∃ ε > 0, ∀ k, ε ≤ c k)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (p : ℕ → EuclideanSpace ℝ (Fin m))
    (hrun : IsEqMultRun A b X f h c x p) :
    ((∃ q, IsOptimalMultiplier A b X f q) →
      (∃ pstar, IsOptimalMultiplier A b X f pstar ∧ Tendsto p atTop (𝓝 pstar)) ∧
      ∀ (φ : ℕ → ℕ) (x' : EuclideanSpace ℝ (Fin n)), StrictMono φ →
        Tendsto (x ∘ φ) atTop (𝓝 x') → IsSolution7 A b X f x') ∧
    ((¬ ∃ q, IsOptimalMultiplier A b X f q) → ¬ Bornology.IsBounded (Set.range p)) := by
  let F := negDual A b X f
  let T := BregmanPPA.Convergence.subdiffOp F
  have hproper : IsProperFn F := BregmanEqMultCodex.original_negdual_proper A b X f hP hd
  have hconvex : IsConvexFn F := BregmanEqMultCodex.original_negdual_convex A b X f hP
  have hlsc : LowerSemicontinuous F := BregmanEqMultCodex.original_negdual_lsc A b X f hP
  have hmax : ThreeOpSplitting.Convergence.IsMaximalMonotone T :=
    BregmanExistenceCodex.original_subdiff_maximal F hproper hconvex hlsc
  have hdom : ThreeOpSplitting.Convergence.dom T ⊆ closure (Set.univ : Set (EuclideanSpace ℝ (Fin m))) := by simp
  have hclosure : closure (ThreeOpSplitting.Convergence.dom T) ⊆ (Set.univ : Set (EuclideanSpace ℝ (Fin m))) := Set.subset_univ _
  have hr : BregmanPPA.Convergence.IsBregmanPPARun Set.univ h T c p :=
    BregmanEqMultCodex.original_dual_ppa_run A b X f hP h hh him c hc x p hrun
  have hg := BregmanPPACodex.theorem1 T Set.univ h c p hmax hh hdom hc hcinf hr (Or.inl hclosure)
  have he (q : EuclideanSpace ℝ (Fin m)) : q ∈ ThreeOpSplitting.Convergence.zer T ↔ IsOptimalMultiplier A b X f q :=
    BregmanEqMultCodex.original_negdual_zero_iff A b X f hd q
  constructor
  · intro hex
    obtain ⟨q,hq⟩ := hex
    obtain ⟨pstar,hzero,hp⟩ := hg.1 ⟨q,(he q).mpr hq⟩
    have hpstar := (he pstar).mp hzero
    refine ⟨⟨pstar,hpstar,hp⟩,?_⟩
    intro φ x' hφ hx'
    exact (BregmanEqMultCodex.original_limit_points A b X f hP h hh him c hc hcinf x p hrun pstar hp φ hφ x' hx').2.2.2
  · intro hno
    apply hg.2 _ hclosure
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    exact hno ⟨q,(he q).mp hq⟩



#print axioms solution
