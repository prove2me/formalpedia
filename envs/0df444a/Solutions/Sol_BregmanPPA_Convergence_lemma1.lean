-- Prove2me | solution 1 for BregmanPPA.Convergence.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T14:05:13.303785+00:00
-- url     : https://prove2.me/submissions/ee1cf74f-26c1-478d-891e-bde1b081b671

import Definitions.Def_BregmanPPA_Convergence_Model
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

/-- The three-point inequality follows directly from the original monotone graph. -/
theorem three_point (T : H → Set H) (h : H → ℝ) (hT : IsMonotoneOp T)
    (z y p : H) (hz : z ∈ zer T) (hp : gradient h y-gradient h p ∈ T p) :
    bregmanD h z p ≤ bregmanD h z y-bregmanD h p y := by
  have hm := hT p z (gradient h y-gradient h p) 0 hp hz
  rw [sub_zero,inner_sub_right] at hm
  have hc1 : inner ℝ (p-z) (gradient h y) = inner ℝ (gradient h y) (p-z) :=
    real_inner_comm _ _
  have hc2 : inner ℝ (p-z) (gradient h p) = inner ℝ (gradient h p) (p-z) :=
    real_inner_comm _ _
  rw [hc1,hc2,← neg_sub z p,inner_neg_right,inner_neg_right] at hm
  have he : z-y = (z-p)+(p-y) := by abel
  have hi : inner ℝ (gradient h y) (z-y) =
      inner ℝ (gradient h y) (z-p)+inner ℝ (gradient h y) (p-y) := by
    rw [he,inner_add_right]
  dsimp [bregmanD]
  linarith
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem gradient_strict_support (S : Set H) (h : H → ℝ) (hh : IsBregmanFunction S h)
    {y z : H} (hy : y ∈ S) (hz : z ∈ closure S) (hneq : y ≠ z) :
    inner ℝ (gradient h y) (z-y) < h z-h y := by
  let m : H := (1/2 : ℝ) • y+(1/2 : ℝ) • z
  have hm : m ∈ closure S := hh.strictConvexOn.1 (subset_closure hy) hz
    (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num)
  have hs := gradient_support S h hh hy hm
  have hc := hh.strictConvexOn.2 (subset_closure hy) hz hneq
    (by norm_num : 0 < (1/2 : ℝ)) (by norm_num : 0 < (1/2 : ℝ)) (by norm_num)
  have he : m-y = (1/2 : ℝ) • (z-y) := by dsimp [m]; module
  rw [he,inner_smul_right] at hs
  change h m < (1/2 : ℝ)*h y+(1/2 : ℝ)*h z at hc
  nlinarith

theorem resolvent_unique (T : H → Set H) (S : Set H) (h : H → ℝ)
    (hT : IsMonotoneOp T) (hh : IsBregmanFunction S h) (y p q : H)
    (hp : p ∈ S) (hq : q ∈ S)
    (hip : gradient h y-gradient h p ∈ T p)
    (hiq : gradient h y-gradient h q ∈ T q) : p=q := by
  by_contra hneq
  have hpq := gradient_strict_support S h hh hp (subset_closure hq) hneq
  have hqp := gradient_strict_support S h hh hq (subset_closure hp) (fun he => hneq he.symm)
  have hm := hT p q _ _ hip hiq
  have he : (gradient h y-gradient h p)-(gradient h y-gradient h q) =
      gradient h q-gradient h p := by abel
  rw [he,inner_sub_right] at hm
  have hc1 : inner ℝ (p-q) (gradient h q) = inner ℝ (gradient h q) (p-q) :=
    real_inner_comm _ _
  have hc2 : inner ℝ (p-q) (gradient h p) = inner ℝ (gradient h p) (p-q) :=
    real_inner_comm _ _
  have hn : inner ℝ (gradient h p) (q-p) = -inner ℝ (gradient h p) (p-q) := by
    rw [← neg_sub p q,inner_neg_right]
  rw [hc1,hc2] at hm
  rw [hn] at hpq
  linarith

theorem lemma1 (T : H → Set H) (S : Set H) (h : H → ℝ)
    (hT : IsMonotoneOp T) (hh : IsBregmanFunction S h) :
    (∀ (y p q : H), y ∈ S → p ∈ S → q ∈ S →
      gradient h y-gradient h p ∈ T p → gradient h y-gradient h q ∈ T q → p=q) ∧
    (∀ (z y p : H), z ∈ zer T → z ∈ closure S → y ∈ S → p ∈ S →
      gradient h y-gradient h p ∈ T p →
      bregmanD h z p ≤ bregmanD h z y-bregmanD h p y) := by
  constructor
  · intro y p q _ hp hq hip hiq
    exact resolvent_unique T S h hT hh y p q hp hq hip hiq
  · intro z y p hz _ _ _ hip
    exact three_point T h hT z y p hz hip
end BregmanPPACodex

end

set_option autoImplicit false
open BregmanPPA.Convergence ThreeOpSplitting.Convergence InertialFB.IFB Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Lemma 1: uniqueness of the Bregman resolvent and its three-point inequality. -/
theorem solution (T : H → Set H) (S : Set H) (h : H → ℝ)
    (hT : IsMonotoneOp T) (hh : IsBregmanFunction S h) :
    (∀ (y p q : H), y ∈ S → p ∈ S → q ∈ S →
      gradient h y - gradient h p ∈ T p →
      gradient h y - gradient h q ∈ T q → p = q) ∧
    (∀ (z y p : H), z ∈ zer T → z ∈ closure S → y ∈ S → p ∈ S →
      gradient h y - gradient h p ∈ T p →
      bregmanD h z p ≤ bregmanD h z y - bregmanD h p y) := by
  exact BregmanPPACodex.lemma1 T S h hT hh



#print axioms solution
