-- Prove2me | solution 1 for BregmanPPA.Convergence.step1
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T14:17:35.818098+00:00
-- url     : https://prove2.me/submissions/c086ab26-4de4-4535-99c3-e404979bd484

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

set_option autoImplicit false
open BregmanPPA.Convergence ThreeOpSplitting.Convergence InertialFB.IFB Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Theorem 1, proof, Step 1: decreasing Bregman distance and bounded iterates. -/
theorem solution (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hx : IsBregmanPPARun S h T c x) (z : H) (hz : z ∈ zer T) :
    (∀ k, bregmanD h z (x (k + 1)) ≤
      bregmanD h z (x k) - bregmanD h (x (k + 1)) (x k)) ∧
    (∃ δ : ℝ, 0 ≤ δ ∧ Tendsto (fun k => bregmanD h z (x k)) atTop (𝓝 δ)) ∧
    Bornology.IsBounded (Set.range x) := by
  exact BregmanPPACodex.step1 T S h c x hT hh hdom hc hcinf hx z hz



#print axioms solution
