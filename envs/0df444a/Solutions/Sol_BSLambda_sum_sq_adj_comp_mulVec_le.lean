-- Prove2me | solution 1 for BSLambda.sum_sq_adj_comp_mulVec_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:43:18.043767+00:00
-- url     : https://prove2.me/submissions/2ec3d4ea-d390-4e18-8efa-feb716e76113

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Theorems.Thm_BSLambda_sum_sq_fibres
public import Theorems.Thm_BSLambda_sum_sq_fibreNorm
public import Theorems.Thm_BSLambda_sum_sq_fibre_adj_comp_mulVec_le
public import Theorems.Thm_BSLambda_sum_sq_adj_mulVec_le


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input W → Bool) (g : Input V → Bool)
    (ψ : Input (W × V) → ℝ) :
    ∑ x, (adj (comp f g) *ᵥ ψ) x ^ 2 ≤ (lam f * lam g) ^ 2 * ∑ x, ψ x ^ 2 :=
  calc ∑ x, (adj (comp f g) *ᵥ ψ) x ^ 2
      = ∑ b : Input W, ∑ x : Input (W × V),
          (if topBits g x = b then (adj (comp f g) *ᵥ ψ) x else 0) ^ 2 :=
        (sum_sq_fibres g (adj (comp f g) *ᵥ ψ)).symm
    _ ≤ ∑ b : Input W, lam g ^ 2 * ((adj f *ᵥ fibreNorm g ψ) b) ^ 2 :=
        Finset.sum_le_sum fun b _ ↦ sum_sq_fibre_adj_comp_mulVec_le f g ψ b
    _ = lam g ^ 2 * ∑ b : Input W, ((adj f *ᵥ fibreNorm g ψ) b) ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ lam g ^ 2 * (lam f ^ 2 * ∑ b : Input W, fibreNorm g ψ b ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_sq_adj_mulVec_le f (fibreNorm g ψ)) (sq_nonneg _)
    _ = (lam f * lam g) ^ 2 * ∑ x, ψ x ^ 2 := by
        rw [sum_sq_fibreNorm]
        ring
end BSLambda
