-- Prove2me | solution 1 for BSLambda.sum_sq_fibreNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:37:41.184143+00:00
-- url     : https://prove2.me/submissions/e4c5f9f4-8a66-4651-be0d-3d1d470ff2cc

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Theorems.Thm_BSLambda_sum_sq_fibres
public import Theorems.Thm_BSLambda_sq_fibreNorm

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (g : Input V → Bool) (ψ : Input (W × V) → ℝ) :
    ∑ b : Input W, fibreNorm g ψ b ^ 2 = ∑ x : Input (W × V), ψ x ^ 2 :=
  (Finset.sum_congr rfl fun b _ ↦ sq_fibreNorm g ψ b).trans (sum_sq_fibres g ψ)
end BSLambda
