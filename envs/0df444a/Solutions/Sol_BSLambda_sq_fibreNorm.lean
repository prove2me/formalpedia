-- Prove2me | solution 1 for BSLambda.sq_fibreNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:20:30.046301+00:00
-- url     : https://prove2.me/submissions/5c86e369-9e2c-44f5-b0c5-85cad96b4419

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (g : Input V → Bool) (ψ : Input (W × V) → ℝ) (b : Input W) :
    fibreNorm g ψ b ^ 2 = ∑ x : Input (W × V), (if topBits g x = b then ψ x else 0) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
end BSLambda
