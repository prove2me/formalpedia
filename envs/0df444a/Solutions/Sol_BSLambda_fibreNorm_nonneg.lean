-- Prove2me | solution 1 for BSLambda.fibreNorm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:37:35.701284+00:00
-- url     : https://prove2.me/submissions/3fc91266-8fa2-4451-8b57-fd693d568ab2

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
    0 ≤ fibreNorm g ψ b :=
  Real.sqrt_nonneg _
end BSLambda
