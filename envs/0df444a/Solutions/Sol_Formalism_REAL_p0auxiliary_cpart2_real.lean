-- Prove2me | solution 1 for Formalism.REAL.p0auxiliary_cpart2_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:01:37.411783+00:00
-- url     : https://prove2.me/submissions/5e510675-88bf-40c9-b892-85129936333b

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_LieOperatorConjHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
private lemma Jm_mul_conjTranspose_smul_mul_Jm {n : ℕ} (ε : Fin n → Bool) (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (c • Z)ᴴ * Jm ε = star c • (Jm ε * Zᴴ * Jm ε) := by
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
section EcV
variable (hl : RdLinV) {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : Matrix (Fin n) (Fin n) ℂ → E} {g : Matrix (Fin n) (Fin n) ℂ}
include hl
end EcV
end Formalism.REAL
end
end

set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (x : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε ((x : ℂ) • Z) = (x : ℂ) • cpart2 ε Z := by
  have hx : star (x : ℂ) = x := Complex.conj_ofReal x
  rw [cpart2, cpart2, Jm_mul_conjTranspose_smul_mul_Jm, hx, ← smul_add, smul_comm]
end Formalism.REAL
