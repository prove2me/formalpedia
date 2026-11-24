-- Prove2me | solution 1 for Formalism.REAL.p0auxiliary_cpart2_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:19:02.073808+00:00
-- url     : https://prove2.me/submissions/51e668fd-f6a3-4cf5-9ba3-45592a89e4e7

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_LieOperatorConjHolds
import Theorems.Thm_Formalism_REAL_p0auxiliary_half_I
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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε (Complex.I • Z) = cpart1 ε Z := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have k1 : (-(1 / 2) * Complex.I) * Complex.I = 1 / 2 := by
    linear_combination (-(1 / 2) : ℂ) * Complex.I_sq
  have k2 : (-(1 / 2) * Complex.I) * -Complex.I = -(1 / 2) := by
    linear_combination ((1 / 2) : ℂ) * Complex.I_sq
  rw [cpart2, cpart1, Jm_mul_conjTranspose_smul_mul_Jm, hI, p0auxiliary_half_I, smul_add, smul_smul, smul_smul, k1, k2]
  module
end Formalism.REAL
