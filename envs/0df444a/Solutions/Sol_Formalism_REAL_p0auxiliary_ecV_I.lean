-- Prove2me | solution 1 for Formalism.REAL.p0auxiliary_ecV_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:37:41.833608+00:00
-- url     : https://prove2.me/submissions/7af7ece3-e62c-4a04-845b-b50cb3e5231d

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_LieOperatorConjHolds
import Theorems.Thm_Formalism_REAL_p0auxiliary_rdV_neg
import Theorems.Thm_Formalism_REAL_p0auxiliary_cpart1_I
import Theorems.Thm_Formalism_REAL_p0auxiliary_cpart2_I

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable (hl : RdLinV) {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : Matrix (Fin n) (Fin n) ℂ → E} {g : Matrix (Fin n) (Fin n) ℂ}
include hl
namespace Formalism.REAL
theorem _root_.solution (Z : Matrix (Fin n) (Fin n) ℂ) :
    EcV ε (Complex.I • Z) f g = Complex.I • EcV ε Z f g := by
  simp only [EcV]
  rw [p0auxiliary_cpart1_I, p0auxiliary_cpart2_I, p0auxiliary_rdV_neg, smul_add, smul_smul, Complex.I_mul_I,
    neg_one_smul]
  abel
end Formalism.REAL
