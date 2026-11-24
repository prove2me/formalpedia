-- Prove2me | solution 1 for Formalism.REAL.imaginary_part_single_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:37:40.303901+00:00
-- url     : https://prove2.me/submissions/f0a44113-dfad-44cf-b792-010b9cf50b64

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasComm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnGroupSum
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IntegrableComplexContinuousBoundedSupport
import Theorems.Thm_Formalism_REAL_signature_conj_single
import Theorems.Thm_Formalism_REAL_signature_sign_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ENNReal
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
namespace Formalism.REAL
theorem _root_.solution (ε : Fin n → Bool) (a b : Fin n) :
    cpart2 ε (Matrix.single b a 1) = ((sgn ε a b : ℝ) : ℂ) • cpart2 ε (Matrix.single a b 1) := by
  have e1 := signature_conj_single ε a b
  have e2 := signature_conj_single ε b a
  rw [signature_sign_symm] at e2
  unfold cpart2
  rw [e1, e2]
  unfold sgn
  split_ifs
  · simp only [Complex.ofReal_one, one_smul]; module
  · simp only [Complex.ofReal_one, Complex.ofReal_neg, one_smul, neg_smul]; module
end Formalism.REAL
