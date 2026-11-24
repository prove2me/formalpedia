-- Prove2me | solution 1 for Formalism.REAL.invInvariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:18:13.019505+00:00
-- url     : https://prove2.me/submissions/51eaaea7-4248-48e9-a40f-3b0651d07396

import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_RightDerivativeZeroOutsideSupport
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Theorems.Thm_Formalism_REAL_indefinite_unitary_unimodular


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : InvInvariant := by
  intro n ε
  have hR := indefinite_unitary_unimodular n ε
  haveI : (muG ε).IsMulRightInvariant := ⟨hR⟩
  show (muG ε).inv = muG ε
  have key : (muG ε).inv =
      MeasureTheory.Measure.haarScalarFactor (muG ε).inv (muG ε) • muG ε := by
    exact MeasureTheory.Measure.isMulLeftInvariant_eq_smul _ _
  generalize MeasureTheory.Measure.haarScalarFactor (muG ε).inv (muG ε) = c at key
  have h2 : muG ε = (c * c) • muG ε := by
    calc muG ε = (muG ε).inv.inv := (MeasureTheory.Measure.inv_inv _).symm
      _ = (c • muG ε).inv := by rw [← key]
      _ = c • (muG ε).inv := MeasureTheory.Measure.map_smul _ _ _
      _ = (c * c) • muG ε := by rw [key, smul_smul]
  have hc1 : c = 1 := by
    obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : ↥(UJ ε))
    have hpos : muG ε K ≠ 0 := (MeasureTheory.Measure.measure_pos_of_mem_nhds (muG ε) hK1).ne'
    have hfin : muG ε K ≠ ⊤ := hKc.measure_lt_top.ne
    have hK : muG ε K = ((c * c : NNReal) : ENNReal) * muG ε K := by
      conv_lhs => rw [h2]
      rfl
    have h3 : ((c * c : NNReal) : ENNReal) = 1 := by
      have h4 : ((c * c : NNReal) : ENNReal) * muG ε K = 1 * muG ε K := by
        rw [one_mul]
        exact hK.symm
      exact (ENNReal.mul_left_inj hpos hfin).mp h4
    have h5 : (c : ℝ) * c = 1 := by exact_mod_cast h3
    have h6 : (0 : ℝ) ≤ c := c.2
    apply NNReal.eq
    push_cast
    nlinarith
  rw [key, hc1, one_smul]
end Formalism.REAL
