-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.lemmaS_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:29.057731+00:00
-- url     : https://prove2.me/submissions/8beed079-4e29-49a9-bbed-69150948c52b

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffEvenDerivativeEqZero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmS_cc_be
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_constantCoeff_evenDerivative_eq_zero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_constantCoeff_oddDerivative_eq_zero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmS_diff
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPowerSeries
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (hGW : GenLogWeight.{u, 0}) (hGI : GenLogInverse.{u, 0}) (hB : LogBridges.{u})
    (hSW : SubstWt.{u, 0, 0}) (hX : ExpDeInv.{u}) (hQ : Quant.{u}) (hLS : LogStep.{u, 0})
    (hBE : BinomExtract.{u}) : LemmaS.{u} := by
  intro K _ _ _ l d _ hl hlo hd hde hpi K0 hK0 ζ hζ be hBh
  obtain ⟨hK, htor, hlow, ⟨hEi1, hEc1⟩, ⟨hEi2, hEc2⟩⟩ := hBh
  have hbe0 := asmS_cc_be hlow
  have hX' := hX K l d hl hd hde K0 ζ hζ be hK htor hbe0
  obtain ⟨hK1, hc1⟩ := hX' (de1 be) (by simp)
  obtain ⟨hK2, hc2⟩ := hX' (de2 be) (by simp)
  have w1 := asmS_diff hGW hGI hB hSW hQ hLS hl hd hde hpi hK0 (de1 be) (constantCoeff_evenDerivative_eq_zero hbe0) hK1 hc1
    hEi1 hEc1
  have w2 := asmS_diff hGW hGI hB hSW hQ hLS hl hd hde hpi hK0 (de2 be) (constantCoeff_oddDerivative_eq_zero hbe0) hK2 hc2
    hEi2 hEc2
  exact hBE K l d hl hlo hd hde hpi ζ hζ be htor hlow w1 w2
end Formalism.DworkPowerSeriesWeights
