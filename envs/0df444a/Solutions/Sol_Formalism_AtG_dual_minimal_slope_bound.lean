-- Prove2me | solution 1 for Formalism.AtG.dual_minimal_slope_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:50:26.531908+00:00
-- url     : https://prove2.me/submissions/b75f1ba2-84e6-489e-96a8-5edd2c958689

import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ScaledCoordinatesValuationLemma
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_SumValuationNat
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_ValAdd
import Definitions.Def_Formalism_TowerValuationBounds_TowerValuationProofs_SumAdditiveCharacterEqZero
import Definitions.Def_Lemmata_PlaneOverMembership_PlOverOfMem
import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ExponentGridsProofs_FrameHeightOfDualSlope
import Theorems.Thm_Formalism_AtG_ne_bot_of_span_top
import Theorems.Thm_Formalism_HN_dual_polygon_identity
import Theorems.Thm_Formalism_HN_size_maximal_slope


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw PlOver meanLog)
open Formalism.PairingDivisionLocalBalance (Pl wt HtLe meanInf)
open Formalism.HN (muMaxDef muMinDef htMap dualLat dualFrame)
noncomputable section
open Formalism Formalism.AtG
namespace Formalism.AtG
theorem _root_.solution : DualLatticeMinimalSlope := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ _ b X hX A hA hspan
  have hXd : ∀ v, IsUnit (dualFrame X v).det := by
    intro v
    simp only [Formalism.HN.dualFrame]
    rw [Matrix.isUnit_nonsing_inv_det_iff, Matrix.det_transpose]
    exact hX v
  obtain ⟨hdfg, hdspan, -, -, -, hlarge, -⟩ := Formalism.HN.dual_polygon_identity K V ι b X hX A hA hspan
  have hA0 : A ≠ ⊥ := ne_bot_of_span_top b A hspan
  have hd0 : dualLat A ≠ ⊥ := ne_bot_of_span_top b.dualBasis (dualLat A) hdspan
  obtain ⟨-, -, -, hl, -, -⟩ := Formalism.HN.size_maximal_slope K V ι b X hX A hA hA0
  obtain ⟨-, -, -, -, hL, -⟩ :=
    Formalism.HN.size_maximal_slope K (Module.Dual K V) ι b.dualBasis (dualFrame X) hXd (dualLat A) hdfg hd0
  rw [hl, hL, ← Real.exp_neg] at hlarge
  have h := Real.exp_injective hlarge
  unfold Formalism.HN.muMinDef Formalism.HN.muMaxDef
  have e : Formalism.HN.logDisc K / (2 * (finrank ℚ K : ℝ)) = Formalism.HN.logDisc K / (finrank ℚ K : ℝ) / 2 := by
    ring
  rw [e] at h
  linarith
end Formalism.AtG
