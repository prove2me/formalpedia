-- Prove2me | solution 1 for Formalism.AtG.grid_function_of_lemma_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:13:25.600071+00:00
-- url     : https://prove2.me/submissions/acfb85c1-aed7-4531-87db-5c75a985ccf4

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
import Theorems.Thm_P2M_Formalism_AtG_lw_nonneg__115b3852fc51
import Theorems.Thm_Formalism_DivisionValues_kappa_normalise
import Theorems.Thm_Formalism_DivisionValues_lattice_fg_ne_bot


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
theorem _root_.solution (hA : SlopeInequalityDenominators) : LargestSlopeLatticeFrames := by
  intro K W κ _ _ _ _ _ _ _ _ _ _ D hD XE kap b' X' hXE hkap hX' R M Ψ T a r dF EM hInf Gr BF
    hR hM hM0 hΨ hincl ha hEM hh hGr hBF
  obtain ⟨hfg, hne⟩ := Formalism.DivisionValues.lattice_fg_ne_bot hD R hR
  obtain ⟨hu, -, -, -, h5⟩ := Formalism.DivisionValues.kappa_normalise K D hD XE hXE kap hkap
  obtain ⟨-, e2, -⟩ := h5 R hR
  have h := hA K (Fin D → K) (Fin D) W κ (Pi.basisFun K (Fin D))
    (Formalism.DivisionValues.scaleFrame (fun v => (kap v)⁻¹) XE) b' X' hu hX' Ψ R M T a hfg hne hM hM0 hΨ hincl
  have hs : ∑ w ∈ T, lw w * (a w : ℝ) ≤ Gr + BF := by
    calc ∑ w ∈ T, lw w * (a w : ℝ)
        ≤ ∑ w ∈ T, (lw w * (vw w (r w) : ℝ) + lw w * dF w) := by
          refine Finset.sum_le_sum fun w hw => ?_
          have h1 := ha w hw
          have hl : 0 ≤ lw w := lw_nonneg' w
          nlinarith
      _ = ∑ w ∈ T, lw w * (vw w (r w) : ℝ) + ∑ w ∈ T, lw w * dF w := Finset.sum_add_distrib
      _ ≤ Gr + BF := add_le_add hGr hBF
  rw [e2]
  linarith
end Formalism.AtG
