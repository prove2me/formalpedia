-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A.t_NormOfLemmas
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:01.870855+00:00
-- url     : https://prove2.me/submissions/1df0b725-76b2-4a55-9dff-5dac8c2cad9f

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_A_book_constants_pos_of_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A
theorem _root_.solution : NormOfLemmas := by
  intro hJC hLP hCo P _ B hin
  obtain ⟨hPos, hJac, hNu, hInf, hVol, hLev, hMas, hCol, hOrd, hTyp, hInd⟩ := hin
  obtain ⟨hGam, hμK, hμKpp, hμSpp, hμSpp', hMM, hU, hc0, hc0', htt, hAA, hD⟩ := book_constants_pos_of_pos B hPos
  have hJ := hJC P B hPos hJac hNu
  have hL := (hLP P B hPos hOrd hTyp hInd).1
  obtain ⟨-, -, hC1, -, -, hC2⟩ := hCo P B hPos hVol hLev hMas hCol
  have hPos' := hPos
  obtain ⟨hp, hμKo, hμSo, hμSo', hMo, hU00o, hμH, hμH', hμHpp, hμHpp', hμN, hμN', hvolZZ, hvolPP, hal,
    hvolG, hvolHa, hvolHa', hvolNa, hvolNa', hvolB, hvolH, hvolH', hvolN, hvolN', hCoo, hdeg, hdimπ,
    hdimπ', hρ0, hρ0', hd, hd', hn0c, hsup, hδ⟩ := hPos'
  have hV := hVol.1
  unfold S3.MassData.InInfinity at hInf

  have key : B.Gam1 * B.AA * ((B.c0 * B.c0')⁻¹ * (B.volZZ / B.unitLevelVolume * B.Coo⁻¹)) * (1 / B.deg)
      = B.d * B.d' / B.Dstar := by
    have e1 : B.Gam1 * B.AA * ((B.c0 * B.c0')⁻¹ * (B.volZZ / B.unitLevelVolume * B.Coo⁻¹))
        = B.Gam1 * B.volB * (B.MM / B.unitLevelVolume / B.μK) * ((1 / B.c0) * (1 / B.c0')) := by
      unfold S3.MassData.AA
      field_simp
    rw [e1, hL, hC1, hC2]
    unfold S3.MassData.Dstar
    have hVG : B.volG = B.volHa * B.volHa' / B.volB := by
      field_simp
      linarith
    rw [hVG]
    field_simp
  have hX : 0 ≤ B.Gam1 * B.AA * ((B.c0 * B.c0')⁻¹ * (B.volZZ / B.unitLevelVolume * B.Coo⁻¹)) := by
    positivity
  calc B.Gam1 * B.AA * ((B.c0 * B.c0')⁻¹ * B.IntN)
      = B.Gam1 * B.AA * ((B.c0 * B.c0')⁻¹ * (B.volZZ / B.unitLevelVolume * B.Coo⁻¹)) * B.IntOO := by
        rw [hJ]; ring
    _ ≤ B.Gam1 * B.AA * ((B.c0 * B.c0')⁻¹ * (B.volZZ / B.unitLevelVolume * B.Coo⁻¹)) * (1 / B.deg) :=
        mul_le_mul_of_nonneg_left hInf hX
    _ = B.d * B.d' / B.Dstar := key
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A
