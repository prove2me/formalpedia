-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A.t_NormOfMain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:02.226919+00:00
-- url     : https://prove2.me/submissions/5cc8f019-0cd5-4bbc-b599-d62971a14cf4

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
theorem _root_.solution : NormOfMain := by
  intro hM P _ B hin
  obtain ⟨hPos, hJac, hNu, hInf, hVol, hLev, hMas, hCol, hOrd, hTyp, hInd⟩ := hin
  obtain ⟨hGam, hμK, hμKpp, hμSpp, hμSpp', hMM, hU, hc0, hc0', htt, hAA, hD⟩ := book_constants_pos_of_pos B hPos
  have hPos' := hPos
  obtain ⟨hp, hμKo, hμSo, hμSo', hMo, hU00o, hμH, hμH', hμHpp, hμHpp', hμN, hμN', hvolZZ, hvolPP, hal,
    hvolG, hvolHa, hvolHa', hvolNa, hvolNa', hvolB, hvolH, hvolH', hvolN, hvolN', hCoo, hdeg, hdimπ,
    hdimπ', hρ0, hρ0', hd, hd', hn0c, hsup, hδ⟩ := hPos'
  by_cases hI : 0 ≤ B.IntN
  · let B' : S3.MassData P := { B with
      δ := 0, e1 := 1, supdens := 1, KtopV := B.IntN / (B.c0 * B.c0'), n0c := B.AA / B.ρ0,
      KV := B.AA / B.ρ0 * (B.IntN / (B.c0 * B.c0')),
      Sig := B.ρ0 * (B.AA / B.ρ0 * (B.IntN / (B.c0 * B.c0'))),
      Kgs2 := B.tt * B.Gam1 * (B.ρ0 * (B.AA / B.ρ0 * (B.IntN / (B.c0 * B.c0')))) }
    have hPosB' : B'.Pos :=
      ⟨hp, hμKo, hμSo, hμSo', hMo, hU00o, hμH, hμH', hμHpp, hμHpp', hμN, hμN', hvolZZ, hvolPP, hal,
        hvolG, hvolHa, hvolHa', hvolNa, hvolNa', hvolB, hvolH, hvolH', hvolN, hvolN', hCoo, hdeg, hdimπ,
        hdimπ', hρ0, hρ0', hd, hd', div_pos hAA hρ0, zero_le_one, le_refl 0⟩
    have hTwoA : B'.InTwoA := le_refl _
    have hForm : B'.InForm := rfl
    have hKer : B'.InKernel := by
      refine ⟨?_, div_nonneg hI (mul_pos hc0 hc0').le⟩
      show B.AA / B.ρ0 * (B.IntN / (B.c0 * B.c0')) ≤ 1 * (B.AA / B.ρ0) * (B.IntN / (B.c0 * B.c0'))
      rw [one_mul]
    have hMass : B'.InMass := by
      show B.AA / B.ρ0 * B.ρ0 = B.AA
      field_simp
    have hDens : B'.InDens := le_refl (1 : ℝ)
    have hThA : B'.InTheoremA := by
      show B.c0 * B.c0' * (B.IntN / (B.c0 * B.c0')) ≤ (1 + 0) * B.IntN
      have : B.c0 * B.c0' * (B.IntN / (B.c0 * B.c0')) = B.IntN := by field_simp
      rw [this]; simp
    obtain ⟨hGS, hB, -⟩ := hM P B' hPosB' hTwoA hForm hKer hMass hDens hThA hJac hNu hInf hVol hLev hMas
      hCol hOrd hTyp hInd
    rw [hGS] at hB
    have hB2 : B.tt * B.Gam1 * (B.ρ0 * (B.AA / B.ρ0 * (B.IntN / (B.c0 * B.c0')))) ≤
        (1 + 0) * 1 * B.tt * (B.d * B.d' / B.Dstar) := hB
    have e : B.tt * B.Gam1 * (B.ρ0 * (B.AA / B.ρ0 * (B.IntN / (B.c0 * B.c0')))) =
        B.tt * (B.Gam1 * B.AA * ((B.c0 * B.c0')⁻¹ * B.IntN)) := by field_simp
    rw [e] at hB2
    have hB3 : B.tt * (B.Gam1 * B.AA * ((B.c0 * B.c0')⁻¹ * B.IntN)) ≤ B.tt * (B.d * B.d' / B.Dstar) := by
      linarith
    exact le_of_mul_le_mul_left hB3 htt
  · have hI' : B.IntN ≤ 0 := le_of_not_ge hI
    have h1 : B.Gam1 * B.AA * ((B.c0 * B.c0')⁻¹ * B.IntN) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_pos hGam hAA).le
        (mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr (mul_pos hc0 hc0')).le hI')
    have h2 : 0 ≤ B.d * B.d' / B.Dstar := (div_pos (mul_pos hd hd') hD).le
    linarith
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A
