-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.F.t_RowNGJoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:17.414216+00:00
-- url     : https://prove2.me/submissions/c072bbec-fe16-4ea4-be4a-f48dc9b6b595

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_F_pos_facts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.F
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset NumberField
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.F
theorem _root_.solution : RowNGJoint := by
  intro hch C1 C0 A CB CSt Cg CT hCB hCSt hCg hCT hA
  obtain ⟨hc48, hCSS, hRFC, hCCS, hFB, hSB, hMA, hRA, hNorm, hFP, hNR, hES, hNum⟩ := hch
  obtain ⟨Cn, hCn0, hCn⟩ := hNum A CB CSt Cg CT hCB hCSt hCg hCT
  refine ⟨Cn, hCn0, ?_⟩
  intro E _ _ _ τ Rw I H H₁ _ _ _ _ _ _ X r k Cl Nu N P _ B b rd g TT cSt e1 Irat Ire hAbs hGam hNI hFI
    hSz hIn
  obtain ⟨hCl, hAmp, hNo, hPt, hLoc, hMe, hGM, hHt, hTB⟩ := hIn
  have hnum := hCn r _ b rd g TT cSt e1 hSz
  obtain ⟨hf, hb, hrd, hrdb, hg1, hgb, hTT, hTTb, hcSt, hcStb, he1, he12⟩ := hSz
  obtain ⟨hAApos, hddpos⟩ := pos_facts B hNI.1
  have hLam : 0 < abelian₂ rd r k (Fintype.card (InfinitePlace E)) := by
    unfold abelian₂; positivity
  have hrow := hRA hc48 hCSS hRFC hCCS hFB hSB hMA E τ Rw I H H₁ X r k Cl Nu N C1 C0 (A * (r + 1) ^ 2)
    _ _ cSt _ e1 _ (hES C1 C0 A r hA) (by positivity) (one_le_pow₀ hg1) hcSt
    (le_of_lt (mul_pos hLam hAApos)) he1 hAbs hCl hAmp hNo hPt hLoc hMe hGM hHt hTB
  have hnr := hNR hNorm hFP P B rd g r k _ Irat Ire hNI hFI
  unfold PB.Terms.RowNG
  refine le_trans hrow ?_
  rw [hGam]
  generalize Fintype.card (InfinitePlace E) = f at *
  set κ : ℝ := ((2 : ℝ) ^ (k - 2 * r - 5))⁻¹ with hκ
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  set S : ℝ := 64 ^ (f * (r + 1)) with hS
  set Pc : ℝ := rd ^ (12 * r * (r + 1) * f) * TT ^ (6 * f) with hPc
  set gA : ℝ := (g ^ f) ^ (A * (r + 1) ^ 2) with hgA
  set ex : ℝ := Real.exp (CB * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b) with hex
  set vg : ℝ := (rd / 2) ^ (f * (r + 1)) * g ^ (f * (r + 1) * (2 * r + 3)) with hvg
  set dd : ℝ := B.d * B.d' / B.Dstar with hdd
  set AAre : ℝ := abelian₂ rd r k f * B.AA with hAAre
  set EX : ℝ := Real.exp (Cn * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b) with hEX
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hPc0 : 0 ≤ Pc := by rw [hPc]; positivity
  have hgA0 : 0 ≤ gA := by rw [hgA]; positivity
  have hex0 : 0 ≤ ex := by rw [hex]; positivity
  have hF : 0 ≤ S * κ * cSt * e1 * Pc * gA * ex := by positivity
  calc B.Gam1 * (S * (κ * cSt * AAre * e1 * Pc * gA * (ex * Ire)))
      = (S * κ * cSt * e1 * Pc * gA * ex) * (B.Gam1 * AAre * Ire) := by ring
    _ ≤ (S * κ * cSt * e1 * Pc * gA * ex) * (vg * dd) := mul_le_mul_of_nonneg_left hnr hF
    _ = κ * (S * (cSt * e1 * Pc * gA * ex) * vg) * dd := by ring
    _ ≤ κ * EX * dd := by
        apply mul_le_mul_of_nonneg_right _ hddpos.le
        exact mul_le_mul_of_nonneg_left hnum hκ0
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.F
