-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.cPosCutBase
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:24.757517+00:00
-- url     : https://prove2.me/submissions/66c0ad69-63f2-464c-8bf6-9c764ad1eb27

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_pos_ofReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Finset Formalism.FourierDecayAlt.I Formalism.FourierDecayAlt.P.Interlace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr2
namespace Formalism.FourierDecayAlt.P.Fr2
theorem _root_.solution : CPosCutBase := by
  intro hI hQ hQs hC S _ _ k u u' ρ l T T' w hl1 hlk hint hT hT' hpts hpw e
  apply hC S _ _ w (fun a ha => (hpts a ha).1) hpw
  intro a ha
  obtain ⟨him, hcut⟩ := hpts a ha
  have himy : (ypt a).im = 0 := by unfold ypt; split_ifs <;> simp [him]
  obtain ⟨y, hy⟩ : ∃ y : ℝ, ypt a = (y : ℂ) := ⟨(ypt a).re, by apply Complex.ext <;> simp [himy]⟩
  have hcut' : OnCut u u' l y ∨ OnCut u u' l (y + 1) := by simpa [hy] using hcut
  have hx : ∀ z : ℝ, 0 < (-1 : ℝ) ^ (k - l) * xpoly k ρ z →
      Pos ((-1 : ℂ) ^ (k - l) * ∏ i ∈ Finset.Icc 1 (k - 1), (((z : ℝ) : ℂ) + (ρ i : ℂ))) := by
    intro z hz
    have c : ((-1 : ℂ) ^ (k - l) * ∏ i ∈ Finset.Icc 1 (k - 1), (((z : ℝ) : ℂ) + (ρ i : ℂ))) =
        (((-1 : ℝ) ^ (k - l) * xpoly k ρ z : ℝ) : ℂ) := by
      unfold xpoly; push_cast; ring
    rw [c]; exact pos_ofReal hz
  have hq : ∀ z : ℝ, 0 < qpoly k T T' u u' z →
      Pos (-((T : ℂ) * T') * ∏ i ∈ Finset.Icc 1 k, (((z : ℝ) : ℂ) + 1 / 2 + (u i : ℂ)) * (((z : ℝ) : ℂ) + 1 / 2 + (u' i : ℂ))) := by
    intro z hz
    have c : (-((T : ℂ) * T') * ∏ i ∈ Finset.Icc 1 k, (((z : ℝ) : ℂ) + 1 / 2 + (u i : ℂ)) * (((z : ℝ) : ℂ) + 1 / 2 + (u' i : ℂ))) =
        ((qpoly k T T' u u' z : ℝ) : ℂ) := by
      unfold qpoly; push_cast; ring
    rw [c]; exact pos_ofReal hz
  rw [hy]
  rcases hcut' with hc | hc
  · have a0 := hI k u u' ρ l y hl1 hlk hint hc 0 (by simp)
    have a1 := hI k u u' ρ l y hl1 hlk hint hc 1 (by simp)
    rw [add_zero] at a0
    refine ⟨hx y a0, ?_, hq y (hQ k u u' ρ l y T T' hl1 hlk hint hc hT hT')⟩
    have := hx (y + 1) a1; simpa using this
  · have a0 := hI k u u' ρ l (y + 1) hl1 hlk hint hc 0 (by simp)
    have a1 := hI k u u' ρ l (y + 1) hl1 hlk hint hc (-1) (by simp)
    have b := hQs k u u' ρ l (y + 1) T T' hl1 hlk hint hc hT hT'
    rw [add_zero] at a0
    have e1 : y + 1 + -1 = y := by ring
    have e2 : y + 1 - 1 = y := by ring
    rw [e1] at a1; rw [e2] at b
    refine ⟨hx y a1, ?_, hq y b⟩
    have := hx (y + 1) a0; simpa using this
end Formalism.FourierDecayAlt.P.Fr2
