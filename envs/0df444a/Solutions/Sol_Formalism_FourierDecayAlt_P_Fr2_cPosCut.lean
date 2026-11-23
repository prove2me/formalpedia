-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.cPosCut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:24.544116+00:00
-- url     : https://prove2.me/submissions/9ae8dc71-c161-4056-aa9c-93842e8cad27

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
theorem _root_.solution : CPosCut := by
  intro hI hQ hQs hC S _ _ k u u' ρ l T T' w hl1 hlk hint hT hT' hpts hpw e
  apply hC S _ _ w (fun a ha => (hpts a ha).1) hpw
  intro a ha
  obtain ⟨him, hcut⟩ := hpts a ha
  obtain ⟨y, hy⟩ : ∃ y : ℝ, a.pt = (y : ℂ) := ⟨a.pt.re, by apply Complex.ext <;> simp [him]⟩
  have hcut' : OnCut u u' l y := by simpa [hy] using hcut
  have hx : ∀ e : ℝ, e ∈ ({-1, 0, 1} : Finset ℝ) →
      Pos ((-1 : ℂ) ^ (k - l) * ∏ i ∈ Finset.Icc 1 (k - 1), (((y + e : ℝ) : ℂ) + (ρ i : ℂ))) := by
    intro e he
    have := hI k u u' ρ l y hl1 hlk hint hcut' e he
    have c : ((-1 : ℂ) ^ (k - l) * ∏ i ∈ Finset.Icc 1 (k - 1), (((y + e : ℝ) : ℂ) + (ρ i : ℂ))) =
        (((-1 : ℝ) ^ (k - l) * xpoly k ρ (y + e) : ℝ) : ℂ) := by
      unfold xpoly; push_cast; ring
    rw [c]; exact pos_ofReal this
  have hq : ∀ z : ℝ, 0 < qpoly k T T' u u' z →
      Pos (-((T : ℂ) * T') * ∏ i ∈ Finset.Icc 1 k, (((z : ℝ) : ℂ) + 1 / 2 + (u i : ℂ)) * (((z : ℝ) : ℂ) + 1 / 2 + (u' i : ℂ))) := by
    intro z hz
    have c : (-((T : ℂ) * T') * ∏ i ∈ Finset.Icc 1 k, (((z : ℝ) : ℂ) + 1 / 2 + (u i : ℂ)) * (((z : ℝ) : ℂ) + 1 / 2 + (u' i : ℂ))) =
        ((qpoly k T T' u u' z : ℝ) : ℂ) := by
      unfold qpoly; push_cast; ring
    rw [c]; exact pos_ofReal hz
  rw [hy]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := hx 0 (by simp); simpa using this
  · have := hx 1 (by simp); simpa using this
  · have := hx (-1) (by simp); simpa [sub_eq_add_neg] using this
  · exact hq y (hQ k u u' ρ l y T T' hl1 hlk hint hcut' hT hT')
  · have := hq (y - 1) (hQs k u u' ρ l y T T' hl1 hlk hint hcut' hT hT'); simpa using this
end Formalism.FourierDecayAlt.P.Fr2
