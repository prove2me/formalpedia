-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Interlace.q_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:32.454151+00:00
-- url     : https://prove2.me/submissions/6557d8f7-3133-4ebf-bad8-1cf74a2fa6c3

import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Theorems.Thm_Formalism_FourierDecayAlt_P_Interlace_interlaces_swap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Interlace_antitone_on
import Theorems.Thm_Formalism_FourierDecayAlt_P_Interlace_u_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Interlace
open Finset Formalism.FourierDecayAlt.I
namespace Formalism.FourierDecayAlt.P.Interlace
theorem _root_.solution (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) :
    ∏ i ∈ Icc 1 k, ((Y + 1/2 + u i) * (Y + 1/2 + u' i)) < 0 := by
  have hu := antitone_on (u_step h)
  have hu' := antitone_on (u_step (interlaces_swap h))
  have hl : l ∈ Icc 1 k := mem_Icc.2 ⟨hl1, hlk⟩
  rw [← mul_prod_erase _ _ hl]
  apply mul_neg_of_neg_of_pos
  · apply mul_neg_of_neg_of_pos <;> linarith
  · apply prod_pos
    intro i hi
    have hne := ne_of_mem_erase hi
    have hi' := mem_Icc.1 (mem_of_mem_erase hi)
    rcases lt_or_gt_of_ne hne with hil | hil
    · obtain ⟨a, b, c, d⟩ := h i (mem_Icc.2 ⟨hi'.1, by omega⟩)
      have h1 := hu' (i + 1) l (by omega) (by omega) hlk
      have h2 := hu' i l hi'.1 (by omega) hlk
      apply mul_pos <;> linarith
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      obtain ⟨a, b, c, d⟩ := h j (mem_Icc.2 ⟨by omega, by omega⟩)
      have h1 := hu l (j + 1) hl1 (by omega) hi'.2
      have h2 := hu l j hl1 (by omega) (by omega)
      apply mul_pos_of_neg_of_neg <;> linarith
end Formalism.FourierDecayAlt.P.Interlace
