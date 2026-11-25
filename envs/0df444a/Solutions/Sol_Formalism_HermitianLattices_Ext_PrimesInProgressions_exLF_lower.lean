-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exLF_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:02:18.627798+00:00
-- url     : https://prove2.me/submissions/6930ef8d-3600-4307-9108-801344f17bfa

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_of_ne
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_one_char_apply
import Theorems.Thm_Formalism_ZeroFreeDirichlet_inverseBound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
variable {M : ℕ} [NeZero M]
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (χ : DirichletCharacter ℂ M) (s : ℂ) (hs : 1 < s.re) :
    min 1 ‖s - 1‖ * ((s.re - 1) / s.re) ≤ ‖exLF χ s‖ := by
  have hI := inverseBound M χ s hs
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  have hne : DirichletCharacter.LFunction χ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hs1) hs.le
  have hpos : 0 < ‖DirichletCharacter.LFunction χ s‖ := norm_pos_iff.2 hne
  have hq : 0 < (s.re - 1) / s.re := div_pos (by linarith) (by linarith)
  have hL : (s.re - 1) / s.re ≤ ‖DirichletCharacter.LFunction χ s‖ := by
    have h1 : (s.re / (s.re - 1))⁻¹ ≤ (‖DirichletCharacter.LFunction χ s‖⁻¹)⁻¹ :=
      inv_anti₀ (inv_pos.2 hpos) hI
    rwa [inv_inv, inv_div] at h1
  by_cases h : χ = 1
  · subst h
    rw [exLF_one_char_apply hs1, norm_mul]
    exact mul_le_mul (min_le_right _ _) hL hq.le (norm_nonneg _)
  · rw [exLF_of_ne h]
    calc min 1 ‖s - 1‖ * ((s.re - 1) / s.re) ≤ 1 * ((s.re - 1) / s.re) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hq.le
      _ ≤ _ := by rw [one_mul]; exact hL
end Formalism.HermitianLattices.Ext.PrimesInProgressions
