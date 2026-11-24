-- Prove2me | solution 1 for Formalism.REAL.leading_minors_positive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:44:08.261093+00:00
-- url     : https://prove2.me/submissions/3bf1cde3-c449-4061-ae15-2f3deaef903a

import Definitions.Def_Formalism_RealPlaceAnalysis_LminorPos
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_LeadingMinorEqDetSubmatrix
import Theorems.Thm_Formalism_REAL_exp_posDef_of_hermitian
import Theorems.Thm_Formalism_REAL_leading_minor_eq_det_submatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : LminorPos := by
  intro n Y hY i
  have hP := (exp_posDef_of_hermitian Y hY).submatrix (Fin.castLE_injective (Nat.lt_succ_iff.mp i.isLt))
  have h := hP.det_pos
  rw [← leading_minor_eq_det_submatrix] at h
  obtain ⟨h1, h2⟩ := Complex.pos_iff.mp h
  exact ⟨h2.symm, h1⟩
end Formalism.REAL
