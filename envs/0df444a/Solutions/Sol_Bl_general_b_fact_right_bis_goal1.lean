-- Prove2me | solution 1 for Bl.general_b_fact_right_bis.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:00.502663+00:00
-- url     : https://prove2.me/submissions/f09a8630-f72b-478f-9000-612ef00216c5

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightBis_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial ComplexOrder
open Bl Bl.general_b_fact_right_bis
namespace Bl.general_b_fact_right_bis
theorem _root_.solution {k : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (μ : ℂ) (hμ : G.charpoly.IsRoot μ) :
    ∃ v : Fin k → ℂ, v ≠ 0 ∧ G *ᵥ v = μ • v := by
  have hdet : (Matrix.scalar (Fin k) μ - G).det = 0 := by
    rw [← Matrix.eval_charpoly]; exact hμ
  obtain ⟨v, hv, h⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at h
  rw [← h]
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
end Bl.general_b_fact_right_bis
