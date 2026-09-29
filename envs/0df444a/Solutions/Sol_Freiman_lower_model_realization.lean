-- Prove2me | solution 1 for Freiman.lower_model_realization
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:56:34.566138+00:00
-- url     : https://prove2.me/submissions/1c51adbe-bd3e-46e6-b542-a9813935ee11

import Theorems.Thm_Freiman_lower_model_structure
import Theorems.Thm_Freiman_lower_central_dominance
import Theorems.Thm_Freiman_background_constant_order
import Theorems.Thm_Freiman_separated_peaks
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (ht : cF ≤ t) (hm : lowerHasValue t) : t ∈ lagrangeSpectrum := by
  rcases hm with ⟨a,ha,hcenter⟩
  have hbg := background_constant_order
  refine separated_peaks a t hcenter ?_ (lower_model_structure a ha).2.2.2.1 (Or.inr ⟨ha.1,?_⟩)
  · intro i
    by_cases hi : i = 0
    · simpa [hi,hcenter]
    · exact le_trans (le_of_lt (lt_trans (lower_central_dominance a ha i hi) hbg.2.2)) ht
  · exact le_trans (le_of_lt (lt_trans hbg.2.1 hbg.2.2)) ht
