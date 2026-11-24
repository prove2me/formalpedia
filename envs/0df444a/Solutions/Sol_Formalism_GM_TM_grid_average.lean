-- Prove2me | solution 1 for Formalism.GM.TM.grid_average
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:32:33.129808+00:00
-- url     : https://prove2.me/submissions/3ed7c167-4c17-4fe5-82c7-64f89365ca94

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Theorems.Thm_Formalism_GM_TM_sum_fiber

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open Finset
namespace Formalism.GM.TM
theorem _root_.solution {t : ℕ} (s : Fin t → Finset ℕ) (bad : (Fin t → ℕ) → ℝ) (B Dm : Fin t → (Fin t → ℕ) → ℝ)
    (eps : Fin t → ℝ) (hcard : ∀ i, 0 < (s i).card)
    (h1 : ∀ n ∈ Fintype.piFinset s, bad n ≤ ∑ i, B i n)
    (h2 : ∀ i, ∀ n ∈ Fintype.piFinset s, ∑ y ∈ s i, B i (Function.update n i y) ≤ (s i).card * (eps i * Dm i n)) :
    (∑ n ∈ Fintype.piFinset s, bad n) / (Fintype.piFinset s).card ≤
      ∑ i, eps i * ((∑ n ∈ Fintype.piFinset s, Dm i n) / (Fintype.piFinset s).card) := by
  have hB : ∀ i, ∑ n ∈ Fintype.piFinset s, B i n ≤ eps i * ∑ n ∈ Fintype.piFinset s, Dm i n := by
    intro i
    have hc : (0 : ℝ) < (s i).card := by exact_mod_cast hcard i
    have := sum_fiber s (B i) i
    have h3 : ∑ n ∈ Fintype.piFinset s, ∑ y ∈ s i, B i (Function.update n i y) ≤
        ∑ n ∈ Fintype.piFinset s, (s i).card * (eps i * Dm i n) := Finset.sum_le_sum (h2 i)
    rw [this, ← Finset.mul_sum, ← Finset.mul_sum] at h3
    exact le_of_mul_le_mul_left h3 hc
  have hsum : ∑ n ∈ Fintype.piFinset s, bad n ≤ ∑ i, eps i * ∑ n ∈ Fintype.piFinset s, Dm i n := by
    calc ∑ n ∈ Fintype.piFinset s, bad n ≤ ∑ n ∈ Fintype.piFinset s, ∑ i, B i n := Finset.sum_le_sum h1
      _ = ∑ i, ∑ n ∈ Fintype.piFinset s, B i n := Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum fun i _ => hB i
  have hG : (0 : ℝ) ≤ (Fintype.piFinset s).card := by positivity
  calc (∑ n ∈ Fintype.piFinset s, bad n) / (Fintype.piFinset s).card
      ≤ (∑ i, eps i * ∑ n ∈ Fintype.piFinset s, Dm i n) / (Fintype.piFinset s).card :=
        div_le_div_of_nonneg_right hsum hG
    _ = _ := by rw [Finset.sum_div]; simp only [mul_div_assoc]
end Formalism.GM.TM
