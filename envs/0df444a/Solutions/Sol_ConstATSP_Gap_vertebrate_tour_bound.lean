-- Prove2me | solution 1 for ConstATSP.Gap.vertebrate_tour_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T14:04:45.135904+00:00
-- url     : https://prove2.me/submissions/42231662-1eb8-4155-b0a0-164b760dea60
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ConstATSP_Gap_Graph
import Definitions.Def_ConstATSP_Gap_Instance
import Theorems.Thm_ConstATSP_Gap_theorem_5_1
import Theorems.Thm_ConstATSP_Gap_theorem_10_1

open ConstATSP.Gap

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (I : ConstATSP.Gap.Instance V E) (hI : I.IsValid)
    (B : E → ℕ) (hB : I.IsVertebrate B) :
    ∃ F : E → ℕ, IsTour I.G F ∧ I.wt F ≤ 2 * I.value + 21 * I.lbCompl B + I.wt B := by
  obtain ⟨F, hF, hwt⟩ := theorem_5_1 I hI B hB.1 4 (2 * I.value + I.lbCompl B) (by norm_num)
    (theorem_10_1 I hI B hB)
  exact ⟨F, hF, by linarith⟩
