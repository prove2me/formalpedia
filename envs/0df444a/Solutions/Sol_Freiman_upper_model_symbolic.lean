-- Prove2me | solution 1 for Freiman.upper_model_symbolic
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:38:06.16322+00:00
-- url     : https://prove2.me/submissions/c8ac0422-d756-4f8d-82fd-38344069b55e

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_upper_padding_converges
import Theorems.Thm_Freiman_upper_padding_alphabet
import Theorems.Thm_Freiman_upper_padding_upper_bound
import Theorems.Thm_Freiman_upper_small_constants
import Theorems.Thm_Freiman_padded_models_symbolic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Freiman
open Filter Topology

theorem solution (t : ℝ) (ht : upperRayStart ≤ t) (hm : upperModel t) :
    t ∈ symbolicLagrangeSpectrum := by
  obtain ⟨a, D, N, hN, hc, hD, hb⟩ := hm
  have hlim : Filter.Tendsto (fun j => localValue (upperPad a j) 0)
      Filter.atTop (nhds t) := by simpa only [hc] using upper_padding_converges a
  have heps : Filter.Tendsto (fun j => |localValue (upperPad a j) 0 - t|)
      Filter.atTop (nhds 0) := by
    simpa using (hlim.sub (tendsto_const_nhds (x := t))).abs
  apply padded_models_symbolic (upperPad a) 3 t
    (fun j => |localValue (upperPad a j) 0 - t|)
    ⟨max N 3, upper_padding_alphabet a N hN⟩
  · intro j i hi
    simp [upperPad, Nat.not_le.mpr hi]
  · exact hlim
  · exact upper_padding_upper_bound a D t hD hb
  · exact heps
  · norm_num
    exact upper_small_constants.2.2.le.trans ht
