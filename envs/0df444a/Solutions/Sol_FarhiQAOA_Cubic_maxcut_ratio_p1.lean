-- Prove2me | solution 1 for FarhiQAOA.Cubic.maxcut_ratio_p1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:48:37.610507+00:00
-- url     : https://prove2.me/submissions/631a5cc7-d50a-4f85-9e10-443648819ee8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_FarhiQAOA_Cubic_Types
import Theorems.Thm_FarhiQAOA_Cubic_eq_32
import Theorems.Thm_FarhiQAOA_Cubic_vertex_bound
import Theorems.Thm_FarhiQAOA_Cubic_cut_le
import Theorems.Thm_FarhiQAOA_Cubic_eq_35_min
import Theorems.Thm_FarhiQAOA_Cubic_k4_case

open QAlgorithms FarhiQAOA.Cubic in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (hconn : G.Connected) :
    ∃ γ β : ℝ, γ ∈ Set.Icc 0 (2 * Real.pi) ∧ β ∈ Set.Icc 0 Real.pi ∧
      ∀ z : Qubits n, (1731 / 2500 : ℝ) * cutValue G z ≤ F1 G γ β := by
  by_cases hn4 : n = 4
  · subst hn4
    obtain ⟨γ, β, hγ, hβ, hlt⟩ := k4_case G h3
    exact ⟨γ, β, hγ, hβ, fun z => (hlt z).le⟩
  · have hne : Nonempty (Fin n) := hconn.nonempty
    have hn_pos : 0 < n := Fin.pos_iff_nonempty.mpr hne
    have hn_real_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    have hn_ne : (n : ℝ) ≠ 0 := hn_real_pos.ne'
    set s : ℝ := (S G : ℝ) / (n : ℝ) with hsdef
    set t : ℝ := (T G : ℝ) / (n : ℝ) with htdef
    have hs : 0 ≤ s := by positivity
    have ht : 0 ≤ t := by positivity
    have hvb : 3 * (T G : ℝ) + 4 * (S G : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast vertex_bound G h3
    have hst : 4 * s + 3 * t ≤ 1 := by
      rw [hsdef, htdef, mul_div_assoc', mul_div_assoc', ← add_div, div_le_one hn_real_pos]
      linarith
    obtain ⟨γ, β, hγ, hβ, hmin⟩ := eq_35_min s t hs ht hst
    refine ⟨γ, β, hγ, hβ, fun z => ?_⟩
    have hcut := cut_le G h3 z
    have heq32 := eq_32 G h3 hconn hn4 γ β
    have hmul := mul_le_mul_of_nonneg_right hmin hn_real_pos.le
    have hsn : s * (n : ℝ) = (S G : ℝ) := div_mul_cancel₀ _ hn_ne
    have htn : t * (n : ℝ) = (T G : ℝ) := div_mul_cancel₀ _ hn_ne
    have hlhs : (1731 / 2500 : ℝ) * (3 / 2 - s - t) * (n : ℝ) =
        (1731 / 2500 : ℝ) * ((3 : ℝ) / 2 * (n : ℝ) - (S G : ℝ) - (T G : ℝ)) := by
      calc (1731 / 2500 : ℝ) * (3 / 2 - s - t) * (n : ℝ)
          = (1731 / 2500 : ℝ) * ((3 : ℝ) / 2 * (n : ℝ) - s * (n : ℝ) - t * (n : ℝ)) := by ring
        _ = (1731 / 2500 : ℝ) * ((3 : ℝ) / 2 * (n : ℝ) - (S G : ℝ) - (T G : ℝ)) := by
          rw [hsn, htn]
    have hrhs : (s * fg4 γ β + (4 * s + 3 * t) * fg5 γ β + (3 / 2 - 5 * s - 3 * t) * fg6 γ β) * (n : ℝ) =
        F1 G γ β := by
      calc (s * fg4 γ β + (4 * s + 3 * t) * fg5 γ β + (3 / 2 - 5 * s - 3 * t) * fg6 γ β) * (n : ℝ)
          = (s * (n : ℝ)) * fg4 γ β + (4 * (s * (n : ℝ)) + 3 * (t * (n : ℝ))) * fg5 γ β +
            ((3 : ℝ) / 2 * (n : ℝ) - 5 * (s * (n : ℝ)) - 3 * (t * (n : ℝ))) * fg6 γ β := by ring
        _ = F1 G γ β := by rw [hsn, htn, ← heq32]
    linarith
