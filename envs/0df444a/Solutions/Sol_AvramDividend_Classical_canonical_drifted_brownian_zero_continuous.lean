-- Prove2me | solution 1 for AvramDividend.Classical.canonical_drifted_brownian_zero_continuous
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:22:05.560999+00:00
-- url     : https://prove2.me/submissions/81c392ac-309e-4386-8317-fcbc42be8931

import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic

open ProbabilityTheory MeasureTheory
open scoped NNReal

lemma S194cbz_cont (ω : ℝ≥0 → ℝ) : Continuous (fun t : ℝ≥0 => ProbabilityTheory.brownian t ω) := by
  have hs := isPreBrownianReal_preBrownian.exists_continuous_modification.choose_spec.2.2
  rw [continuous_iff_continuousAt]
  intro t
  have hβ : ((1/5 : ℝ≥0) : ℝ) < ⨆ n : ℕ, (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ)) := by
    have hb : BddAbove (Set.range fun n : ℕ => (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ))) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨n, rfl⟩
      rw [div_le_one (by positivity)]
      push_cast; linarith
    refine lt_of_lt_of_le ?_ (le_ciSup hb 0)
    norm_num
  obtain ⟨U, hU, C, hH⟩ := hs ω t (1/5) (by norm_num) hβ
  exact (hH.continuousOn (by norm_num)).continuousAt hU

theorem solution
    (ω : ℝ≥0 → ℝ) :
    (ProbabilityTheory.brownian 0 ω - ProbabilityTheory.brownian 0 ω - (0 : ℝ)) = 0 ∧
    Continuous (fun t : ℝ≥0 =>
      ProbabilityTheory.brownian t ω - ProbabilityTheory.brownian 0 ω - (t : ℝ)) := by
  refine ⟨by ring, ?_⟩
  have := S194cbz_cont ω
  fun_prop
