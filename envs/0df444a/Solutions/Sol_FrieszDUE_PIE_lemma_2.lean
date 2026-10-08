-- Prove2me | solution 1 for FrieszDUE.PIE.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:41:59.697551+00:00
-- url     : https://prove2.me/submissions/62fcb7a2-ed07-4491-8719-350a431016cc

import Mathlib
import Definitions.Def_FrieszDUE_PIE_Setting

open MeasureTheory FrieszDUE.PIE

theorem solution (T : ℝ) (S : Set ℝ) (hS : S ⊆ Set.Icc 0 T) (hSpos : 0 < ν T S)
    (f : ℝ → ℝ) (hf : Measurable f) (hpos : 0 < ν T {t | t ∈ S ∧ 0 < f t}) :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Icc (0 : ℝ) ε₀, 0 < ν T {t | t ∈ S ∧ ε < f t} := by
  classical
  have hex : ∃ n : ℕ, 0 < ν T {t | t ∈ S ∧ (1 : ℝ) / (n + 1) < f t} := by
    by_contra hn
    have hz : ∀ n : ℕ, ν T {t | t ∈ S ∧ (1 : ℝ) / (n + 1) < f t} = 0 := by
      intro n
      exact le_antisymm (le_of_not_gt (fun h => hn ⟨n,h⟩)) bot_le
    have hs : {t | t ∈ S ∧ 0 < f t} ⊆ ⋃ n : ℕ, {t | t ∈ S ∧ (1 : ℝ) / (n + 1) < f t} := by
      rintro t ⟨ht, hft⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hft
      exact Set.mem_iUnion.mpr ⟨n, ht, hn⟩
    have := measure_mono (μ := ν T) hs
    have hu := measure_iUnion_null hz
    rw [hu] at this
    exact (not_le_of_gt hpos) this
  obtain ⟨n, hn⟩ := hex
  refine ⟨1 / (n + 1), by positivity, ?_⟩
  intro ε hε
  exact hn.trans_le (measure_mono (fun t ht => ⟨ht.1, lt_of_le_of_lt hε.2 ht.2⟩))

#print axioms solution
