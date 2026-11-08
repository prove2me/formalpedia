-- Prove2me | solution 1 for AvgValueAlloc.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:35:02.553237+00:00
-- url     : https://prove2.me/submissions/0c1ba5ae-d45a-40ae-bcd8-f221c2816eea

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_OPToff
import Definitions.Def_AvgValueAlloc_posVal

open scoped ENNReal

open AvgValueAlloc in
theorem solution {n T : ℕ} (ρ : Fin n → ℚ) (hρ : ∀ j, 0 < ρ j) (Q : Fin T → AvgValueAlloc.Vec n) :
    AvgValueAlloc.OPToff ρ Q ≤ (T : ℝ≥0∞) * ENNReal.ofReal (AvgValueAlloc.posValSum ρ Q) := by
  classical
  have hPS0 : 0 ≤ AvgValueAlloc.posValSum ρ Q := by
    unfold AvgValueAlloc.posValSum
    exact Finset.sum_nonneg (fun i _ => NNRat.cast_nonneg _)
  have hle_pv : ∀ (s : Fin T) (j : Fin n), ρ j ≤ (Q s j : ℚ) →
      ((Q s j : ℚ≥0) : ℝ) ≤ AvgValueAlloc.posValSum ρ Q := by
    intro s j hj
    have h1 : Q s j ≤ AvgValueAlloc.posVal ρ (Q s) := by
      unfold AvgValueAlloc.posVal
      exact Finset.le_sup (f := Q s) (by
        unfold AvgValueAlloc.posSet
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)
    have h2 : ((AvgValueAlloc.posVal ρ (Q s) : ℚ≥0) : ℝ) ≤ AvgValueAlloc.posValSum ρ Q := by
      unfold AvgValueAlloc.posValSum
      exact Finset.single_le_sum (f := fun i => ((AvgValueAlloc.posVal ρ (Q i) : ℚ≥0) : ℝ))
        (fun i _ => NNRat.cast_nonneg _) (Finset.mem_univ s)
    exact (NNRat.cast_le.2 h1).trans h2
  unfold AvgValueAlloc.OPToff
  apply iSup₂_le
  intro dec hfeas
  have key : ∀ t, (dec t).elim 0 (fun j => ((Q t j : ℚ≥0) : ℝ)) ≤ AvgValueAlloc.posValSum ρ Q := by
    intro t
    cases h : dec t with
    | none => simpa using hPS0
    | some j =>
      simp only [Option.elim]
      by_cases hpos : ρ j ≤ (Q t j : ℚ)
      · exact hle_pv t j hpos
      · push_neg at hpos
        have hex : ∃ s, dec s = some j ∧ ρ j ≤ (Q s j : ℚ) := by
          by_contra hno
          push_neg at hno
          have hne : (Finset.univ.filter (fun s => dec s = some j)).Nonempty :=
            ⟨t, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩
          have hlt := Finset.sum_lt_sum_of_nonempty hne (f := fun s => ((Q s j : ℚ) - ρ j))
            (g := fun _ => (0:ℚ)) (fun s hs => by
              have := hno s (Finset.mem_filter.1 hs).2
              linarith)
          simp only [Finset.sum_const_zero] at hlt
          have := hfeas j
          linarith
        obtain ⟨s, hs, hsj⟩ := hex
        have hts : Q t j ≤ Q s j := by
          have : (Q t j : ℚ) ≤ (Q s j : ℚ) := by linarith
          exact_mod_cast this
        exact (NNRat.cast_le.2 hts).trans (hle_pv s j hsj)
  have hw : AvgValueAlloc.welfare Q dec ≤ (T : ℝ) * AvgValueAlloc.posValSum ρ Q := by
    unfold AvgValueAlloc.welfare
    calc ∑ t, (dec t).elim 0 (fun j => ((Q t j : ℚ≥0) : ℝ))
        ≤ ∑ _t : Fin T, AvgValueAlloc.posValSum ρ Q := Finset.sum_le_sum (fun t _ => key t)
      _ = (T : ℝ) * AvgValueAlloc.posValSum ρ Q := by simp
  calc ENNReal.ofReal (AvgValueAlloc.welfare Q dec)
      ≤ ENNReal.ofReal ((T : ℝ) * AvgValueAlloc.posValSum ρ Q) := ENNReal.ofReal_le_ofReal hw
    _ = (T : ℝ≥0∞) * ENNReal.ofReal (AvgValueAlloc.posValSum ρ Q) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
