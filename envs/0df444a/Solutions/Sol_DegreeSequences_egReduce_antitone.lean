-- Prove2me | solution 1 for DegreeSequences.egReduce_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:06:13.540934+00:00
-- url     : https://prove2.me/submissions/8eee380f-2ce1-4a9c-96d3-3475e2ad04c6

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {n : ℕ} (d : Fin n → ℕ) (hd : Antitone d) (t p : Fin n) (htp : t < p)
    (hp1 : 1 ≤ d p) (hpz : ∀ i, p < i → d i = 0)
    (htmax : ∀ i, t < i → i < p → d i < d t) : Antitone (egReduce d t p) := by
  intro i j hij
  have hji := hd hij
  have F2 : i = t → j ≠ t → j ≠ p → d j < d i := by
    rintro rfl hjt hjp
    rcases lt_or_gt_of_ne hjp with h | h
    · exact htmax j (lt_of_le_of_ne hij (Ne.symm hjt)) h
    · rw [hpz j h]; have := hd htp.le; omega
  have F3 : i = p → j ≠ p → d j = 0 := by
    rintro rfl hjp
    exact hpz j (lt_of_le_of_ne hij (Ne.symm hjp))
  have F4 : j = t → i ≠ p := by
    rintro rfl rfl
    exact absurd (lt_of_le_of_lt hij htp) (lt_irrefl _)
  have F5 : i = t → i ≠ p := by rintro rfl; exact htp.ne
  have F6 : j = t → j ≠ p := by rintro rfl; exact htp.ne
  unfold egReduce
  split_ifs <;> simp_all <;> omega
end DegreeSequences
