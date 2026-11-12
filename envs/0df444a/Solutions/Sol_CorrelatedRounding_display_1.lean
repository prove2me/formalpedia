-- Prove2me | solution 1 for CorrelatedRounding.display_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T20:48:26.336121+00:00
-- url     : https://prove2.me/submissions/26f965e2-e0ec-447e-aaa2-a35e9af53a8a

import Mathlib
import Definitions.Def_CorrelatedRounding_IsInstance
import Definitions.Def_CorrelatedRounding_y
import Definitions.Def_CorrelatedRounding_clock
import Definitions.Def_CorrelatedRounding_IsAlg1Output

open CorrelatedRounding in
theorem solution {q K : ℕ} {u : Fin K → Fin q → ℝ} (hu : IsInstance u) {E : Fin K → ℝ}
    {z : Fin q → Fin K} (hz : IsAlg1Output u E z) (k : Fin K) (S : ℕ → ℝ) (hS : StrictMono S)
    (hS0 : S 0 = E k) (i : Fin q) :
    (z i = k → 0 < u k i) ∧
      (0 < u k i → z i = k → ∀ k', clock u E k i ≤ clock u E k' i) ∧
      (0 < u k i → ((∀ k', clock u E k i ≤ clock u E k' i) ↔
        ∀ k', k' ≠ k → ((y u k / u k i * S 0 : ℝ) : EReal) ≤ clock u E k' i)) ∧
      (0 < u k i → ((∀ k', k' ≠ k → ((y u k / u k i * S 0 : ℝ) : EReal) ≤ clock u E k' i) ↔
        ∃ j, (∀ k', k' ≠ k → ((y u k / u k i * S j : ℝ) : EReal) ≤ clock u E k' i) ∧
          ∀ j' < j, y u k / u k i * S j ≤ y u k / u k i * S j')) := by
  have hyi : u k i ≤ y u k := by
    unfold y
    exact le_ciSup (Set.finite_range _).bddAbove i
  refine ⟨fun hzi => ?_, fun _ hzi k' => ?_, fun hpos => ?_, fun hpos => ?_⟩
  · by_contra hneg
    have hz0 : u k i = 0 := le_antisymm (not_lt.mp hneg) (hu.1 k i)
    obtain ⟨k', hk'⟩ : ∃ k', u k' i ≠ 0 := by
      by_contra hall
      push_neg at hall
      have h1 := hu.2 i
      simp [hall] at h1
    have h := hz i k'
    rw [hzi] at h
    unfold clock at h
    rw [if_pos hz0, if_neg hk'] at h
    exact EReal.coe_ne_top _ (top_le_iff.mp h)
  · have h := hz i k'
    rwa [hzi] at h
  · have hck : clock u E k i = ((y u k / u k i * S 0 : ℝ) : EReal) := by
      unfold clock
      rw [if_neg hpos.ne', hS0]
    constructor
    · intro h k' _
      rw [← hck]
      exact h k'
    · intro h k'
      by_cases hk : k' = k
      · subst hk
        exact le_rfl
      · rw [hck]
        exact h k' hk
  · have hc : 0 ≤ y u k / u k i := div_nonneg (le_trans hpos.le hyi) hpos.le
    constructor
    · intro h
      exact ⟨0, h, fun j' hj' => absurd hj' (Nat.not_lt_zero _)⟩
    · rintro ⟨j, hj, _⟩ k' hk'
      exact le_trans (EReal.coe_le_coe_iff.mpr
        (mul_le_mul_of_nonneg_left (hS.monotone (Nat.zero_le j)) hc)) (hj k' hk')
