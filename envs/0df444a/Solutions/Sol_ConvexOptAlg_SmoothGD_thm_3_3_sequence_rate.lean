-- Prove2me | solution 1 for ConvexOptAlg.SmoothGD.thm_3_3_sequence_rate
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-06T13:45:38.729981+00:00
-- url     : https://prove2.me/submissions/f883e34e-5458-4e08-9a70-1a2db0e63d24

import Definitions.Def_ConvexOptAlg_SmoothGD_Defs

open ConvexOptAlg.SmoothGD

theorem solution (δ : ℕ → ℝ) (ω : ℝ) (hω : 0 < ω)
    (hδ : ∀ s : ℕ, 1 ≤ s → 0 ≤ δ s)
    (hrec : ∀ s : ℕ, 1 ≤ s → ω * δ s ^ 2 + δ (s + 1) ≤ δ s) (t : ℕ) (ht : 2 ≤ t) :
    ω * ((t : ℝ) - 1) * δ t ≤ 1 := by
  have hm (s : ℕ) (hs : 1 ≤ s) : δ (s + 1) ≤ δ s := by
    nlinarith [hrec s hs, mul_nonneg hω.le (sq_nonneg (δ s))]
  have step (s : ℕ) (hs : 1 ≤ s) (hp : 0 < δ (s + 1)) :
      1 / δ s + ω ≤ 1 / δ (s + 1) := by
    have hspos : 0 < δ s := hp.trans_le (hm s hs)
    calc
      1 / δ s + ω = (1 + ω * δ s) / δ s := by field_simp
      _ ≤ 1 / δ (s + 1) := by
        apply (div_le_div_iff₀ hspos hp).2
        nlinarith [hrec s hs,
          mul_le_mul_of_nonneg_left (hm s hs) (mul_nonneg hω.le hspos.le)]
  have invbound : ∀ s : ℕ, 1 ≤ s → 0 < δ s → ω * ((s : ℝ) - 1) ≤ 1 / δ s := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base =>
        intro hp
        simpa using (one_div_pos.mpr hp).le
    | succ s hs ih =>
        intro hp
        have ih' := ih (hp.trans_le (hm s hs))
        have hh := step s hs hp
        push_cast
        linarith
  by_cases hz : δ t = 0
  · simp [hz]
  · have hp : 0 < δ t := lt_of_le_of_ne (hδ t (by omega)) (Ne.symm hz)
    exact (le_div_iff₀ hp).mp (invbound t (by omega) hp)
