-- Prove2me | solution 1 for DirectedOpinion.Typical.delta_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:11:32.37477+00:00
-- url     : https://prove2.me/submissions/b750ed03-42b7-4302-9b99-cccfa0d4eb78

import Mathlib
import Definitions.Def_DirectedOpinion_Typical_Model

set_option autoImplicit false
open DirectedOpinion.Typical

theorem solution {V : Type*} (G : WDigraph V) (c d : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hd0 : 0 < d) (hd1 : d ≤ 1) (hcd : c + d ≤ 1) (hG : G.Valid c) (f : V → ℝ) (M : ℝ)
    (hf : ∀ v, |f v| ≤ M) (i : V) :
    |Δ G c d f i| ≤ (1 - d) * M := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hf i)
  have h1 : 0 ≤ 1 - c - d := by linarith
  have hsum : |∑ r ∈ Finset.range (G.deg i), G.wt i r * f (G.nbr i r)| ≤
      ∑ r ∈ Finset.range (G.deg i), G.wt i r * M := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r hr => ?_)
    have hr' : r < G.deg i := Finset.mem_range.mp hr
    have hw := hG.1 i r hr'
    rw [abs_mul, abs_of_nonneg hw.1]
    exact mul_le_mul_of_nonneg_left (hf _) hw.1
  have hS : ∑ r ∈ Finset.range (G.deg i), G.wt i r * M ≤ c * M := by
    rcases Nat.eq_zero_or_pos (G.deg i) with h0 | hpos
    · rw [h0]; simp; positivity
    · rw [← Finset.sum_mul, hG.2 i hpos]
  unfold Δ
  calc |∑ r ∈ Finset.range (G.deg i), G.wt i r * f (G.nbr i r) + (1 - c - d) * f i|
      ≤ |∑ r ∈ Finset.range (G.deg i), G.wt i r * f (G.nbr i r)| + |(1 - c - d) * f i| :=
        abs_add_le _ _
    _ ≤ c * M + (1 - c - d) * M := by
        have : |(1 - c - d) * f i| ≤ (1 - c - d) * M := by
          rw [abs_mul, abs_of_nonneg h1]
          exact mul_le_mul_of_nonneg_left (hf i) h1
        linarith
    _ = (1 - d) * M := by ring
