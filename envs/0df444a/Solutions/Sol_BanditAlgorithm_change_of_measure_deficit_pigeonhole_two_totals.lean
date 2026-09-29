-- Prove2me | solution 1 for BanditAlgorithm.change_of_measure_deficit_pigeonhole_two_totals
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-04T04:12:01.126474+00:00
-- url     : https://prove2.me/submissions/940be577-1a3b-4b3e-a65e-30f6e0befcc9

import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Chebyshev

open Finset

theorem solution
    {ι : Type*} [Fintype ι] {k : ℕ} (hk : 0 < k) (hcard : Fintype.card ι = k)
    (V Vt W : ι → ℝ) (T0 T0full B : ℝ)
    (hV : ∀ j, 0 ≤ V j) (hsumV : ∑ j, V j = T0full) (hsumVt : ∑ j, Vt j = T0)
    (hB : 0 ≤ B)
    (hW : ∀ j, T0 - Vt j - B * Real.sqrt (2 * V j) ≤ W j) :
    ∃ j : ι,
      (((k : ℝ) - 1) * T0 - B * Real.sqrt (2 * k * T0full)) / k ≤ W j := by
  classical
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hcardR : ((#(Finset.univ : Finset ι) : ℕ) : ℝ) = (k : ℝ) := by
    rw [Finset.card_univ, hcard]
  have hT0full : 0 ≤ T0full := hsumV ▸ Finset.sum_nonneg fun j _ ↦ hV j
  -- Cauchy-Schwarz: `∑ⱼ √(2 V j) ≤ √(2 k T0full)`.
  have hsq : ∑ j, Real.sqrt (2 * V j) ^ 2 = 2 * T0full := by
    have : ∀ j : ι, Real.sqrt (2 * V j) ^ 2 = 2 * V j := fun j ↦
      Real.sq_sqrt (by have := hV j; linarith)
    rw [Finset.sum_congr rfl fun j _ ↦ this j, ← Finset.mul_sum, hsumV]
  have hcs : ∑ j, Real.sqrt (2 * V j) ≤ Real.sqrt (2 * k * T0full) := by
    refine Real.le_sqrt_of_sq_le ?_
    calc (∑ j, Real.sqrt (2 * V j)) ^ 2
        ≤ (#(univ : Finset ι) : ℝ) * ∑ j, Real.sqrt (2 * V j) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ = 2 * k * T0full := by rw [hsq, hcardR]; ring
  -- Sum the hypothesis over `j`: the deficit total telescopes to `(k-1) T0`.
  have hsumW : ((k : ℝ) - 1) * T0 - B * Real.sqrt (2 * k * T0full) ≤ ∑ j, W j := by
    have h1 : ∑ j, (T0 - Vt j - B * Real.sqrt (2 * V j)) ≤ ∑ j, W j :=
      Finset.sum_le_sum fun j _ ↦ hW j
    have h2 : ∑ j, (T0 - Vt j - B * Real.sqrt (2 * V j))
        = ((k : ℝ) - 1) * T0 - B * ∑ j, Real.sqrt (2 * V j) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, hsumVt,
        ← Finset.mul_sum, nsmul_eq_mul, hcardR]
      ring
    have h3 : B * ∑ j, Real.sqrt (2 * V j) ≤ B * Real.sqrt (2 * k * T0full) :=
      mul_le_mul_of_nonneg_left hcs hB
    linarith [h1, h2.symm.le, h2.le]
  -- Pigeonhole.
  have hne : (univ : Finset ι).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ, hcard]; exact hk
  obtain ⟨j, -, hj⟩ :=
    Finset.exists_le_of_sum_le (f := fun _ : ι ↦
      (((k : ℝ) - 1) * T0 - B * Real.sqrt (2 * k * T0full)) / k) (g := W) hne
      (by
        rw [Finset.sum_const, nsmul_eq_mul, hcardR,
          mul_div_cancel₀ _ (ne_of_gt hkR)]
        exact hsumW)
  exact ⟨j, hj⟩
