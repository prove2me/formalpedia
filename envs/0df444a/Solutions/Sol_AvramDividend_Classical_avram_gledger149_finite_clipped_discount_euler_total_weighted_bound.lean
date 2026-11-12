-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger149_finite_clipped_discount_euler_total_weighted_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:15:41.783743+00:00
-- url     : https://prove2.me/submissions/38e74a8e-882f-438a-96a9-4a2c7d903ddb

import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_avram_gledger146_finite_discount_Euler_cell_absolute_aggregation
import Theorems.Thm_AvramDividend_Classical_avram_gledger148_weighted_clipped_discount_euler_boundary_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section
theorem solution
    (m : ℕ) (q δ K t r a : ℝ) (s weight : ℕ → ℝ)
    (hq : 0 ≤ q) (ht : 0 ≤ t) (hr : 0 ≤ r) (hrδ : r ≤ δ)
    (hK : 0 ≤ K) (ha : |a| ≤ K)
    (hw : ∀ i ∈ Finset.range m, |weight i| ≤ K)
    (hcell : ∀ i ∈ Finset.range m,
      |Real.exp (-(q * (s i + δ))) - Real.exp (-(q * s i)) + q * δ * Real.exp (-(q * s i))| ≤ (q * δ) ^ 2) :
    |Finset.sum (Finset.range m) (fun i => (Real.exp (-(q * (s i + δ))) - Real.exp (-(q * s i)) + q * δ * Real.exp (-(q * s i))) * weight i) +
      (Real.exp (-(q * (t + r))) - Real.exp (-(q * t)) + q * δ * Real.exp (-(q * t))) * a| ≤
      (m : ℝ) * ((q * δ) ^ 2 * K) + 2 * q * δ * K := by
  have hsum :=
    AvramDividend.Classical.avram_gledger146_finite_discount_Euler_cell_absolute_aggregation
      m q δ K s weight hK hw hcell
  have hlast :=
    AvramDividend.Classical.avram_gledger148_weighted_clipped_discount_euler_boundary_bound
      q t r δ a K hq ht hr hrδ hK ha
  exact (abs_add_le _ _).trans (add_le_add hsum hlast)
