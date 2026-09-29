-- Prove2me | solution 1 for DFT.ks_density_normalization
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:37:06.564219+00:00
-- url     : https://prove2.me/submissions/021bd1dc-6153-4082-9fc0-862019225716

import Definitions.Def_DFT_HohenbergKohn

open MeasureTheory
open DFT

theorem solution {N : ℕ} (φ : Fin N → Pos → ℂ)
    (hmem : ∀ i, MemLp (φ i) 2 volume)
    (horth : ∀ i j, ∫ r : Pos, (starRingEnd ℂ) (φ i r) * φ j r = if i = j then 1 else 0) :
    ∫ r : Pos, ∑ i, ‖φ i r‖ ^ 2 = (N : ℝ) := by
  rw [integral_finset_sum _ (fun i _ => (hmem i).integrable_norm_pow (by norm_num))]
  have : ∀ i, ∫ r : Pos, ‖φ i r‖ ^ 2 = 1 := by
    intro i
    have h := horth i i
    simp only [if_true] at h
    have h2 : ∀ r, (starRingEnd ℂ) (φ i r) * φ i r = ((‖φ i r‖ ^ 2 : ℝ) : ℂ) := by
      intro r
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [h2] at h
    rw [integral_complex_ofReal] at h
    exact_mod_cast h
  simp [this]
