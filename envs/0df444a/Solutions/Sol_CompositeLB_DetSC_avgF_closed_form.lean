-- Prove2me | solution 1 for CompositeLB.DetSC.avgF_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:34:02.571259+00:00
-- url     : https://prove2.me/submissions/65438356-e7bb-4b39-afbc-87ce60f38973

import Mathlib
import Definitions.Def_CompositeLB_DetSC_HardInstance

open CompositeLB.DetSC


theorem solution {m d k : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (lam C zeta : ℝ) (hlam : 0 < lam)
    (v : ℕ → CompositeLB.DetLip.E d) (delta : Fin m → ℕ → ℝ)
    (hdelta : ∀ i r, delta i r = 0 ∨ delta i r = 1)
    (hsum : ∀ r ∈ Finset.Icc 1 k,
      ∑ i : Fin m, delta i r = ((m / 2 : ℕ) : ℝ)) :
    ∀ x : CompositeLB.DetLip.E d,
      hardAvg lam C zeta k v delta x =
        lam * (bigQ m lam - 1) / 8 *
          ((inner ℝ x (v 0)) ^ 2 - 2 * C * inner ℝ x (v 0) +
            zeta * (inner ℝ x (v k)) ^ 2 +
            ∑ r ∈ Finset.Icc 1 k, (inner ℝ x (v (r - 1) - v r)) ^ 2) +
          lam / 2 * ‖x‖ ^ 2 := by
  intro x
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have h1k : 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨le_rfl, hk⟩
  have hkk : k ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨hk, le_rfl⟩
  set h : ℝ := ((m / 2 : ℕ) : ℝ) with hh
  set P : ℝ := (inner ℝ x (v 0)) ^ 2 - 2 * C * inner ℝ x (v 0) with hP
  set Bk : ℝ := (inner ℝ x (v k)) ^ 2 with hBk
  set c : ℕ → ℝ := fun r => (inner ℝ x (v (r - 1) - v r)) ^ 2 with hc
  set N : ℝ := ‖x‖ ^ 2 with hN
  unfold hardAvg CompositeLB.DetLip.avgF hardF
  have e1 : ∑ i : Fin m, delta i 1 * P = h * P := by rw [← Finset.sum_mul, hsum 1 h1k]
  have e2 : ∑ i : Fin m, delta i k * zeta * Bk = h * zeta * Bk := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, hsum k hkk]
  have e3 : ∑ i : Fin m, ∑ r ∈ Finset.Icc 1 k, delta i r * c r = h * ∑ r ∈ Finset.Icc 1 k, c r := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [← Finset.sum_mul, hsum r hr]
  have e4 : ∑ i : Fin m, ((1 - lam) / 8 * (delta i 1 * P + delta i k * zeta * Bk +
      ∑ r ∈ Finset.Icc 1 k, delta i r * c r) + lam / 2 * N)
      = (1 - lam) / 8 * (h * P + h * zeta * Bk + h * ∑ r ∈ Finset.Icc 1 k, c r) + m * (lam / 2 * N) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
      e1, e2, e3, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [e4]
  unfold bigQ
  rw [← hh]
  field_simp
  ring
