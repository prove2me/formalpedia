-- Prove2me | solution 1 for BroughanRH.fareyL1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T19:45:51.999955+00:00
-- url     : https://prove2.me/submissions/59824579-e23f-4262-967d-26bd8818bb63
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BroughanRH_fareyL2
import Mathlib

theorem solution :
    let F (N : ℕ) : Finset ℚ := (Finset.Icc 1 N).biUnion fun q =>
      ((Finset.Icc 1 q).filter fun a => Nat.Coprime a q).image fun a : ℕ => (a : ℚ) / q
    let D (N : ℕ) (r : ℚ) : ℝ := (r : ℝ) - (((F N).filter (fun u => u ≤ r)).card : ℝ) / (F N).card
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop (fun N : ℕ => ∑ r ∈ F N, |D N r|) (fun N : ℕ => (N : ℝ)^(1/2 + ε)) := by
  intro F D ε hε
  have h2 := BroughanRH.fareyL2 ε hε
  simp only at h2
  -- card bound
  have hcard : ∀ N : ℕ, ((F N).card : ℝ) ≤ (N : ℝ)^2 := by
    intro N
    have h1 : (F N).card ≤ ∑ q ∈ Finset.Icc 1 N, (((Finset.Icc 1 q).filter fun a => Nat.Coprime a q).image fun a : ℕ => (a : ℚ) / q).card :=
      Finset.card_biUnion_le
    have h3 : ∀ q ∈ Finset.Icc 1 N, (((Finset.Icc 1 q).filter fun a => Nat.Coprime a q).image fun a : ℕ => (a : ℚ) / q).card ≤ N := by
      intro q hq
      refine (Finset.card_image_le).trans ((Finset.card_filter_le _ _).trans ?_)
      simp only [Nat.card_Icc, add_tsub_cancel_right]
      exact (Finset.mem_Icc.mp hq).2
    have h4 := (h1.trans (Finset.sum_le_sum h3))
    simp only [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, smul_eq_mul] at h4
    have : ((F N).card : ℝ) ≤ ((N * N : ℕ) : ℝ) := by exact_mod_cast h4
    simpa [sq] using this
  obtain ⟨C, hC⟩ := h2.bound
  rw [Filter.eventually_atTop] at hC
  obtain ⟨N0, hN0⟩ := hC
  refine Asymptotics.IsBigO.of_bound (Real.sqrt (max C 0)) ?_
  rw [Filter.eventually_atTop]
  refine ⟨max N0 1, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hb := hN0 N (le_of_max_le_left hN)
  -- Cauchy–Schwarz
  have hcs : (∑ r ∈ F N, |D N r|)^2 ≤ ((F N).card : ℝ) * ∑ r ∈ F N, (D N r)^2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (F N) (fun _ => (1 : ℝ)) (fun r => |D N r|)
    simpa [sq_abs] using this
  have hsq_nonneg : 0 ≤ ∑ r ∈ F N, (D N r)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS : ∑ r ∈ F N, (D N r)^2 ≤ max C 0 * (N : ℝ)^(-1 + ε) := by
    have hp : 0 < (N : ℝ)^(-1 + ε) := Real.rpow_pos_of_pos hNpos _
    rw [Real.norm_of_nonneg hsq_nonneg, Real.norm_of_nonneg hp.le] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le)
  have hA : 0 ≤ ∑ r ∈ F N, |D N r| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hpow : (N : ℝ)^2 * (N : ℝ)^(-1 + ε) = ((N : ℝ)^(1/2 + ε/2))^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hNpos, ← Real.rpow_mul hNpos.le]
    norm_num; ring_nf
  have hkey : (∑ r ∈ F N, |D N r|)^2 ≤ (Real.sqrt (max C 0) * (N : ℝ)^(1/2 + ε/2))^2 := by
    rw [mul_pow, Real.sq_sqrt (le_max_right _ _), ← hpow]
    calc _ ≤ ((F N).card : ℝ) * ∑ r ∈ F N, (D N r)^2 := hcs
      _ ≤ (N : ℝ)^2 * (max C 0 * (N : ℝ)^(-1 + ε)) :=
          mul_le_mul (hcard N) hS hsq_nonneg (by positivity)
      _ = _ := by ring
  have h3 : ∑ r ∈ F N, |D N r| ≤ Real.sqrt (max C 0) * (N : ℝ)^(1/2 + ε/2) :=
    (sq_le_sq₀ hA (by positivity)).mp hkey
  have h4 : (N : ℝ)^(1/2 + ε/2) ≤ (N : ℝ)^(1/2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  rw [Real.norm_of_nonneg hA, Real.norm_of_nonneg (Real.rpow_pos_of_pos hNpos _).le]
  exact h3.trans (mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _))
