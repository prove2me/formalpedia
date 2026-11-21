-- Prove2me | solution 1 for DQI.Semicircle.eq_129
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:10:22.709156+00:00
-- url     : https://prove2.me/submissions/ad59895b-58ee-4cfe-9116-16ce94fac608

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace Aux_DQI_Semicircle_eq_129

open DQI.Semicircle

/-- AM-GM in the form `2 s ℓ √(X Y) ≤ s² X + ℓ² Y`. -/
lemma amgm (s l X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    2 * s * l * Real.sqrt (X * Y) ≤ s ^ 2 * X + l ^ 2 * Y := by
  rw [Real.sqrt_mul hX]
  have h := two_mul_le_add_sq (s * Real.sqrt X) (l * Real.sqrt Y)
  rw [mul_pow, mul_pow, Real.sq_sqrt hX, Real.sq_sqrt hY] at h
  linarith

end Aux_DQI_Semicircle_eq_129

open Aux_DQI_Semicircle_eq_129 in
open DQI.Semicircle in
theorem solution (m ℓ : ℕ) (dpar : ℝ) (hℓ : 1 ≤ ℓ) (hℓm : 2 * ℓ ≤ m)
    (hd : -((m : ℝ) - 2 * ℓ) / Real.sqrt (ℓ * ((m : ℝ) - ℓ)) ≤ dpar) :
    ∀ t ∈ spectrum ℝ (Atri m ℓ dpar),
      t ≤ 2 * Real.sqrt m + ℓ * dpar + 2 * Real.sqrt (ℓ * ((m : ℝ) - ℓ)) := by
  intro t ht
  have hev : Module.End.HasEigenvalue (Matrix.toLin' (Atri m ℓ dpar)) t := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin']
    exact ht
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball hev
  rw [Metric.mem_closedBall, Real.dist_eq] at hi
  have hti : t ≤ Atri m ℓ dpar i i + ∑ j ∈ Finset.univ.erase i, ‖Atri m ℓ dpar i j‖ := by
    have := le_abs_self (t - Atri m ℓ dpar i i)
    linarith
  have hdiag : Atri m ℓ dpar i i = ((i : ℕ) : ℝ) * dpar := by
    simp [Atri]
  have hiℓ : (i : ℕ) ≤ ℓ := by have := i.isLt; omega
  -- the radius
  have hpt : ∀ j ∈ Finset.univ.erase i, ‖Atri m ℓ dpar i j‖ ≤
      (if (j : ℕ) = (i : ℕ) + 1 then Real.sqrt (((i : ℕ) + 1 : ℝ) * ((m : ℝ) - (i : ℕ))) else 0) +
      (if (i : ℕ) = (j : ℕ) + 1 then Real.sqrt (((i : ℕ) : ℝ) * ((m : ℝ) - (i : ℕ) + 1)) else 0) := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hji' : (i : ℕ) ≠ (j : ℕ) := fun h => hji (Fin.ext h.symm)
    simp only [Atri, if_neg hji']
    by_cases h1 : (j : ℕ) = (i : ℕ) + 1
    · rw [if_pos h1, if_pos h1, if_neg (show ¬ ((i : ℕ) = (j : ℕ) + 1) by omega),
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), add_zero]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : (i : ℕ) = (j : ℕ) + 1
      · rw [if_pos h2, if_pos h2, zero_add, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
        have hj' : ((j : ℕ) : ℝ) = ((i : ℕ) : ℝ) - 1 := by
          rw [h2]; push_cast; ring
        rw [hj']
        apply le_of_eq
        congr 1
        ring
      · rw [if_neg h2, if_neg h2]
        simp
  have hPsum : ∑ j : Fin (ℓ + 1),
      (if (j : ℕ) = (i : ℕ) + 1 then Real.sqrt (((i : ℕ) + 1 : ℝ) * ((m : ℝ) - (i : ℕ))) else 0) =
      if (i : ℕ) + 1 ≤ ℓ then Real.sqrt (((i : ℕ) + 1 : ℝ) * ((m : ℝ) - (i : ℕ))) else 0 := by
    by_cases h : (i : ℕ) + 1 ≤ ℓ
    · rw [if_pos h, Finset.sum_eq_single (⟨(i : ℕ) + 1, by omega⟩ : Fin (ℓ + 1))]
      · rw [if_pos]
        rfl
      · intro j _ hj
        rw [if_neg]
        intro hc
        exact hj (Fin.ext hc)
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg]
      intro hc
      have := j.isLt
      omega
  have hQsum : ∑ j : Fin (ℓ + 1),
      (if (i : ℕ) = (j : ℕ) + 1 then Real.sqrt (((i : ℕ) : ℝ) * ((m : ℝ) - (i : ℕ) + 1)) else 0) =
      if 1 ≤ (i : ℕ) then Real.sqrt (((i : ℕ) : ℝ) * ((m : ℝ) - (i : ℕ) + 1)) else 0 := by
    by_cases h : 1 ≤ (i : ℕ)
    · rw [if_pos h, Finset.sum_eq_single (⟨(i : ℕ) - 1, by omega⟩ : Fin (ℓ + 1))]
      · rw [if_pos]
        show (i : ℕ) = (i : ℕ) - 1 + 1
        omega
      · intro j _ hj
        rw [if_neg]
        intro hc
        apply hj
        apply Fin.ext
        show (j : ℕ) = (i : ℕ) - 1
        omega
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg]
      intro hc
      omega
  have hR : ∑ j ∈ Finset.univ.erase i, ‖Atri m ℓ dpar i j‖ ≤
      (if (i : ℕ) + 1 ≤ ℓ then Real.sqrt (((i : ℕ) + 1 : ℝ) * ((m : ℝ) - (i : ℕ))) else 0) +
      (if 1 ≤ (i : ℕ) then Real.sqrt (((i : ℕ) : ℝ) * ((m : ℝ) - (i : ℕ) + 1)) else 0) := by
    calc ∑ j ∈ Finset.univ.erase i, ‖Atri m ℓ dpar i j‖
        ≤ ∑ j ∈ Finset.univ.erase i,
          ((if (j : ℕ) = (i : ℕ) + 1 then
              Real.sqrt (((i : ℕ) + 1 : ℝ) * ((m : ℝ) - (i : ℕ))) else 0) +
            (if (i : ℕ) = (j : ℕ) + 1 then
              Real.sqrt (((i : ℕ) : ℝ) * ((m : ℝ) - (i : ℕ) + 1)) else 0)) :=
          Finset.sum_le_sum hpt
      _ ≤ ∑ j : Fin (ℓ + 1),
          ((if (j : ℕ) = (i : ℕ) + 1 then
              Real.sqrt (((i : ℕ) + 1 : ℝ) * ((m : ℝ) - (i : ℕ))) else 0) +
            (if (i : ℕ) = (j : ℕ) + 1 then
              Real.sqrt (((i : ℕ) : ℝ) * ((m : ℝ) - (i : ℕ) + 1)) else 0)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          intro j _ _
          apply add_nonneg
          · split_ifs
            · exact Real.sqrt_nonneg _
            · exact le_rfl
          · split_ifs
            · exact Real.sqrt_nonneg _
            · exact le_rfl
      _ = _ := by rw [Finset.sum_add_distrib, hPsum, hQsum]
  -- real-number facts
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = ((i : ℕ) : ℝ) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hxℓ : x ≤ ℓ := by rw [hx]; exact_mod_cast hiℓ
  have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓmR : 2 * (ℓ : ℝ) ≤ m := by exact_mod_cast hℓm
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (ℓ * ((m : ℝ) - ℓ)) := ⟨_, rfl⟩
  have hprod : 0 < (ℓ : ℝ) * ((m : ℝ) - ℓ) :=
    mul_pos (by linarith) (by linarith)
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hprod
  have hs2 : s ^ 2 = ℓ * ((m : ℝ) - ℓ) := by rw [hs]; exact Real.sq_sqrt hprod.le
  obtain ⟨M, hM⟩ : ∃ M, M = Real.sqrt (m : ℝ) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; exact Real.sqrt_nonneg _
  have hM2 : M ^ 2 = m := by rw [hM]; exact Real.sq_sqrt (by positivity)
  rw [← hs, ← hM]
  rw [← hs] at hd
  have F3 : -((m : ℝ) - 2 * ℓ) ≤ dpar * s := (div_le_iff₀ hs0).mp hd
  have hsM : M ≤ 2 * s := by
    have h1 : M ^ 2 ≤ 4 * s ^ 2 := by
      rw [hM2, hs2]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ ℓ - 1) (by linarith : (0:ℝ) ≤ m - ℓ)]
    nlinarith
  have F5 : (m : ℝ) ≤ 4 * s * M := by
    nlinarith [mul_le_mul_of_nonneg_left hsM hM0, mul_nonneg hs0.le hM0]
  have F2 : 2 * s * ℓ *
      (if (i : ℕ) + 1 ≤ ℓ then Real.sqrt (((i : ℕ) + 1 : ℝ) * ((m : ℝ) - (i : ℕ))) else 0) ≤
      ℓ * ((m : ℝ) - ℓ) * (x + 1) + (ℓ : ℝ) ^ 2 * ((m : ℝ) - x) := by
    split_ifs
    · have := amgm s ℓ (((i : ℕ) + 1 : ℝ)) ((m : ℝ) - (i : ℕ)) (by positivity) (by rw [← hx]; linarith)
      rw [hs2, ← hx] at this
      rw [← hx]
      linarith
    · have : 0 ≤ (ℓ : ℝ) * ((m : ℝ) - ℓ) * (x + 1) := by
        apply mul_nonneg hprod.le; linarith
      have : 0 ≤ (ℓ : ℝ) ^ 2 * ((m : ℝ) - x) := by
        apply mul_nonneg (by positivity); linarith
      linarith
  have F1 : 2 * s * ℓ *
      (if 1 ≤ (i : ℕ) then Real.sqrt (((i : ℕ) : ℝ) * ((m : ℝ) - (i : ℕ) + 1)) else 0) ≤
      ℓ * ((m : ℝ) - ℓ) * x + (ℓ : ℝ) ^ 2 * ((m : ℝ) - x + 1) := by
    split_ifs
    · have := amgm s ℓ (((i : ℕ) : ℝ)) ((m : ℝ) - (i : ℕ) + 1) (by positivity) (by rw [← hx]; linarith)
      rw [hs2, ← hx] at this
      rw [← hx]
      linarith
    · have : 0 ≤ (ℓ : ℝ) * ((m : ℝ) - ℓ) * x := mul_nonneg hprod.le hx0
      have : 0 ≤ (ℓ : ℝ) ^ 2 * ((m : ℝ) - x + 1) := by
        apply mul_nonneg (by positivity); linarith
      linarith
  have F3' : 2 * ℓ * (ℓ - x) * (-((m : ℝ) - 2 * ℓ)) ≤ 2 * ℓ * (ℓ - x) * (dpar * s) :=
    mul_le_mul_of_nonneg_left F3 (mul_nonneg (by linarith) (by linarith))
  have F5' : (ℓ : ℝ) * m ≤ ℓ * (4 * s * M) := mul_le_mul_of_nonneg_left F5 (by linarith)
  have hs2' : s * s * ℓ = ℓ * (ℓ * ((m : ℝ) - ℓ)) := by rw [← sq, hs2]; ring
  obtain ⟨BP, hBP⟩ : ∃ B, B =
      (if (i : ℕ) + 1 ≤ ℓ then Real.sqrt (((i : ℕ) + 1 : ℝ) * ((m : ℝ) - (i : ℕ))) else 0) :=
    ⟨_, rfl⟩
  obtain ⟨BQ, hBQ⟩ : ∃ B, B =
      (if 1 ≤ (i : ℕ) then Real.sqrt (((i : ℕ) : ℝ) * ((m : ℝ) - (i : ℕ) + 1)) else 0) :=
    ⟨_, rfl⟩
  rw [← hBP] at F2 hR
  rw [← hBQ] at F1 hR
  rw [hdiag, ← hx] at hti
  have key : 2 * s * ℓ * (x * dpar + (BP + BQ)) ≤
      2 * s * ℓ * (2 * M + ℓ * dpar + 2 * s) := by
    nlinarith
  have h2sl : 0 < 2 * s * ℓ := mul_pos (mul_pos two_pos hs0) (by linarith)
  have := le_of_mul_le_mul_left key h2sl
  linarith
