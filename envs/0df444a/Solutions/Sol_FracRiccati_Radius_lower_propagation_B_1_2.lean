-- Prove2me | solution 1 for FracRiccati.Radius.lower_propagation_B_1_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:25:14.980317+00:00
-- url     : https://prove2.me/submissions/c379ad22-327b-4fac-a2ba-8d0ba4cc7b6b

import Mathlib
import Definitions.Def_FracRiccati_Radius_Coeff
import Theorems.Thm_FracRiccati_Radius_prop_B_1_a
import Theorems.Thm_FracRiccati_Radius_prop_B_1_b
import Theorems.Thm_FracRiccati_Radius_kershaw_A_41

namespace Aux_FRR_B12
open FracRiccati.Radius

lemma eq_of_log_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : Real.log x = Real.log y) : x = y :=
  Real.log_injOn_pos (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hy) h

/-- Gamma factor of (B.50), via Kershaw's lower bound with `x = 2αk`, `s = α`. -/
lemma gamma_lower (α k : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hk : 0 < k) :
    (2 * α * k + α / 2) ^ (1 - α) / (α * (2 * k + 1)) ≤
      Real.Gamma (2 * α * k + 1) / Real.Gamma ((2 * k + 1) * α + 1) := by
  have hx : 0 < 2 * α * k := by positivity
  have hpos : 0 < (2 * k + 1) * α := by positivity
  have e1 : Real.Gamma ((2 * k + 1) * α + 1) = (α * (2 * k + 1)) * Real.Gamma (2 * α * k + α) := by
    rw [Real.Gamma_add_one hpos.ne']; congr 1 <;> ring_nf
  have hGx : 0 < Real.Gamma (2 * α * k + α) := Real.Gamma_pos_of_pos (by linarith)
  have hK : (2 * α * k + α / 2) ^ (1 - α) ≤
      Real.Gamma (2 * α * k + 1) / Real.Gamma (2 * α * k + α) := by
    rcases eq_or_lt_of_le hα1 with h | h
    · subst h
      rw [div_self (Real.Gamma_pos_of_pos (by positivity)).ne']; simp
    · exact (kershaw_A_41 (2 * α * k) α hx hα0 h).1.le
  rw [e1, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [le_div_iff₀ hGx] at hK
  nlinarith [hK, show 0 < α * (2 * k + 1) by positivity]

end Aux_FRR_B12

open FracRiccati.Radius Aux_FRR_B12 in
theorem solution (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (l n : ℝ) (hl : 0 < l) (hn : 0 < n) :
    let ρ : ℝ := (5 : ℝ) ^ (1 - α) / 3 * α ^ (-α) * (l * n) / Real.Gamma (α + 1)
    let c : ℝ := n / (ρ * α * Real.Gamma α)
    ∀ k : ℕ, 1 ≤ k → c * ρ ^ k * (k : ℝ) ^ (α - 1) ≤ (coeff α l 0 n (2 * k - 1)).re := by
  intro ρ c
  have hα2 : α ≤ 2 := by linarith
  have hG : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα0
  have hG1 : 0 < Real.Gamma (α + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hGa : Real.Gamma (α + 1) = α * Real.Gamma α := Real.Gamma_add_one hα0.ne'
  have hρ : 0 < ρ := by positivity
  have hc : 0 < c := by positivity
  have hcρ : c * ρ = n / Real.Gamma (α + 1) := by
    show n / (ρ * α * Real.Gamma α) * ρ = _
    rw [hGa]; field_simp
  have hlc : l * c = 3 * (5 : ℝ) ^ (α - 1) * α ^ α := by
    show l * (n / (((5 : ℝ) ^ (1 - α) / 3 * α ^ (-α) * (l * n) / Real.Gamma (α + 1)) * α *
      Real.Gamma α)) = _
    rw [show (1 - α) = -(α - 1) by ring, Real.rpow_neg (by norm_num), Real.rpow_neg hα0.le, hGa]
    have : 0 < (5 : ℝ) ^ (α - 1) := by positivity
    have : 0 < α ^ α := by positivity
    field_simp
  clear_value ρ c
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨-, -, hb1, hrec⟩ := prop_B_1_a α hα0 (l : ℂ) (n : ℂ) hl0 hn0
  have hreal := (prop_B_1_b α hα0 hα2 l 0 n hl.le le_rfl hn.le).1
  set B : ℕ → ℝ := fun k => (coeff α l 0 n (2 * k - 1)).re with hBdef
  have hz : ∀ k, 1 ≤ k → coeff α l 0 n (2 * k - 1) = ((B k : ℝ) : ℂ) := by
    intro k hk
    exact Complex.ext (by simp [hBdef]) (by simp [hBdef, (hreal (2 * k - 1) (by omega)).2.1])
  have hB0 : ∀ k, 1 ≤ k → 0 ≤ B k := fun k hk => (hreal (2 * k - 1) (by omega)).2.2.2
  have hrecR : ∀ k, 1 ≤ k → B (k + 1) =
      l * (Real.Gamma (2 * α * k + 1) / Real.Gamma ((2 * k + 1) * α + 1)) *
        ∑ ℓ ∈ Finset.Ico 1 (k + 1), B ℓ * B (k + 1 - ℓ) := by
    intro k hk
    have h := hrec k hk
    have hs : ∑ ℓ ∈ Finset.Ico 1 (k + 1),
        coeff α (l : ℂ) 0 (n : ℂ) (2 * ℓ - 1) * coeff α (l : ℂ) 0 (n : ℂ) (2 * (k + 1 - ℓ) - 1) =
        ((∑ ℓ ∈ Finset.Ico 1 (k + 1), B ℓ * B (k + 1 - ℓ) : ℝ) : ℂ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      rw [Finset.mem_Ico] at hℓ
      rw [hz ℓ (by omega), hz (k + 1 - ℓ) (by omega)]
    rw [hs] at h
    have := congrArg Complex.re h
    rw [hBdef]
    simp only at this ⊢
    rw [this]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain rfl : k = 1 := by omega
      have : B 1 = n / Real.Gamma (α + 1) := by
        rw [hBdef]; simp only
        rw [hb1, ← Complex.ofReal_div, Complex.ofReal_re]
      show c * ρ ^ 1 * ((1 : ℕ) : ℝ) ^ (α - 1) ≤ B 1
      rw [this, pow_one, Nat.cast_one, Real.one_rpow, mul_one, hcρ]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj : 1 ≤ j := by omega
      show c * ρ ^ (j + 1) * ((j + 1 : ℕ) : ℝ) ^ (α - 1) ≤ B (j + 1)
      rw [hrecR j hj]
      set K : ℝ := ((j + 1 : ℕ) : ℝ) with hK
      have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
      have hKj : K = (j : ℝ) + 1 := by rw [hK]; push_cast; ring
      have hK0 : (0 : ℝ) < K := by linarith
      set Q : ℝ := ((K / 2) ^ 2) ^ (α - 1) with hQ
      have hQpos : 0 < Q := by positivity
      -- convolution lower bound
      have hsum : (j : ℝ) * (c ^ 2 * ρ ^ (j + 1) * Q) ≤
          ∑ ℓ ∈ Finset.Ico 1 (j + 1), B ℓ * B (j + 1 - ℓ) := by
        have hcard : ∑ ℓ ∈ Finset.Ico 1 (j + 1), c ^ 2 * ρ ^ (j + 1) * Q =
            (j : ℝ) * (c ^ 2 * ρ ^ (j + 1) * Q) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]; congr 1
        rw [← hcard]
        apply Finset.sum_le_sum
        intro ℓ hℓ
        rw [Finset.mem_Ico] at hℓ
        have i1 := ih ℓ (by omega) (by omega)
        have i2 := ih (j + 1 - ℓ) (by omega) (by omega)
        have hcast : ((j + 1 - ℓ : ℕ) : ℝ) = K - ℓ := by rw [hK, Nat.cast_sub (by omega)]
        rw [hcast] at i2
        have hℓ0 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.1
        have hℓK : (ℓ : ℝ) + 1 ≤ K := by rw [hK]; exact_mod_cast hℓ.2
        have hker : Q ≤ (ℓ : ℝ) ^ (α - 1) * (K - ℓ) ^ (α - 1) := by
          rw [← Real.mul_rpow (by linarith) (by linarith), hQ]
          exact Real.rpow_le_rpow_of_nonpos (by nlinarith) (by nlinarith [sq_nonneg (K - 2 * ℓ)])
            (by linarith)
        have hρs : ρ ^ ℓ * ρ ^ (j + 1 - ℓ) = ρ ^ (j + 1) := by
          rw [← pow_add]; congr 1; omega
        calc c ^ 2 * ρ ^ (j + 1) * Q
            ≤ c ^ 2 * ρ ^ (j + 1) * ((ℓ : ℝ) ^ (α - 1) * (K - ℓ) ^ (α - 1)) :=
              mul_le_mul_of_nonneg_left hker (by positivity)
          _ = (c * ρ ^ ℓ * (ℓ : ℝ) ^ (α - 1)) * (c * ρ ^ (j + 1 - ℓ) * (K - ℓ) ^ (α - 1)) := by
              rw [← hρs]; ring
          _ ≤ B ℓ * B (j + 1 - ℓ) :=
              mul_le_mul i1 i2 (by have : (0:ℝ) ≤ K - ℓ := by linarith
                                   positivity) (hB0 ℓ (by omega))
      have hg := gamma_lower α j hα0 hα1 (by linarith)
      -- the key numerical inequality
      have hW : (5 : ℝ) ^ (α - 1) * α ^ α * ((2 * α * j + α / 2) ^ (1 - α) * Q) =
          α * ((8 * j + 2) / (5 * K)) ^ (1 - α) * K ^ (α - 1) := by
        apply eq_of_log_eq (by positivity) (by positivity)
        have h1 : 0 < 2 * α * (j : ℝ) + α / 2 := by positivity
        have h2 : 0 < (8 * (j : ℝ) + 2) / (5 * K) := by positivity
        rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
          Real.log_rpow hα0, Real.log_rpow h1, hQ, Real.log_rpow (by positivity),
          Real.log_rpow h2, Real.log_rpow hK0, Real.log_pow, Real.log_div hK0.ne' (by norm_num),
          Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) hK0.ne',
          show 2 * α * (j : ℝ) + α / 2 = α * ((8 * j + 2) / 4) by ring,
          Real.log_mul hα0.ne' (by positivity), Real.log_div (by positivity) (by norm_num),
          show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        ring
      have hfac1 : 1 ≤ 3 * (j : ℝ) / (2 * j + 1) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have hfac2 : 1 ≤ ((8 * (j : ℝ) + 2) / (5 * K)) ^ (1 - α) := by
        apply Real.one_le_rpow _ (by linarith)
        rw [le_div_iff₀ (by positivity), hKj]; linarith
      have hKa : 0 < K ^ (α - 1) := by positivity
      have hgpos : 0 ≤ (2 * α * j + α / 2) ^ (1 - α) / (α * (2 * j + 1)) := by positivity
      calc c * ρ ^ (j + 1) * K ^ (α - 1)
          ≤ c * ρ ^ (j + 1) * K ^ (α - 1) *
              ((3 * (j : ℝ) / (2 * j + 1)) * ((8 * (j : ℝ) + 2) / (5 * K)) ^ (1 - α)) := by
            have : 1 ≤ (3 * (j : ℝ) / (2 * j + 1)) * ((8 * (j : ℝ) + 2) / (5 * K)) ^ (1 - α) := by
              nlinarith
            nlinarith [mul_pos (mul_pos hc (pow_pos hρ (j + 1))) hKa]
        _ = l * ((2 * α * j + α / 2) ^ (1 - α) / (α * (2 * j + 1))) *
              ((j : ℝ) * (c ^ 2 * ρ ^ (j + 1) * Q)) := by
            have hW' := hW
            have e : l * ((2 * α * j + α / 2) ^ (1 - α) / (α * (2 * j + 1))) *
                ((j : ℝ) * (c ^ 2 * ρ ^ (j + 1) * Q)) =
                (l * c) * c * ρ ^ (j + 1) * (j : ℝ) / (α * (2 * j + 1)) *
                  ((2 * α * j + α / 2) ^ (1 - α) * Q) := by ring
            rw [e, hlc]
            have e2 : 3 * (5 : ℝ) ^ (α - 1) * α ^ α * c * ρ ^ (j + 1) * (j : ℝ) / (α * (2 * j + 1)) *
                ((2 * α * j + α / 2) ^ (1 - α) * Q) =
                3 * c * ρ ^ (j + 1) * (j : ℝ) / (α * (2 * j + 1)) *
                  ((5 : ℝ) ^ (α - 1) * α ^ α * ((2 * α * j + α / 2) ^ (1 - α) * Q)) := by ring
            rw [e2, hW]
            field_simp
        _ ≤ l * (Real.Gamma (2 * α * j + 1) / Real.Gamma ((2 * j + 1) * α + 1)) *
              ∑ ℓ ∈ Finset.Ico 1 (j + 1), B ℓ * B (j + 1 - ℓ) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hg hl.le) hsum (by positivity)
            exact mul_nonneg hl.le (le_trans hgpos hg)
