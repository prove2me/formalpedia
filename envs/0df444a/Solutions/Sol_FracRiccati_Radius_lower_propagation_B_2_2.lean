-- Prove2me | solution 1 for FracRiccati.Radius.lower_propagation_B_2_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:09:48.438771+00:00
-- url     : https://prove2.me/submissions/402a5022-9dd1-43fb-a080-ed61f336cd12

import Mathlib
import Definitions.Def_FracRiccati_Radius_Coeff
import Definitions.Def_FracRiccati_Radius_Constants
import Theorems.Thm_FracRiccati_Radius_prop_B_1_a
import Theorems.Thm_FracRiccati_Radius_prop_B_1_b
import Theorems.Thm_FracRiccati_Radius_riemann_sum_B_52

namespace Aux_FRR_B22

/-- Wendel-type upper bound from log-convexity: `Γ(x+s) ≤ x^s Γ(x)` for `s ∈ (0,1]`. -/
lemma gamma_upper (x s : ℝ) (hx : 0 < x) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    Real.Gamma (x + s) ≤ x ^ s * Real.Gamma x := by
  have hG : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  rcases eq_or_lt_of_le hs1 with h | h
  · subst h; rw [Real.rpow_one, Real.Gamma_add_one hx.ne']
  · have key := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := x) (t := x + 1)
      (a := 1 - s) (b := s) hx (by linarith) (by linarith) hs0 (by ring)
    have e1 : (1 - s) * x + s * (x + 1) = x + s := by ring
    rw [e1, Real.Gamma_add_one hx.ne', Real.mul_rpow hx.le hG.le] at key
    calc Real.Gamma (x + s) ≤ Real.Gamma x ^ (1 - s) * (x ^ s * Real.Gamma x ^ s) := key
      _ = x ^ s * (Real.Gamma x ^ (1 - s) * Real.Gamma x ^ s) := by ring
      _ = x ^ s * Real.Gamma x := by
        rw [← Real.rpow_add hG, show 1 - s + s = 1 by ring, Real.rpow_one]

/-- `Γ(2αk+1)/Γ((2k+1)α+1) ≥ (2α(k+1))^{-α}` for `α ∈ (1,2]`. -/
lemma gamma_ratio_lower (α k : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) (hk : 0 ≤ k) :
    1 / ((2 * α) ^ α * (k + 1) ^ α) ≤
      Real.Gamma (2 * α * k + 1) / Real.Gamma ((2 * k + 1) * α + 1) := by
  have hα0 : 0 < α := by linarith
  set x := 2 * α * k + 1 with hxdef
  set s := α - 1 with hsdef
  have hx : 0 < x := by positivity
  have hxs : 0 < x + s := by linarith
  have hGx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have e1 : (2 * k + 1) * α + 1 = (x + s) + 1 := by rw [hxdef, hsdef]; ring
  rw [e1, Real.Gamma_add_one hxs.ne']
  have hW := gamma_upper x s hx (by linarith) (by linarith)
  set M := 2 * α * (k + 1) with hM
  have hMpos : 0 < M := by positivity
  have hxM : x ≤ M := by rw [hxdef, hM]; nlinarith
  have hxsM : x + s ≤ M := by rw [hxdef, hM, hsdef]; nlinarith
  have hMα : (2 * α) ^ α * (k + 1) ^ α = M ^ s * M := by
    rw [hM, ← Real.mul_rpow (by positivity) (by positivity)]
    have h' : (2 * α * (k + 1)) ^ α = (2 * α * (k + 1)) ^ (s + 1) := by
      congr 1; rw [hsdef]; ring
    rw [show 2 * α * (k + 1) = 2 * α * (k + 1) from rfl, mul_assoc 2 α, ← mul_assoc, h',
      Real.rpow_add_one (by positivity)]
  rw [hMα]
  have hden : (x + s) * Real.Gamma (x + s) ≤ M ^ s * M * Real.Gamma x := by
    calc (x + s) * Real.Gamma (x + s) ≤ M * (x ^ s * Real.Gamma x) :=
          mul_le_mul hxsM hW (Real.Gamma_pos_of_pos hxs).le hMpos.le
      _ ≤ M * (M ^ s * Real.Gamma x) := by
          apply mul_le_mul_of_nonneg_left _ hMpos.le
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow hx.le hxM (by linarith)) hGx.le
      _ = M ^ s * M * Real.Gamma x := by ring
  have hpos : 0 < (x + s) * Real.Gamma (x + s) := mul_pos hxs (Real.Gamma_pos_of_pos hxs)
  rw [div_le_div_iff₀ (by positivity) hpos]
  linarith

end Aux_FRR_B22

open FracRiccati.Radius Aux_FRR_B22 in
theorem solution (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2)
    (l n : ℝ) (hl : 0 < l) (hn : 0 < n) :
    let ρ : ℝ := l * n * (2 * α) ^ (-α) * BTilde α / Real.Gamma (α + 1)
    let C : ℝ := (2 * α) ^ α / (l * BTilde α)
    ∀ k : ℕ, 1 ≤ k → C * ρ ^ k * (k : ℝ) ^ (α - 1) ≤ (coeff α l 0 n (2 * k - 1)).re := by
  intro ρ C
  have hα0 : 0 < α := by linarith
  obtain ⟨hR1, -, hBpos⟩ := riemann_sum_B_52 α hα1 hα2
  have hG1 : 0 < Real.Gamma (α + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hρ : 0 < ρ := by positivity
  have hC : 0 < C := by positivity
  have hCB : l * C * BTilde α = (2 * α) ^ α := by
    show l * ((2 * α) ^ α / (l * BTilde α)) * BTilde α = _
    field_simp
  have hCρ : C * ρ = n / Real.Gamma (α + 1) := by
    show (2 * α) ^ α / (l * BTilde α) * (l * n * (2 * α) ^ (-α) * BTilde α / Real.Gamma (α + 1)) = _
    rw [Real.rpow_neg (by positivity)]
    field_simp
  clear_value ρ C
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨-, -, hb1, hrec⟩ := prop_B_1_a α hα0 (l : ℂ) (n : ℂ) hl0 hn0
  have hreal := (prop_B_1_b α hα0 hα2 l 0 n hl.le le_rfl hn.le).1
  set B : ℕ → ℝ := fun k => (coeff α l 0 n (2 * k - 1)).re with hBdef
  have hz : ∀ k, 1 ≤ k → coeff α l 0 n (2 * k - 1) = ((B k : ℝ) : ℂ) := by
    intro k hk
    exact Complex.ext (by simp [hBdef]) (by simp [hBdef, (hreal (2 * k - 1) (by omega)).2.1])
  have hB0 : ∀ k, 1 ≤ k → 0 ≤ B k := fun k hk => (hreal (2 * k - 1) (by omega)).2.2.2
  -- real recursion
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
      show C * ρ ^ 1 * ((1 : ℕ) : ℝ) ^ (α - 1) ≤ B 1
      rw [this, pow_one, Nat.cast_one, Real.one_rpow, mul_one, hCρ]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj : 1 ≤ j := by omega
      show C * ρ ^ (j + 1) * ((j + 1 : ℕ) : ℝ) ^ (α - 1) ≤ B (j + 1)
      rw [hrecR j hj]
      set K : ℝ := ((j + 1 : ℕ) : ℝ) with hK
      have hK1 : (2 : ℝ) ≤ K := by rw [hK]; push_cast; exact_mod_cast (by omega : 2 ≤ j + 1)
      have hK0 : (0 : ℝ) < K := by linarith
      -- the convolution lower bound
      have hsum : C ^ 2 * ρ ^ (j + 1) * ((K ^ 2) ^ (α - 1) * (K * BTilde α)) ≤
          ∑ ℓ ∈ Finset.Ico 1 (j + 1), B ℓ * B (j + 1 - ℓ) := by
        have hRj := hR1 (j + 1) (by omega)
        simp only at hRj
        have hRs : K * BTilde α ≤ ∑ ℓ ∈ Finset.Ico 1 (j + 1),
            ((ℓ : ℝ) / K * (1 - (ℓ : ℝ) / K)) ^ (α - 1) := by
          rw [← hK] at hRj
          have := mul_le_mul_of_nonneg_left hRj hK0.le
          rwa [← mul_assoc, mul_one_div_cancel hK0.ne', one_mul] at this
        calc C ^ 2 * ρ ^ (j + 1) * ((K ^ 2) ^ (α - 1) * (K * BTilde α))
            ≤ C ^ 2 * ρ ^ (j + 1) * ((K ^ 2) ^ (α - 1) * ∑ ℓ ∈ Finset.Ico 1 (j + 1),
                ((ℓ : ℝ) / K * (1 - (ℓ : ℝ) / K)) ^ (α - 1)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_left hRs (by positivity)
          _ = ∑ ℓ ∈ Finset.Ico 1 (j + 1), (C * ρ ^ ℓ * (ℓ : ℝ) ^ (α - 1)) *
                (C * ρ ^ (j + 1 - ℓ) * ((j + 1 - ℓ : ℕ) : ℝ) ^ (α - 1)) := by
              rw [Finset.mul_sum, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro ℓ hℓ
              rw [Finset.mem_Ico] at hℓ
              have hcast : ((j + 1 - ℓ : ℕ) : ℝ) = K - ℓ := by
                rw [hK, Nat.cast_sub (by omega)]
              rw [hcast]
              have hℓ0 : (0 : ℝ) ≤ ℓ := by positivity
              have hℓK : (ℓ : ℝ) ≤ K := by rw [hK]; exact_mod_cast hℓ.2.le
              have e1 : (ℓ : ℝ) / K * (1 - (ℓ : ℝ) / K) = (ℓ * (K - ℓ)) / K ^ 2 := by
                field_simp
              rw [e1, Real.div_rpow (by nlinarith) (by positivity), Real.mul_rpow hℓ0 (by linarith)]
              have hρs : ρ ^ ℓ * ρ ^ (j + 1 - ℓ) = ρ ^ (j + 1) := by
                rw [← pow_add]; congr 1; omega
              have hK2 : 0 < (K ^ 2) ^ (α - 1) := by positivity
              rw [← hρs]
              field_simp
          _ ≤ ∑ ℓ ∈ Finset.Ico 1 (j + 1), B ℓ * B (j + 1 - ℓ) := by
              apply Finset.sum_le_sum
              intro ℓ hℓ
              rw [Finset.mem_Ico] at hℓ
              have i1 := ih ℓ (by omega) (by omega)
              have i2 := ih (j + 1 - ℓ) (by omega) (by omega)
              exact mul_le_mul i1 i2 (by positivity) (hB0 ℓ (by omega))
      have hg := gamma_ratio_lower α j hα1 hα2 (by positivity)
      have hKj : (j : ℝ) + 1 = K := by rw [hK]; push_cast; ring
      rw [hKj] at hg
      have hg0 : 0 < 1 / ((2 * α) ^ α * K ^ α) := by positivity
      have hKa : K ^ α = K ^ (α - 1) * K := by
        rw [Real.rpow_sub_one hK0.ne']; field_simp
      have hK2a : (K ^ 2) ^ (α - 1) = K ^ (α - 1) * K ^ (α - 1) := by
        rw [show (K ^ 2 : ℝ) = K * K by ring, Real.mul_rpow hK0.le hK0.le]
      have hKpos : 0 < K ^ (α - 1) := by positivity
      calc C * ρ ^ (j + 1) * K ^ (α - 1)
          = l * (1 / ((2 * α) ^ α * K ^ α)) *
              (C ^ 2 * ρ ^ (j + 1) * ((K ^ 2) ^ (α - 1) * (K * BTilde α))) := by
            rw [hKa, hK2a, ← hCB]
            have hB0' : BTilde α ≠ 0 := hBpos.ne'
            field_simp
        _ ≤ l * (Real.Gamma (2 * α * j + 1) / Real.Gamma ((2 * j + 1) * α + 1)) *
              ∑ ℓ ∈ Finset.Ico 1 (j + 1), B ℓ * B (j + 1 - ℓ) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hg hl.le) hsum (by positivity)
            exact mul_nonneg hl.le (le_trans hg0.le hg)
