-- Prove2me | solution 1 for Erdos287.gap_from_uniform_prime_window
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T03:27:44.794313+00:00
-- url     : https://prove2.me/submissions/e9d547e8-d9dc-49a5-8f0d-e196111f45c2

import Mathlib
import Theorems.Thm_Erdos287_gap_from_dense_prime_form_groups

open Finset

set_option autoImplicit false

/-- A strict ratio bound on the pair coefficients gives a uniform parameter window. -/
theorem solution (A : ℕ) (L U : ℝ) (hL : 0 < L) (hLU : L ≤ U)
    (hU : U < Real.exp 1 * L) :
    ∃ α β : ℝ, 0 < α ∧ α < β ∧ ∃ M₀ : ℕ,
    ∀ (k : ℕ) (f : ℕ → ℕ), 2 ≤ k →
      (∀ i, i < k → 1 < f i) →
      (∀ i j, i < j → j < k → f i < f j) →
      (∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) →
      M₀ ≤ f (k - 1) →
      ∀ (N u v t : ℕ) (S : Finset ℕ) (a : ℕ → ℕ),
        0 < u → 2 * u ≤ v + 2 →
        (∀ s ∈ S, s < N) →
        u * (N + v) < (u + v) * S.card →
        α * (f (k - 1) : ℝ) ≤ t → (t : ℝ) ≤ β * f (k - 1) →
        (∀ s ∈ S, 0 < a s ∧ a s ≤ A ∧ Nat.Prime (a s * t + 1)) →
        (∀ s ∈ S, ∀ r ∈ S, u ≤ r - s → r - s ≤ v →
        a s < a r ∧ (a r - a s) ∣ a s ∧
          L ≤ ((a s / (a r - a s) : ℕ) : ℝ) * a r ∧
          ((a s / (a r - a s) : ℕ) : ℝ) * a r ≤ U) →
        ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  have hUp : 0 < U := hL.trans_le hLU
  have heL : 0 < Real.exp 1 * L := mul_pos (Real.exp_pos _) hL
  obtain ⟨α, hαl, hαu⟩ := exists_between (one_div_lt_one_div_of_lt hUp hU)
  obtain ⟨β, hβl, hβu⟩ := exists_between hαu
  have hα : 0 < α := (one_div_pos.mpr heL).trans hαl
  have hαe : 1 < α * (Real.exp 1 * L) := (div_lt_iff₀ heL).mp hαl
  have hβU : β * U < 1 := (lt_div_iff₀ hUp).mp hβu
  obtain ⟨B₀, hB₀⟩ := exists_nat_gt (1 / α)
  have hB₀p : (0 : ℝ) < B₀ := (one_div_pos.mpr hα).trans hB₀
  let H := Real.log (B₀ : ℝ) + Chebyshev.psi (B₀ : ℝ)
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt
    (max ((A + 1 : ℝ) / (1 - β * U)) (Real.exp H / α))
  refine ⟨α, β, hα, hβl, M₀, ?_⟩
  intro k f hk hf1 hmono hsum hM N u v t S a hu hv hS hdensity htl htu hprime hpair
  let M := f (k - 1)
  have hM' : (M₀ : ℝ) ≤ M := by exact_mod_cast hM
  have hMp : (0 : ℝ) < M := by
    have : 1 < M := hf1 (k - 1) (by omega)
    exact_mod_cast (show 0 < M by omega)
  have hmargin : (A + 1 : ℝ) < (1 - β * U) * M := by
    have h := (div_lt_iff₀ (sub_pos.mpr hβU)).mp
      ((le_max_left _ _).trans_lt (hM₀.trans_le hM'))
    simpa [mul_comm] using h
  have hbig : Real.exp H < α * M := by
    have h := (div_lt_iff₀ hα).mp ((le_max_right _ _).trans_lt (hM₀.trans_le hM'))
    simpa [mul_comm] using h
  refine Erdos287.gap_from_dense_prime_form_groups k hk f hf1 hmono hsum
    N u v t S a hu hv hS hdensity (fun s hs => (hprime s hs).2.2) ?_ ?_
  · intro s hs
    let p := a s * t + 1
    let B := M / p
    change Real.log (B : ℝ) + Chebyshev.psi (B : ℝ) < Real.log (p : ℝ)
    have htp : t ≤ p := by
      have h := Nat.mul_le_mul_right t (show 1 ≤ a s from (hprime s hs).1)
      simpa [p] using h.trans (Nat.le_succ (a s * t))
    have hαp : α * (M : ℝ) ≤ p := htl.trans (by exact_mod_cast htp)
    have hBmul : (B : ℝ) * p ≤ M := by exact_mod_cast (Nat.div_mul_le_self M p)
    have hB₀a : 1 < α * (B₀ : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hα).mp hB₀
    have hB : (B : ℝ) ≤ B₀ := by
      by_contra! h
      have hBa : 1 < α * (B : ℝ) :=
        hB₀a.trans (mul_lt_mul_of_pos_left h hα)
      have hp : (0 : ℝ) < p := (mul_pos hα hMp).trans_le hαp
      have hh := mul_lt_mul_of_pos_right hBa hp
      have hle := mul_le_mul_of_nonneg_left hBmul hα.le
      rw [one_mul, mul_assoc] at hh
      exact (hh.trans_le (hle.trans hαp)).false
    have hlog : Real.log (B : ℝ) ≤ Real.log (B₀ : ℝ) := by
      by_cases hz : B = 0
      · simpa [hz] using Real.log_nonneg (show (1 : ℝ) ≤ B₀ by
          exact_mod_cast (show 1 ≤ B₀ by exact Nat.pos_of_ne_zero (by
            intro h
            simp [h] at hB₀p)))
      · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz) hB
    have hψ := Chebyshev.psi_mono hB
    have hh := Real.log_lt_log (Real.exp_pos H) (hbig.trans_le hαp)
    rw [Real.log_exp] at hh
    exact (add_le_add hlog hψ).trans_lt hh
  · intro s hs r hr hrs₁ hrs₂
    obtain ⟨ha, hd, hlo, hhi⟩ := hpair s hs r hr hrs₁ hrs₂
    let c := a s / (a r - a s)
    let x := c * (a r * t + 1)
    let C := (c : ℝ) * (a r : ℝ)
    change L ≤ C at hlo
    change C ≤ U at hhi
    change a s < a r ∧ (a r - a s) ∣ a s ∧ x + 1 ≤ M ∧ (M : ℝ) < Real.exp 1 * x
    have hc : (c : ℝ) ≤ A := by
      exact_mod_cast (Nat.div_le_self (a s) (a r - a s)).trans (hprime s hs).2.1
    have hx : (x : ℝ) = C * t + c := by simp [x, C, mul_add, mul_assoc]
    have hu' : C * (t : ℝ) ≤ (β * U) * M := by
      calc
        C * (t : ℝ) ≤ U * (t : ℝ) := mul_le_mul_of_nonneg_right hhi (Nat.cast_nonneg t)
        _ ≤ U * (β * M) := mul_le_mul_of_nonneg_left htu hUp.le
        _ = (β * U) * M := by ring
    have hl' : (α * L) * M ≤ C * (t : ℝ) := by
      calc
        (α * L) * M = L * (α * M) := by ring
        _ ≤ L * (t : ℝ) := mul_le_mul_of_nonneg_left htl hL.le
        _ ≤ C * (t : ℝ) := mul_le_mul_of_nonneg_right hlo (Nat.cast_nonneg t)
    refine ⟨ha, hd, ?_, ?_⟩
    · have hupper : (x : ℝ) + 1 ≤ M := by rw [hx]; linarith
      exact_mod_cast hupper
    · have hle : (α * L) * M ≤ (x : ℝ) := by
        rw [hx]
        exact hl'.trans (le_add_of_nonneg_right (Nat.cast_nonneg c))
      calc
        (M : ℝ) < (α * (Real.exp 1 * L)) * M := by
          simpa using mul_lt_mul_of_pos_right hαe hMp
        _ = Real.exp 1 * ((α * L) * M) := by ring
        _ ≤ Real.exp 1 * (x : ℝ) := mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le

