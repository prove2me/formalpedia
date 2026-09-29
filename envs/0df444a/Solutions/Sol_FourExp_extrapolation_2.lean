-- Prove2me | solution 2 for FourExp.extrapolation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-27T08:02:46.423293+00:00
-- url     : https://prove2.me/submissions/17c57c45-a24b-47ec-a13e-780cee3de014

import Mathlib
import Theorems.Thm_Transcendence_expPoly_grid_estimate
import Theorems.Thm_FourExp_extrapolation_numbers

/-!
Extrapolation for the auxiliary function of the four exponentials theorem.

`F(z) = ∑ c i j k' z^i e^{(j x₁ + k' x₂) z}` is an exponential polynomial with `S (2N)²` terms,
frequencies of modulus `≤ 2N (|x₁| + |x₂|)` and degrees `< S`, where `q = √(log N)`,
`S = ⌊N² / q⌋`, `t₁ = ⌊N / q⌋`, `t₂ = ⌊N q⌋`. It vanishes to order `S` on the grid `a y₁ + b y₂`
(`a < t₁`, `b < t₂`), whose `t₁ t₂` points are distinct since `y₁, y₂` are ℚ-linearly independent.
The grid estimate with radius parameter `u = N` bounds `|F⁽ˢ⁾|` on the fourteen times larger grid
by `2 s! (N - 1)^(-t₁ t₂ S) · S (2N)² e^{κ N² q} · Z^S e^{2N X Z}`, with `X = |x₁| + |x₂|`,
`Z = Y N² q` and `Y = 2 (14 (|y₁| + |y₂|) + 1)`. The zero factor contributes `-N⁴ q / 16` to the
logarithm and everything else `O(N³ q)`, so for `N ≥ 32 (13 + κ + log Y + 2 X Y)` the bound is at
most `exp (-N⁴ q / 32)`.
-/

theorem solution
    (x₁ x₂ y₁ y₂ : ℂ) (hy : LinearIndependent ℚ ![y₁, y₂]) (κ : ℝ) (hκ : 0 < κ) :
    ∃ κ' : ℝ, 0 < κ' ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∀ c : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → Fin (2 * N) → Fin (2 * N) → ℂ,
      (∀ i j k', ‖c i j k'‖ ≤ Real.exp (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) →
      (∀ a b m : ℕ, a < ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ → b < ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ → m < ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ →
        iteratedDeriv m (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
              c i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z)) ((a : ℂ) * y₁ + (b : ℂ) * y₂) = 0) →
      ∀ s : ℕ, s < ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ / 2 → ∀ a b : ℕ, a < 14 * ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ → b < 14 * ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ →
        ‖iteratedDeriv s (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
              c i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z)) ((a : ℂ) * y₁ + (b : ℂ) * y₂)‖
          ≤ Real.exp (-(((N : ℝ) ^ 4 * Real.sqrt (Real.log (N : ℝ))) / κ')) := by
  set X := ‖x₁‖ + ‖x₂‖ with hX
  set Y : ℝ := 2 * (14 * (‖y₁‖ + ‖y₂‖) + 1) with hY
  have hX0 : 0 ≤ X := by positivity
  have hY1 : 1 ≤ Y := by rw [hY]; nlinarith [norm_nonneg y₁, norm_nonneg y₂]
  refine ⟨32, by norm_num, ⌈32 * (13 + κ + Real.log Y + 2 * X * Y)⌉₊, fun N hN => ?_⟩
  have hbig : 32 * (13 + κ + Real.log Y + 2 * X * Y) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN.le)
  have hNr : (416 : ℝ) ≤ N := by
    nlinarith [Real.log_nonneg hY1, mul_nonneg hX0 (by linarith : (0 : ℝ) ≤ Y)]
  -- the scale `q = √(log N)` and the three floors
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by positivity)]; linarith [Real.exp_one_lt_d9]
  have hLN : Real.log N ≤ N := by linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < N)]
  set q := Real.sqrt (Real.log (N : ℝ)) with hq
  have hq1 : 1 ≤ q := Real.one_le_sqrt.2 hL1
  have hqq : q * q = Real.log N := Real.mul_self_sqrt (by linarith)
  have hqN : q ≤ N := by nlinarith
  have hqpos : 0 < q := by linarith
  set S := ⌊(N : ℝ) ^ 2 / q⌋₊ with hS
  set t₁ := ⌊(N : ℝ) / q⌋₊ with ht₁
  set t₂ := ⌊(N : ℝ) * q⌋₊ with ht₂
  have half : ∀ z : ℝ, 1 ≤ z → z ≤ 2 * ⌊z⌋₊ := fun z hz => by
    have := Nat.lt_floor_add_one z
    have : (1 : ℝ) ≤ ⌊z⌋₊ := by exact_mod_cast (Nat.one_le_floor_iff z).2 hz
    linarith
  have hSu : (S : ℝ) * q ≤ (N : ℝ) ^ 2 := by
    rw [← le_div_iff₀ hqpos]; exact Nat.floor_le (by positivity)
  have hSl : (N : ℝ) ^ 2 ≤ 2 * (S * q) := by
    have := half ((N : ℝ) ^ 2 / q) ((one_le_div hqpos).2 (by nlinarith))
    rw [← hS, div_le_iff₀ hqpos] at this; linarith
  have h1l : (N : ℝ) ≤ 2 * (t₁ * q) := by
    have := half ((N : ℝ) / q) ((one_le_div hqpos).2 hqN)
    rw [← ht₁, div_le_iff₀ hqpos] at this; linarith
  have h2l : (N : ℝ) * q ≤ 2 * t₂ := half ((N : ℝ) * q) (by nlinarith)
  have h1u : (t₁ : ℝ) ≤ N * q :=
    (Nat.floor_le (by positivity)).trans ((div_le_self (by positivity) hq1).trans (by nlinarith))
  have h2u : (t₂ : ℝ) ≤ N * q := Nat.floor_le (by positivity)
  intro c hc hvan s hs a b ha hb
  -- the grid estimate, on the grid `a' y₁ + b' y₂` (`a' < t₁`, `b' < t₂`) with `u = N`
  have key := Transcendence.expPoly_grid_estimate ![y₁, y₂] hy
    (Finset.univ : Finset (Fin S × Fin (2 * N) × Fin (2 * N))) (fun p => c p.1 p.2.1 p.2.2)
    (fun p => ((p.2.1 : ℕ) : ℂ) * x₁ + ((p.2.2 : ℕ) : ℂ) * x₂) (fun p => (p.1 : ℕ))
    (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
      c i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z))
    (fun z => by simp only [Fintype.sum_prod_type]) (2 * N * X) S
    (fun p _ => ?_) (fun p _ => p.1.2.le) ![t₁, t₂] ![14 * t₁, 14 * t₂]
    (fun j => by fin_cases j <;> simp <;> omega) S (fun m hm i hi => ?_) N (Y * ((N : ℝ) ^ 2 * q))
    (by linarith) ?_ ![a, b] (fun j => by fin_cases j <;> simpa) s
  · simp only [Fin.sum_univ_two, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at key
    have hcsum : ∑ p : Fin S × Fin (2 * N) × Fin (2 * N), ‖c p.1 p.2.1 p.2.2‖
        ≤ S * (2 * N) * (2 * N) * Real.exp (κ * ((N : ℝ) ^ 2 * q)) := by
      refine (Finset.sum_le_card_nsmul _ _ _ fun p _ => hc _ _ _).trans_eq ?_
      simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]; ring
    refine key.trans (le_trans ?_ (FourExp.extrapolation_numbers X Y κ hX0 hY1 hκ.le
      N S t₁ t₂ s hbig (by omega) hSu hSl h1l h2l))
    have : (0 : ℝ) ≤ 1 / ((N : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
    gcongr
  · refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast, hX]
    have h1 : ((p.2.1 : ℕ) : ℝ) ≤ 2 * N := by exact_mod_cast p.2.1.2.le
    have h2 : ((p.2.2 : ℕ) : ℝ) ≤ 2 * N := by exact_mod_cast p.2.2.2.le
    nlinarith [norm_nonneg x₁, norm_nonneg x₂]
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact hvan (m 0) (m 1) i (by simpa using hm 0) (by simpa using hm 1) hi
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    have e1 : 14 * (t₁ : ℝ) * ‖y₁‖ + 14 * t₂ * ‖y₂‖ + 1 ≤ (14 * (‖y₁‖ + ‖y₂‖) + 1) * (N * q) := by
      nlinarith [mul_le_mul_of_nonneg_right h1u (norm_nonneg y₁),
        mul_le_mul_of_nonneg_right h2u (norm_nonneg y₂)]
    calc _ ≤ (14 * (‖y₁‖ + ‖y₂‖) + 1) * (N * q) * (2 * N) :=
          mul_le_mul e1 (by linarith) (by positivity) (by positivity)
      _ = Y * ((N : ℝ) ^ 2 * q) := by rw [hY]; ring

#print axioms solution
