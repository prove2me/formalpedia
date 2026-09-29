-- Prove2me | solution 2 for FourExp.norm_to_polynomial_alg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T16:51:45.465989+00:00
-- url     : https://prove2.me/submissions/09b3d375-34f4-454e-b361-a077203e66c7

import Mathlib
import Theorems.Thm_FourExp_exists_iteratedDeriv_reduced_presentation
import Theorems.Thm_FourExp_exists_int_norm
import Theorems.Thm_FourExp_exists_pow_mul_pow_le_exp_sq_mul_sqrt_log
import Theorems.Thm_Transcendence_length_sum_le
import Theorems.Thm_Transcendence_length_mul_le

/-!
# A small nonzero derivative gives an integer polynomial that is small at `ω`

Write `φ(P) = P(ω, ω₁)` for `P ∈ ℤ[X][Y]`, `d = deg Q`, `s = √(log N)`, `A = N² s`, `B = N² / s`
and `S = ⌊B⌋`. The auxiliary function is
`F_q(z) = ∑ (∑_{μ,ν} q_{ijkμν} ω^μ ω₁^ν) z^i e^((j x₁ + k x₂) z)`, with integers
`|q_{ijkμν}| ≤ e^(κ A)`, `i < S`, `j, k < 2N`, `μ < M ≤ κ S` and `ν < d`.

At the point `a y₁ + b y₂` and the order `m < S / 2`, `Λ F_q⁽ᵐ⁾(a y₁ + b y₂) = φ(Pol)` with
`Λ ≠ 0` and `Pol = ∑ q_{ijkμν} R_{ijkμν}` of `Y`-degree below `d`. Both `|Λ|` and the lengths of
the `R_{ijkμν}` are at most `e^(κ₅ A)`, so `Pol` has length at most `e^(β A)` and `X`-degree at
most `e = M + c (1 + m + S) ≤ (κ + 3 c) B`. If `F_q⁽ᵐ⁾(a y₁ + b y₂) ≠ 0`, the norm of `φ(Pol)`
down to `ℚ(ω)` is an integer polynomial `P ≠ 0` of length at most `(c₁ e^(β A))^d` and degree at
most `d (e + c₁)`, with `|P(ω)| ≤ |φ(Pol)| (c₁ e^(β A) max(1, |ω|)^e)^d`. One constant `k`
bounds the three exponents. So `|P(ω)| ≤ e^(k A - N⁴ s / κ')` when
`|F_q⁽ᵐ⁾(a y₁ + b y₂)| ≤ e^(-N⁴ s / κ')`, and this is below `e^(-C (k A) (k B)) = e^(-C k² N⁴)`
as soon as `s ≥ 2 κ' (|C| k² + k + 1)`.
-/

namespace NormToPolynomialAlg

open Polynomial

/-- A coefficient of an integer polynomial is at most its length. -/
lemma natAbs_coeff_le (P : Polynomial ℤ) (i : ℕ) :
    (P.coeff i).natAbs ≤ ∑ j ∈ P.support, (P.coeff j).natAbs := by
  by_cases hi : i ∈ P.support
  · exact Finset.single_le_sum (f := fun j => (P.coeff j).natAbs) (fun _ _ => Nat.zero_le _) hi
  · rw [notMem_support_iff.1 hi]; simp

/-- Multiplying by an integer `a` multiplies the length by `|a|` at most. -/
lemma length_C_C_mul_le {a : ℤ} {P : Polynomial (Polynomial ℤ)} {x y : ℝ} (ha : |(a : ℝ)| ≤ x)
    (hP : ((∑ k ∈ P.support, ∑ i ∈ (P.coeff k).support, ((P.coeff k).coeff i).natAbs : ℕ) : ℝ)
      ≤ y) :
    ((∑ k ∈ (C (C a) * P).support, ∑ i ∈ ((C (C a) * P).coeff k).support,
      (((C (C a) * P).coeff k).coeff i).natAbs : ℕ) : ℝ) ≤ x * y := by
  have h := Transcendence.length_mul_le (C (C a)) P
  have hC : ∑ k ∈ (C (C a)).support, ∑ i ∈ ((C (C a)).coeff k).support,
      (((C (C a)).coeff k).coeff i).natAbs = a.natAbs := by
    by_cases ha0 : a = 0
    · simp [ha0]
    · rw [support_C (C_ne_zero.2 ha0), Finset.sum_singleton, coeff_C_zero, support_C ha0,
        Finset.sum_singleton, coeff_C_zero]
  rw [hC] at h
  refine (Nat.cast_le.2 h).trans ?_
  rw [Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs]
  exact mul_le_mul ha hP (Nat.cast_nonneg _) ((abs_nonneg _).trans ha)

/-- The length of a sum is at most the number of terms times a bound on their lengths. -/
lemma length_sum_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial (Polynomial ℤ)) (B : ℝ)
    (h : ∀ i ∈ s, ((∑ k ∈ (f i).support, ∑ j ∈ ((f i).coeff k).support,
      (((f i).coeff k).coeff j).natAbs : ℕ) : ℝ) ≤ B) :
    ((∑ k ∈ (∑ i ∈ s, f i).support, ∑ j ∈ ((∑ i ∈ s, f i).coeff k).support,
      (((∑ i ∈ s, f i).coeff k).coeff j).natAbs : ℕ) : ℝ) ≤ s.card * B := by
  refine (Nat.cast_le.2 (Transcendence.length_sum_le s f)).trans ?_
  rw [Nat.cast_sum]
  exact (Finset.sum_le_sum h).trans (by rw [Finset.sum_const, nsmul_eq_mul])

/-- For `A ≥ 1`, a nonnegative `x` is at most `e^(x A)`. -/
lemma le_exp_mul {x A : ℝ} (hx : 0 ≤ x) (hA : 1 ≤ A) : x ≤ Real.exp (x * A) := by
  nlinarith [Real.add_one_le_exp (x * A), mul_le_mul_of_nonneg_left hA hx]

end NormToPolynomialAlg

open Polynomial NormToPolynomialAlg

theorem solution
    (x₁ x₂ y₁ y₂ : ℂ)
    (hexp : ∀ i j : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * ![y₁, y₂] j))) (ω ω₁ : ℂ) (hω : Transcendental ℚ ω) (Q : Polynomial (Polynomial ℤ)) (hQm : Q.Monic) (hQd : 0 < Q.natDegree)
    (hQroot : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Q = 0)
    (hQmin : ∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree → Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0)
    (D : Polynomial (Polynomial ℤ)) (E G : Fin 2 → Polynomial (Polynomial ℤ)) (H : Fin 2 → Fin 2 → Polynomial (Polynomial ℤ))
    (hD : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D ≠ 0) (hE : ∀ i, ![x₁, x₂] i * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (E i))
    (hG : ∀ j, ![y₁, y₂] j * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (G j))
    (hH : ∀ i j, Complex.exp (![x₁, x₂] i * ![y₁, y₂] j) * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (H i j))
    (κ κ' : ℝ) (hκ : 0 < κ) (hκ' : 0 < κ') :
    ∃ k : ℝ, 0 < k ∧ ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∀ M : ℕ, (M : ℝ) ≤ κ * ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ →
      ∀ q : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → Fin (2 * N) → Fin (2 * N) → Fin M → Fin Q.natDegree → ℤ,
      (∀ i j k' μ ν, |((q i j k' μ ν : ℤ) : ℝ)| ≤ Real.exp (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) →
      ∀ a b s : ℕ, a < 14 * ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ → b < 14 * ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ → s < ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ / 2 →
      iteratedDeriv s (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
              (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z)) ((a : ℂ) * y₁ + (b : ℂ) * y₂) ≠ 0 →
      ‖iteratedDeriv s (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
              (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z)) ((a : ℂ) * y₁ + (b : ℂ) * y₂)‖
          ≤ Real.exp (-(((N : ℝ) ^ 4 * Real.sqrt (Real.log (N : ℝ))) / κ')) →
      ∃ P : Polynomial ℤ, P ≠ 0 ∧
        (∀ i : ℕ, |(P.coeff i : ℝ)| ≤ Real.exp (k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 * Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) ∧
        (P.natDegree : ℝ) ≤ k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 / Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))) ∧
        ‖Polynomial.aeval ω P‖ < Real.exp (-(C * (k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 * Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ)))) * (k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 / Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ)))))) := by
  -- The presentation of the derivatives, the norm down to `ℚ(ω)`, and the growth bound for
  -- the grid `T ≤ 14 N`.
  obtain ⟨c, hc⟩ := FourExp.exists_iteratedDeriv_reduced_presentation x₁ x₂ y₁ y₂ hexp ω ω₁ Q
    hQm hQroot D E G H hD hE hG hH
  obtain ⟨c₁, hc₁⟩ := FourExp.exists_int_norm ω ω₁ Q hQm hQroot hQmin
  obtain ⟨κ₅, hκ₅, hA5⟩ := FourExp.exists_pow_mul_pow_le_exp_sq_mul_sqrt_log c 14
  -- One constant `k` for the height, the degree and the value.
  have hlw : 0 ≤ Real.log (max 1 ‖ω‖) := Real.log_nonneg (le_max_left _ _)
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = 4 * κ * Q.natDegree + 6 + κ + κ₅ := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℝ,
      k = Q.natDegree * (c₁ + β + (κ + 3 * c) * (1 + Real.log (max 1 ‖ω‖))) + κ₅ + 1 := ⟨_, rfl⟩
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hk0 : 0 < k := by rw [hk]; positivity
  refine ⟨k, hk0, fun C => ⟨max 3 ⌈Real.exp ((2 * κ' * (|C| * k ^ 2 + k + 1)) ^ 2)⌉₊,
    fun N hN => ?_⟩⟩
  -- The scale `s = √(log N)`, with `s ≥ 2 κ' (|C| k² + k + 1)`.
  have hN3 : 3 ≤ N := by omega
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hN3' : ¬ (N : ℝ) ≤ 3 := by
    have : (4 : ℝ) ≤ N := by exact_mod_cast (by omega : 4 ≤ N)
    linarith
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by positivity)]; have := Real.exp_one_lt_d9; linarith
  have hLN : Real.log N ≤ N := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < N); linarith
  have hs1 : 1 ≤ Real.sqrt (Real.log N) := Real.one_le_sqrt.2 hL1
  have hss := Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ Real.log N)
  have hσ : 2 * κ' * (|C| * k ^ 2 + k + 1) ≤ Real.sqrt (Real.log N) := by
    have h1 : Real.exp ((2 * κ' * (|C| * k ^ 2 + k + 1)) ^ 2) ≤ N := (Nat.le_ceil _).trans
      (by exact_mod_cast (by omega : ⌈Real.exp ((2 * κ' * (|C| * k ^ 2 + k + 1)) ^ 2)⌉₊ ≤ N))
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * κ' * (|C| * k ^ 2 + k + 1))]
    exact Real.sqrt_le_sqrt ((Real.le_log_iff_exp_le (by positivity)).2 h1)
  generalize hs : Real.sqrt (Real.log (N : ℝ)) = s at hs1 hss hσ ⊢
  have hspos : 0 < s := by linarith
  have hNN : (N : ℝ) * 1 ≤ N * N := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hsN : s ≤ (N : ℝ) ^ 2 := by linarith [mul_le_mul_of_nonneg_left hs1 hspos.le]
  -- The three floors.
  have hSr : (⌊(N : ℝ) ^ 2 / s⌋₊ : ℝ) ≤ (N : ℝ) ^ 2 / s := Nat.floor_le (by positivity)
  have h1r : (⌊(N : ℝ) / s⌋₊ : ℝ) ≤ (N : ℝ) / s := Nat.floor_le (by positivity)
  have h2r : (⌊(N : ℝ) * s⌋₊ : ℝ) ≤ (N : ℝ) * s := Nat.floor_le (by positivity)
  generalize ⌊(N : ℝ) ^ 2 / s⌋₊ = S at hSr ⊢
  generalize ⌊(N : ℝ) / s⌋₊ = t₁ at h1r ⊢
  generalize ⌊(N : ℝ) * s⌋₊ = t₂ at h2r ⊢
  -- `A = N² s` and `B = N² / s`: `1 ≤ B ≤ A`, `log N ≤ A ≤ N⁴` and `A B = N⁴`.
  have hSN : (S : ℝ) ≤ (N : ℝ) ^ 2 := hSr.trans (div_le_self (by positivity) hs1)
  have hB1 : 1 ≤ (N : ℝ) ^ 2 / s := by rw [le_div_iff₀ hspos]; linarith
  have hBA : (N : ℝ) ^ 2 / s ≤ (N : ℝ) ^ 2 * s := by
    rw [div_le_iff₀ hspos, mul_assoc, hss]
    linarith [mul_le_mul_of_nonneg_left hL1 (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2)]
  have hLA : Real.log N ≤ (N : ℝ) ^ 2 * s := by
    linarith [mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2)]
  have hAN : (N : ℝ) ^ 2 * s ≤ (N : ℝ) ^ 4 := by
    linarith [mul_le_mul_of_nonneg_left hsN (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2)]
  have hAB : (N : ℝ) ^ 2 * s * ((N : ℝ) ^ 2 / s) = (N : ℝ) ^ 4 := by
    field_simp
  generalize hA : (N : ℝ) ^ 2 * s = A at hBA hLA hAN hAB ⊢
  generalize hB : (N : ℝ) ^ 2 / s = B at hSr hB1 hBA hAB ⊢
  have hA1 : 1 ≤ A := hB1.trans hBA
  intro M hM q hqq a b m ha hb hm hne hsmall
  have hmS : m ≤ S := by omega
  -- `Λ F_q⁽ᵐ⁾(a y₁ + b y₂) = φ(Pol)`, with `|Λ|` and the lengths of the `R` at most `e^(κ₅ A)`.
  obtain ⟨Λ, hΛ, hΛb, R, hRy, hRl, hRx, hRid⟩ := hc S (2 * N) M a b m
  have h5 := hA5 N S (2 * N) a b m hN3
  rw [hs, hA, hB] at h5
  have hL5 := h5 hSr hmS (by omega)
    (by have : (a : ℝ) ≤ 14 * t₁ := by exact_mod_cast (by omega : a ≤ 14 * t₁)
        push_cast; linarith)
    (by have : (b : ℝ) ≤ 14 * t₂ := by exact_mod_cast (by omega : b ≤ 14 * t₂)
        push_cast; linarith)
  have hΛe : ‖Λ‖ ≤ Real.exp (κ₅ * A) := by
    refine hΛb.trans (le_trans ?_ hL5)
    exact_mod_cast Nat.le_mul_of_pos_right _ (by positivity)
  obtain ⟨Pol, hPol⟩ : ∃ Pol : Polynomial (Polynomial ℤ), Pol = ∑ i : Fin S, ∑ j : Fin (2 * N),
      ∑ k' : Fin (2 * N), ∑ μ : Fin M, ∑ ν : Fin Q.natDegree,
        Polynomial.C (Polynomial.C (q i j k' μ ν)) * R i j k' μ ν := ⟨_, rfl⟩
  have hval := hRid q
  rw [← hPol] at hval
  have hPol0 : eval₂ (eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Pol ≠ 0 := by
    rw [← hval]; exact mul_ne_zero hΛ hne
  -- `Pol` has `Y`-degree below `d`, `X`-degree at most `e`, and length at most `e^(β A)`.
  have hPy : Pol.natDegree < Q.natDegree := by
    rw [hPol]
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ fun i _ =>
      natDegree_sum_le_of_forall_le _ _ fun j _ => natDegree_sum_le_of_forall_le _ _ fun k' _ =>
      natDegree_sum_le_of_forall_le _ _ fun μ _ => natDegree_sum_le_of_forall_le _ _ fun ν _ =>
      (natDegree_C_mul_le _ _).trans (Nat.le_sub_one_of_lt (hRy i j k' μ ν))) (by omega)
  have hPx : ∀ r, (Pol.coeff r).natDegree ≤ M + c * (1 + m + S) := by
    intro r
    simp only [hPol, finsetSum_coeff, coeff_C_mul]
    exact natDegree_sum_le_of_forall_le _ _ fun i _ =>
      natDegree_sum_le_of_forall_le _ _ fun j _ => natDegree_sum_le_of_forall_le _ _ fun k' _ =>
      natDegree_sum_le_of_forall_le _ _ fun μ _ => natDegree_sum_le_of_forall_le _ _ fun ν _ =>
      (natDegree_C_mul_le _ _).trans (hRx i j k' μ ν r)
  obtain ⟨lP, hlP⟩ : ∃ lP : ℕ, ∑ k ∈ Pol.support, ∑ i ∈ (Pol.coeff k).support,
      ((Pol.coeff k).coeff i).natAbs = lP := ⟨_, rfl⟩
  have hlPe : (lP : ℝ) ≤ Real.exp (β * A) := by
    rw [← hlP, hPol]
    refine (length_sum_le _ _ _ fun i _ => length_sum_le _ _ _ fun j _ =>
      length_sum_le _ _ _ fun k' _ => length_sum_le _ _ _ fun μ _ => length_sum_le _ _ _ fun ν _ =>
      length_C_C_mul_le (hqq i j k' μ ν) ((Nat.cast_le.2 (hRl i j k' μ ν)).trans hL5)).trans ?_
    simp only [Finset.card_univ, Fintype.card_fin]
    push_cast
    have hN6 : (N : ℝ) ^ 6 ≤ Real.exp (6 * A) := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < (N : ℝ) ^ 6), Real.log_pow]
      exact Real.exp_le_exp.2 (by push_cast; linarith)
    have hMN : (M : ℝ) ≤ κ * (N : ℝ) ^ 2 := hM.trans (mul_le_mul_of_nonneg_left hSN hκ.le)
    calc _ ≤ (N : ℝ) ^ 2 * (2 * N * (2 * N * (κ * (N : ℝ) ^ 2 * (Q.natDegree *
            (Real.exp (κ * A) * Real.exp (κ₅ * A)))))) := by gcongr
      _ = 4 * κ * Q.natDegree * (N : ℝ) ^ 6 * (Real.exp (κ * A) * Real.exp (κ₅ * A)) := by ring
      _ ≤ Real.exp (4 * κ * Q.natDegree * A) * Real.exp (6 * A) *
            (Real.exp (κ * A) * Real.exp (κ₅ * A)) := by
          gcongr; exact le_exp_mul (by positivity) hA1
      _ = Real.exp (β * A) := by rw [hβ]; simp only [add_mul, Real.exp_add]; ring
  -- The norm `P` of `φ(Pol)`, and the three bounds.
  obtain ⟨P, hP0, hPl, hPd, hPv⟩ := hc₁ Pol lP (M + c * (1 + m + S)) hPy hlP.le hPx hPol0
  have he : ((M + c * (1 + m + S) : ℕ) : ℝ) ≤ (κ + 3 * c) * B := by
    have hmS' : (m : ℝ) ≤ S := by exact_mod_cast hmS
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    push_cast
    linarith [mul_le_mul_of_nonneg_left hSr hκ.le, mul_le_mul_of_nonneg_left hB1 hc0,
      mul_le_mul_of_nonneg_left (hmS'.trans hSr) hc0, mul_le_mul_of_nonneg_left hSr hc0]
  have hX : ((c₁ * lP : ℕ) : ℝ) ≤ Real.exp ((c₁ + β) * A) := by
    rw [Nat.cast_mul, add_mul, Real.exp_add]
    exact mul_le_mul (le_exp_mul (Nat.cast_nonneg _) hA1) hlPe (Nat.cast_nonneg _)
      (Real.exp_pos _).le
  have hd0 : (0 : ℝ) ≤ Q.natDegree := Nat.cast_nonneg _
  refine ⟨P, hP0, fun i => ?_, ?_, ?_⟩
  · -- the height
    rw [if_neg hN3', ← Int.cast_abs, ← Nat.cast_natAbs]
    have h1 : ((P.coeff i).natAbs : ℝ) ≤ ((c₁ * lP : ℕ) : ℝ) ^ Q.natDegree := by
      exact_mod_cast (natAbs_coeff_le P i).trans hPl
    refine h1.trans ((pow_le_pow_left₀ (Nat.cast_nonneg _) hX _).trans ?_)
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    rw [hk]
    linarith [mul_nonneg (by positivity : (0 : ℝ) ≤
      Q.natDegree * ((κ + 3 * c) * (1 + Real.log (max 1 ‖ω‖))) + κ₅ + 1)
      (by linarith : (0 : ℝ) ≤ A)]
  · -- the degree
    rw [if_neg hN3']
    have h1 : (P.natDegree : ℝ) ≤ Q.natDegree * (((M + c * (1 + m + S) : ℕ) : ℝ) + c₁) := by
      exact_mod_cast hPd
    refine h1.trans ?_
    have hc₁B : (c₁ : ℝ) ≤ c₁ * B := le_mul_of_one_le_right (Nat.cast_nonneg _) hB1
    rw [hk]
    linarith [mul_le_mul_of_nonneg_left (add_le_add he hc₁B) hd0, mul_nonneg (by positivity :
      (0 : ℝ) ≤ Q.natDegree * (β + (κ + 3 * c) * Real.log (max 1 ‖ω‖)) + κ₅ + 1)
      (by linarith : (0 : ℝ) ≤ B)]
  · -- the value
    rw [if_neg hN3', if_neg hN3']
    have hW : max 1 ‖ω‖ ^ (M + c * (1 + m + S)) ≤
        Real.exp ((κ + 3 * c) * Real.log (max 1 ‖ω‖) * A) := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < max 1 ‖ω‖), ← Real.exp_nat_mul, Real.log_exp]
      refine Real.exp_le_exp.2 ?_
      linarith [mul_le_mul_of_nonneg_right
        (he.trans (mul_le_mul_of_nonneg_left hBA (by positivity))) hlw]
    have hXW := pow_le_pow_left₀ (by positivity) (mul_le_mul hX hW (by positivity)
      (Real.exp_pos _).le) Q.natDegree
    rw [← Real.exp_add, ← Real.exp_nat_mul] at hXW
    refine lt_of_le_of_lt (b := Real.exp (k * A - (N : ℝ) ^ 4 * s / κ')) (hPv.trans ?_)
      (Real.exp_lt_exp.2 ?_)
    · rw [← hval, norm_mul]
      refine (mul_le_mul (mul_le_mul hΛe hsmall (norm_nonneg _) (Real.exp_pos _).le) hXW
        (by positivity) (by positivity)).trans ?_
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      rw [hk]
      linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ Q.natDegree * (κ + 3 * c) + 1)
        (by linarith : (0 : ℝ) ≤ A)]
    · -- `k A - N⁴ s / κ' < -C (k A) (k B)`, since `A B = N⁴`, `A ≤ N⁴` and `s` is large.
      have hN4 : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
      have h1 : 2 * (|C| * k ^ 2 + k + 1) * (N : ℝ) ^ 4 ≤ (N : ℝ) ^ 4 * s / κ' := by
        rw [le_div_iff₀ hκ']; linarith [mul_le_mul_of_nonneg_left hσ hN4.le]
      have h2 : C * (k * A) * (k * B) ≤ |C| * k ^ 2 * (N : ℝ) ^ 4 := by
        rw [show C * (k * A) * (k * B) = C * k ^ 2 * (A * B) by ring, hAB]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)) hN4.le
      have h3 : k * A ≤ k * (N : ℝ) ^ 4 := mul_le_mul_of_nonneg_left hAN hk0.le
      linarith [mul_nonneg (mul_nonneg (abs_nonneg C) (sq_nonneg k)) hN4.le, mul_pos hk0 hN4]

#print axioms solution
