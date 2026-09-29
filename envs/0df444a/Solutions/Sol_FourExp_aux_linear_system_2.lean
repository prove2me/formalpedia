-- Prove2me | solution 2 for FourExp.aux_linear_system
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T16:51:42.640237+00:00
-- url     : https://prove2.me/submissions/99ae5753-b531-4ee2-8838-bd3103ec5eff

import Mathlib
import Theorems.Thm_FourExp_exists_iteratedDeriv_reduced_presentation
import Theorems.Thm_FourExp_exists_pow_mul_pow_le_exp_sq_mul_sqrt_log

/-!
# The auxiliary linear system of the four exponentials argument

Write `φ(P) = P(ω, ω₁)` for `P ∈ ℤ[X][Y]`, `S = ⌊N² / √(log N)⌋`, `t₁ = ⌊N / √(log N)⌋` and
`t₂ = ⌊N √(log N)⌋`. The unknowns are integers `q_{ijkμν}` with `i < S`, `j, k < 2N`, `μ < M`,
`ν < deg Q`, and the auxiliary function is
`F_q(z) = ∑ (∑_{μ,ν} q_{ijkμν} ω^μ ω₁^ν) z^i e^((j x₁ + k x₂) z)`.

For each point `a y₁ + b y₂` and order `m`, `Λ F_q⁽ᵐ⁾(a y₁ + b y₂) = φ(∑ q_{ijkμν} R_{ijkμν})`
with a nonzero `Λ` and integer polynomials `R_{ijkμν}` of `Y`-degree below `deg Q` that do not
depend on `q`. The equations of the system say that every coefficient of `∑ q_{ijkμν} R_{ijkμν}`
vanishes; then `F_q⁽ᵐ⁾(a y₁ + b y₂) = 0`. With `M = W S` the `X`-degrees stay below `2M`, so there
are at most half as many equations as unknowns; and each coefficient of the system is at most the
length of some `R_{ijkμν}`, hence at most `exp(κ N² √(log N))`.
-/

namespace AuxLinearSystem

/-- A single integer coefficient of `P ∈ ℤ[X][Y]` is at most its length. -/
lemma natAbs_coeff_le_length (P : Polynomial (Polynomial ℤ)) (k i : ℕ) :
    ((P.coeff k).coeff i).natAbs ≤
      ∑ k ∈ P.support, ∑ i ∈ (P.coeff k).support, ((P.coeff k).coeff i).natAbs := by
  by_cases hk : k ∈ P.support
  · by_cases hi : i ∈ (P.coeff k).support
    · exact (Finset.single_le_sum (f := fun i => ((P.coeff k).coeff i).natAbs)
        (fun _ _ => Nat.zero_le _) hi).trans (Finset.single_le_sum
          (f := fun k => ∑ i ∈ (P.coeff k).support, ((P.coeff k).coeff i).natAbs)
          (fun _ _ => Nat.zero_le _) hk)
    · rw [Polynomial.notMem_support_iff.1 hi]; simp
  · rw [Polynomial.notMem_support_iff.1 hk]; simp

end AuxLinearSystem

open Polynomial

theorem solution
        (x₁ x₂ y₁ y₂ : ℂ)
    (hexp : ∀ i j : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * ![y₁, y₂] j))) (ω ω₁ : ℂ) (hω : Transcendental ℚ ω) (Q : Polynomial (Polynomial ℤ)) (hQm : Q.Monic) (hQd : 0 < Q.natDegree)
    (hQroot : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Q = 0)
    (hQmin : ∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree → Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0)
    (D : Polynomial (Polynomial ℤ)) (E G : Fin 2 → Polynomial (Polynomial ℤ)) (H : Fin 2 → Fin 2 → Polynomial (Polynomial ℤ))
    (hD : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D ≠ 0) (hE : ∀ i, ![x₁, x₂] i * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (E i))
    (hG : ∀ j, ![y₁, y₂] j * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (G j))
    (hH : ∀ i j, Complex.exp (![x₁, x₂] i * ![y₁, y₂] j) * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (H i j)) :
    ∃ κ₁ : ℝ, 0 < κ₁ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ κ₁ * ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ ∧ ∃ R : ℕ, 2 * R ≤ ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ * (2 * N) * (2 * N) * M * Q.natDegree ∧
      ∃ B : Fin R → Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → Fin (2 * N) → Fin (2 * N) → Fin M → Fin Q.natDegree → ℤ,
        (∀ e i j k' μ ν, |((B e i j k' μ ν : ℤ) : ℝ)| ≤ Real.exp (κ₁ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) ∧
        ∀ q : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → Fin (2 * N) → Fin (2 * N) → Fin M → Fin Q.natDegree → ℤ,
          (∀ e, ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N), ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, B e i j k' μ ν * q i j k' μ ν = 0) →
          ∀ a b m : ℕ, a < ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ → b < ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ → m < ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ →
            iteratedDeriv m (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
              (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z)) ((a : ℂ) * y₁ + (b : ℂ) * y₂) = 0 := by
  classical
  -- The derivatives at the points `a y₁ + b y₂`, as values of polynomials reduced modulo `Q`.
  obtain ⟨c, hc⟩ := FourExp.exists_iteratedDeriv_reduced_presentation x₁ x₂ y₁ y₂ hexp ω ω₁ Q
    hQm hQroot D E G H hD hE hG hH
  -- `W S` powers of `ω` per unknown leave room for the `X`-degrees of the reduced values.
  obtain ⟨W, hW⟩ : ∃ W : ℕ, W = 3 * c + 1 := ⟨_, rfl⟩
  obtain ⟨κ, hκ, hκb⟩ := FourExp.exists_pow_mul_pow_le_exp_sq_mul_sqrt_log c 2
  refine ⟨W + κ, by positivity, 3, fun N hN => ?_⟩
  have hN3 : 3 ≤ N := by omega
  -- The three floors.
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hLN : Real.log N ≤ N := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < N); linarith
  have hs1 : 1 ≤ Real.sqrt (Real.log N) := Real.one_le_sqrt.2 hL1
  have hsL : Real.sqrt (Real.log N) ≤ Real.log N := by
    have := Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ Real.log N); nlinarith
  have hspos : 0 < Real.sqrt (Real.log N) := by linarith
  have hSr : (⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) ≤
      (N : ℝ) ^ 2 / Real.sqrt (Real.log N) := Nat.floor_le (by positivity)
  have h1r : (⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) ≤ (N : ℝ) / Real.sqrt (Real.log N) :=
    Nat.floor_le (by positivity)
  have h2r : (⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) ≤ (N : ℝ) * Real.sqrt (Real.log N) :=
    Nat.floor_le (by positivity)
  have hS1 : 1 ≤ ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ hspos]
    nlinarith
  have ht : ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ * ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊
      ≤ N ^ 2 := by
    have : (⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) *
        ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ ≤ (N : ℝ) ^ 2 := by
      calc _ ≤ ((N : ℝ) / Real.sqrt (Real.log N)) * ((N : ℝ) * Real.sqrt (Real.log N)) :=
            mul_le_mul h1r h2r (by positivity) (by positivity)
        _ = (N : ℝ) ^ 2 := by field_simp
    exact_mod_cast this
  generalize ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ = S at hSr hS1 ⊢
  generalize ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ = t₁ at h1r ht ⊢
  generalize ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ = t₂ at h2r ht ⊢
  -- The unknowns: `W S` powers of `ω` and `deg Q` powers of `ω₁` per term.
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = W * S := ⟨_, rfl⟩
  -- The reduced values of the unknowns at every point and order.
  choose Λ hΛ _hΛn R hRy hRl hRx hRid using fun a b m : ℕ => hc S (2 * N) M a b m
  -- The common bound for their `X`-degrees at the orders `m < S`.
  obtain ⟨Dx, hDx⟩ : ∃ Dx : ℕ, Dx = M + c * (1 + S + S) := ⟨_, rfl⟩
  have hRx' : ∀ a b m : ℕ, m < S → ∀ i j k μ ν r,
      ((R a b m i j k μ ν).coeff r).natDegree ≤ Dx := by
    intro a b m hm i j k μ ν r
    refine (hRx a b m i j k μ ν r).trans ?_
    rw [hDx]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  -- The equations: one for each point, order, power of `X` and power of `Y`.
  have hcard : Fintype.card (Fin t₁ × Fin t₂ × Fin S × Fin (Dx + 1) × Fin Q.natDegree) =
      t₁ * (t₂ * (S * ((Dx + 1) * Q.natDegree))) := by simp
  have hDxM : Dx + 1 ≤ 2 * M := by
    rw [hDx, hM, hW]
    nlinarith [Nat.mul_le_mul_left c hS1]
  refine ⟨M, by rw [hM]; exact Nat.mul_pos (by omega) (by omega), ?_,
    t₁ * (t₂ * (S * ((Dx + 1) * Q.natDegree))), ?_,
    fun e i j k μ ν => (((R ((Fintype.equivFinOfCardEq hcard).symm e).1
      ((Fintype.equivFinOfCardEq hcard).symm e).2.1 ((Fintype.equivFinOfCardEq hcard).symm e).2.2.1
      i j k μ ν).coeff ((Fintype.equivFinOfCardEq hcard).symm e).2.2.2.2).coeff
      ((Fintype.equivFinOfCardEq hcard).symm e).2.2.2.1), ?_, ?_⟩
  · -- `M = W S ≤ κ₁ S`
    rw [hM]; push_cast
    have : (0 : ℝ) ≤ S := by positivity
    nlinarith
  · -- the number of equations is at most half the number of unknowns
    calc 2 * (t₁ * (t₂ * (S * ((Dx + 1) * Q.natDegree))))
        = 2 * (t₁ * t₂) * S * (Dx + 1) * Q.natDegree := by ring
      _ ≤ 2 * N ^ 2 * S * (2 * M) * Q.natDegree := by gcongr
      _ = S * (2 * N) * (2 * N) * M * Q.natDegree := by ring
  · -- each coefficient is at most the length of its reduced value
    intro e i j k μ ν
    dsimp only
    generalize (Fintype.equivFinOfCardEq hcard).symm e = x
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨m, hm⟩, ⟨h, hh⟩, ⟨r, hr⟩⟩ := x
    show |((((R a b m i j k μ ν).coeff r).coeff h : ℤ) : ℝ)| ≤ _
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    have hA : (a : ℝ) ≤ ((2 : ℕ) : ℝ) * ((N : ℝ) / Real.sqrt (Real.log (N : ℝ))) := by
      have : (a : ℝ) ≤ t₁ := by exact_mod_cast ha.le
      have : (0 : ℝ) ≤ (N : ℝ) / Real.sqrt (Real.log (N : ℝ)) := by positivity
      push_cast; linarith
    have hB : (b : ℝ) ≤ ((2 : ℕ) : ℝ) * ((N : ℝ) * Real.sqrt (Real.log (N : ℝ))) := by
      have : (b : ℝ) ≤ t₂ := by exact_mod_cast hb.le
      have : (0 : ℝ) ≤ (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) := by positivity
      push_cast; linarith
    refine (Nat.cast_le.2 ((AuxLinearSystem.natAbs_coeff_le_length _ r h).trans
      (hRl a b m i j k μ ν))).trans ?_
    refine (hκb N S (2 * N) a b m hN3 hSr hm.le le_rfl hA hB).trans ?_
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · -- solutions of the system make the derivatives vanish
    intro q hq a b m ha hb hm
    have hV : ∑ i : Fin S, ∑ j : Fin (2 * N), ∑ k : Fin (2 * N), ∑ μ : Fin M,
        ∑ ν : Fin Q.natDegree, C (C (q i j k μ ν)) * R a b m i j k μ ν = 0 := by
      ext r h
      simp only [finsetSum_coeff, coeff_C_mul, coeff_zero]
      by_cases hr : r < Q.natDegree
      · by_cases hh : h < Dx + 1
        · have := hq ((Fintype.equivFinOfCardEq hcard) (⟨a, ha⟩, ⟨b, hb⟩, ⟨m, hm⟩, ⟨h, hh⟩, ⟨r, hr⟩))
          simp only [Equiv.symm_apply_apply, Fin.val_mk] at this
          rw [← this]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun μ _ =>
              Finset.sum_congr rfl fun ν _ => mul_comm _ _
        · refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
            Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun μ _ =>
              Finset.sum_eq_zero fun ν _ => ?_
          rw [coeff_eq_zero_of_natDegree_lt ((hRx' a b m hm i j k μ ν r).trans_lt (by omega)),
            mul_zero]
      · refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
          Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun μ _ =>
            Finset.sum_eq_zero fun ν _ => ?_
        rw [coeff_eq_zero_of_natDegree_lt ((hRy a b m i j k μ ν).trans_le (by omega)), coeff_zero,
          mul_zero]
    have h0 := hRid a b m q
    rw [hV, eval₂_zero] at h0
    exact (mul_eq_zero.1 h0).resolve_left (hΛ a b m)

#print axioms solution
