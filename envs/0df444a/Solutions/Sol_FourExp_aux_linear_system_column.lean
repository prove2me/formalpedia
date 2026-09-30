-- Prove2me | solution 1 for FourExp.aux_linear_system_column
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T08:36:21.654723+00:00
-- url     : https://prove2.me/submissions/35854f65-82d8-4a1e-8cd2-17068694bb27

import Mathlib
import Theorems.Thm_FourExp_exists_pow_mul_pow_le_exp_sq_mul_sqrt_log

/-!
# The auxiliary linear system, in the column case

As in `FourExp.aux_linear_system`, with the reduced presentation of the derivatives as the
hypothesis `hpres`, the conclusion of `FourExp.exists_iteratedDeriv_reduced_presentation_column`,
whose `X`-degrees are at most `M + c (1 + m + S + T a)`.

Write `φ(P) = P(ω, ω₁)` for `P ∈ ℤ[X][Y]`, `S = ⌊N² / √(log N)⌋`, `t₁ = ⌊N / √(log N)⌋` and
`t₂ = ⌊N √(log N)⌋`, and take `T = 2 N`. For each point `a y₁ + b y₂` and order `m`,
`Λ F_q⁽ᵐ⁾(a y₁ + b y₂) = φ(∑ q_{ijkμν} R_{ijkμν})` with a nonzero `Λ` and integer polynomials
`R_{ijkμν}` of `Y`-degree below `deg Q` that do not depend on `q`. The equations of the system say
that every coefficient of `∑ q_{ijkμν} R_{ijkμν}` vanishes; then `F_q⁽ᵐ⁾(a y₁ + b y₂) = 0`.

On the points `a < t₁`, `N (a + 1) ≤ N t₁ ≤ N² / √(log N) < S + 1`, so `T a ≤ 2 S`, and at the
orders `m < S` the `X`-degrees are at most `M + c (1 + 4 S)`. With `M = (5 c + 1) S` they stay
below `2 M`, so there are at most half as many equations as unknowns. Each coefficient of the
system is at most the length of some `R_{ijkμν}`, hence at most `exp(κ N² √(log N))` by
`FourExp.exists_pow_mul_pow_le_exp_sq_mul_sqrt_log`.
-/

namespace T2_aux_linear_system_column

/-- A single integer coefficient of `P ∈ ℤ[X][Y]` is at most its length. -/
theorem natAbs_coeff_le_length (P : Polynomial (Polynomial ℤ)) (k i : ℕ) :
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

end T2_aux_linear_system_column

open Polynomial

theorem solution
    (x₁ x₂ y₁ y₂ : ℂ) (ω ω₁ : ℂ) (Q : Polynomial (Polynomial ℤ))
    (hpres : ∃ c : ℕ, ∀ S T M a b m : ℕ, ∃ Λ : ℂ, Λ ≠ 0 ∧
      ‖Λ‖ ≤ (c : ℝ) ^ (c * (1 + m + S + T * (a + b))) ∧
      ∃ R : Fin S → Fin T → Fin T → Fin M → Fin Q.natDegree → Polynomial (Polynomial ℤ),
        (∀ i j k μ ν, (R i j k μ ν).natDegree < Q.natDegree) ∧
        (∀ i j k μ ν, ∑ r ∈ (R i j k μ ν).support, ∑ h ∈ ((R i j k μ ν).coeff r).support,
            (((R i j k μ ν).coeff r).coeff h).natAbs ≤
          c ^ (c * (1 + m + S + T * (a + b))) * (1 + m + S + T + a + b) ^ (c * (1 + m + S))) ∧
        (∀ i j k μ ν r, ((R i j k μ ν).coeff r).natDegree ≤ M + c * (1 + m + S + T * a)) ∧
        ∀ q : Fin S → Fin T → Fin T → Fin M → Fin Q.natDegree → ℤ,
          Λ * iteratedDeriv m (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
              (∑ μ : Fin M, ∑ ν : Fin Q.natDegree,
                ((q i j k μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) * z ^ (i : ℕ) *
                Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z))
            ((a : ℂ) * y₁ + (b : ℂ) * y₂) =
          Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁
            (∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T, ∑ μ : Fin M, ∑ ν : Fin Q.natDegree,
              Polynomial.C (Polynomial.C (q i j k μ ν)) * R i j k μ ν)) :
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
  obtain ⟨c, hc⟩ := hpres
  -- `W S` powers of `ω` per unknown leave room for the `X`-degrees of the reduced values.
  obtain ⟨W, hW⟩ : ∃ W : ℕ, W = 5 * c + 1 := ⟨_, rfl⟩
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
  have hSlo : (N : ℝ) ^ 2 / Real.sqrt (Real.log N) <
      (⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
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
  generalize ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ = S at hSr hSlo hS1 ⊢
  generalize ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ = t₁ at h1r ht ⊢
  generalize ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ = t₂ at h2r ht ⊢
  -- The `X`-degrees grow with `T a = 2 N a`, and `N (a + 1) ≤ N t₁ ≤ N² / √(log N) < S + 1`.
  have hNa : ∀ a : ℕ, a < t₁ → 2 * N * a ≤ 2 * S := by
    intro a ha
    have ha' : (a : ℝ) + 1 ≤ (N : ℝ) / Real.sqrt (Real.log N) := by
      have : ((a + 1 : ℕ) : ℝ) ≤ t₁ := by exact_mod_cast Nat.succ_le_of_lt ha
      push_cast at this; linarith
    have h3 : ((N * a + N : ℕ) : ℝ) < ((S + 1 : ℕ) : ℝ) := by
      have h4 : (N : ℝ) * ((a : ℝ) + 1) ≤ (N : ℝ) * ((N : ℝ) / Real.sqrt (Real.log N)) :=
        mul_le_mul_of_nonneg_left ha' (by positivity)
      have h5 : (N : ℝ) * ((N : ℝ) / Real.sqrt (Real.log N)) =
          (N : ℝ) ^ 2 / Real.sqrt (Real.log N) := by ring
      push_cast; linarith
    have h6 : N * a + N < S + 1 := by exact_mod_cast h3
    rw [Nat.mul_assoc]; omega
  -- The unknowns: `W S` powers of `ω` and `deg Q` powers of `ω₁` per term.
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = W * S := ⟨_, rfl⟩
  -- The reduced values of the unknowns at every point and order.
  choose Λ hΛ _hΛn R hRy hRl hRx hRid using fun a b m : ℕ => hc S (2 * N) M a b m
  -- The common bound for their `X`-degrees at the points `a < t₁` and the orders `m < S`.
  obtain ⟨Dx, hDx⟩ : ∃ Dx : ℕ, Dx = M + c * (1 + S + S + 2 * S) := ⟨_, rfl⟩
  have hRx' : ∀ a b m : ℕ, a < t₁ → m < S → ∀ i j k μ ν r,
      ((R a b m i j k μ ν).coeff r).natDegree ≤ Dx := by
    intro a b m ha hm i j k μ ν r
    refine (hRx a b m i j k μ ν r).trans ?_
    rw [hDx]
    have := hNa a ha
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
    refine (Nat.cast_le.2 ((T2_aux_linear_system_column.natAbs_coeff_le_length _ r h).trans
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
          rw [coeff_eq_zero_of_natDegree_lt ((hRx' a b m ha hm i j k μ ν r).trans_lt (by omega)),
            mul_zero]
      · refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
          Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun μ _ =>
            Finset.sum_eq_zero fun ν _ => ?_
        rw [coeff_eq_zero_of_natDegree_lt ((hRy a b m i j k μ ν).trans_le (by omega)), coeff_zero,
          mul_zero]
    have h0 := hRid a b m q
    rw [hV, eval₂_zero] at h0
    exact (mul_eq_zero.1 h0).resolve_left (hΛ a b m)
