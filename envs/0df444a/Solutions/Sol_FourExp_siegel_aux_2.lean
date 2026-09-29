-- Prove2me | solution 2 for FourExp.siegel_aux
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-27T08:02:49.099245+00:00
-- url     : https://prove2.me/submissions/6edf2e47-9d7e-41c8-8f81-d49d3c6c3f4f

import Mathlib
import Theorems.Thm_Transcendence_siegel_entrywise

open Polynomial Finset

namespace FourExpSiegel

/-- A non-zero integer array gives a non-zero combination of `ω^μ ω₁^ν`, by minimality of `Q`. -/
lemma c_ne_zero {ω ω₁ : ℂ} {Q : Polynomial (Polynomial ℤ)} (hQd : 0 < Q.natDegree)
    (hQmin : ∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree →
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0)
    {M : ℕ} (a : Fin M → Fin Q.natDegree → ℤ) (ha : a ≠ 0) :
    ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((a μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ) ≠ 0 := by
  classical
  let f : Fin Q.natDegree → Polynomial ℤ := fun ν => ∑ μ : Fin M, monomial (μ : ℕ) (a μ ν)
  let P : Polynomial (Polynomial ℤ) := ∑ ν : Fin Q.natDegree, C (f ν) * X ^ (ν : ℕ)
  have hdeg : P.degree < Q.natDegree := Polynomial.degree_sum_fin_lt f
  have hnat : P.natDegree < Q.natDegree := by
    by_cases hP : P = 0
    · rw [hP, natDegree_zero]; exact hQd
    · exact (natDegree_lt_iff_degree_lt hP).2 hdeg
  have hev : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ P
      = ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((a μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ) := by
    simp only [P, f, eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_X_pow, Polynomial.coe_eval₂RingHom,
      eval₂_monomial, eq_intCast, Finset.sum_mul]
    rw [Finset.sum_comm]
  intro h
  apply ha
  have hP0 := hQmin P hnat (by rw [hev]; exact h)
  funext μ ν
  have hc := congrArg (fun p : Polynomial (Polynomial ℤ) => (p.coeff ν).coeff μ) hP0
  simp only [P, f, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero, Fin.val_inj, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, coeff_monomial] at hc
  simpa using hc

end FourExpSiegel

open FourExpSiegel in
theorem solution
    (ω ω₁ : ℂ) (Q : Polynomial (Polynomial ℤ)) (hQd : 0 < Q.natDegree)
    (hQmin : ∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree → Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0)
    (κ₁ : ℝ) (hκ₁ : 0 < κ₁) :
    ∃ κ : ℝ, κ₁ ≤ κ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∀ M : ℕ, 0 < M → (M : ℝ) ≤ κ₁ * ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → ∀ R : ℕ, 2 * R ≤ ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ * (2 * N) * (2 * N) * M * Q.natDegree →
      ∀ B : Fin R → Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → Fin (2 * N) → Fin (2 * N) → Fin M → Fin Q.natDegree → ℤ,
        (∀ e i j k' μ ν, |((B e i j k' μ ν : ℤ) : ℝ)| ≤ Real.exp (κ₁ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) →
        ∃ q : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → Fin (2 * N) → Fin (2 * N) → Fin M → Fin Q.natDegree → ℤ,
          (∀ e, ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N), ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, B e i j k' μ ν * q i j k' μ ν = 0) ∧
          (∀ i j k' μ ν, |((q i j k' μ ν : ℤ) : ℝ)| ≤ Real.exp (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) ∧
          (∃ i j k', (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k' ≠ 0) ∧
          (∀ i j k', ‖(fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k'‖ ≤ Real.exp (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) := by
  classical
  set W : ℝ := max 1 ‖ω‖ with hW
  set W₁ : ℝ := max 1 ‖ω₁‖ with hW₁
  have hW1 : 1 ≤ W := le_max_left _ _
  have hW₁1 : 1 ≤ W₁ := le_max_left _ _
  have hdpos : (0 : ℝ) < Q.natDegree := by exact_mod_cast hQd
  refine ⟨κ₁ + 2, by linarith,
    max 3 (max ⌈7776 * κ₁ * Q.natDegree⌉₊ (max ⌈W ^ (3 * κ₁)⌉₊ ⌈3 * Q.natDegree * Real.log W₁⌉₊)), ?_⟩
  intro N hN M hM0 hMle R hR B hB
  -- thresholds
  have hN3 : (3 : ℝ) ≤ N := by
    have : 3 ≤ N := (le_max_left _ _).trans hN.le
    exact_mod_cast this
  have hT2 : 7776 * κ₁ * Q.natDegree ≤ (N : ℝ) := by
    have : ⌈7776 * κ₁ * Q.natDegree⌉₊ ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN.le
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  have hT3 : W ^ (3 * κ₁) ≤ (N : ℝ) := by
    have : ⌈W ^ (3 * κ₁)⌉₊ ≤ N :=
      (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hN.le
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  have hT4 : 3 * Q.natDegree * Real.log W₁ ≤ (N : ℝ) := by
    have : ⌈3 * Q.natDegree * Real.log W₁⌉₊ ≤ N :=
      (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hN.le
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  -- logarithms
  have hL1 : 1 ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hsL : 1 ≤ Real.sqrt (Real.log (N : ℝ)) := Real.one_le_sqrt.2 hL1
  have hsq : Real.sqrt (Real.log (N : ℝ)) * Real.sqrt (Real.log (N : ℝ)) = Real.log (N : ℝ) := Real.mul_self_sqrt (by linarith)
  have hN0 : (0 : ℝ) ≤ N := by linarith
  set A := (N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ)) with hA
  have hN2A : (N : ℝ) ^ 2 ≤ A := le_mul_of_one_le_right (by positivity) hsL
  have hA0 : 0 ≤ A := (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2).trans hN2A
  have hNN2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  -- sizes
  have hSle : (⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) ≤ (N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ)) := Nat.floor_le (by positivity)
  have hSle2 : (⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) ≤ (N : ℝ) ^ 2 := hSle.trans (div_le_self (by positivity) hsL)
  have hS1 : 1 ≤ ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ := by
    rw [Nat.one_le_floor_iff, one_le_div (by positivity)]
    have hLN : Real.log (N : ℝ) ≤ N := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < N); linarith
    nlinarith
  have hMle2 : (M : ℝ) ≤ κ₁ * (N : ℝ) ^ 2 := hMle.trans (mul_le_mul_of_nonneg_left hSle2 hκ₁.le)
  have hn : ((⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ * (2 * N) * (2 * N) * M * Q.natDegree : ℕ) : ℝ) ≤ 4 * κ₁ * Q.natDegree * (N : ℝ) ^ 6 := by
    push_cast
    calc (⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ : ℝ) * (2 * N) * (2 * N) * M * Q.natDegree ≤ (N : ℝ) ^ 2 * (2 * N) * (2 * N) * (κ₁ * (N : ℝ) ^ 2) * Q.natDegree := by
          gcongr
      _ = 4 * κ₁ * Q.natDegree * (N : ℝ) ^ 6 := by ring
  have h8 : ((N : ℝ) ^ 2 / 3) ^ 4 / 24 ≤ Real.exp ((N : ℝ) ^ 2 / 3) := by
    have := Real.pow_div_factorial_le_exp (x := (N : ℝ) ^ 2 / 3) (by positivity) 4
    simpa [Nat.factorial] using this
  have hnexp : ((⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ * (2 * N) * (2 * N) * M * Q.natDegree : ℕ) : ℝ) ≤ Real.exp (A / 3) := by
    have hN2big : 7776 * κ₁ * Q.natDegree ≤ (N : ℝ) ^ 2 := hT2.trans hNN2
    calc ((⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ * (2 * N) * (2 * N) * M * Q.natDegree : ℕ) : ℝ) ≤ 4 * κ₁ * Q.natDegree * (N : ℝ) ^ 6 := hn
      _ ≤ ((N : ℝ) ^ 2 / 3) ^ 4 / 24 := by
          have h6 : 0 ≤ (N : ℝ) ^ 6 := by positivity
          nlinarith
      _ ≤ Real.exp ((N : ℝ) ^ 2 / 3) := h8
      _ ≤ Real.exp (A / 3) := Real.exp_le_exp.2 (by linarith)
  have hWM : W ^ M ≤ Real.exp (A / 3) := by
    have hlogW : 0 ≤ Real.log W := Real.log_nonneg hW1
    have h3 : 3 * κ₁ * Real.log W ≤ Real.log (N : ℝ) := by
      have := Real.log_le_log (Real.rpow_pos_of_pos (by linarith) _) hT3
      rwa [Real.log_rpow (by linarith)] at this
    rw [← Real.exp_log (by linarith : (0 : ℝ) < W), ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hMs : (M : ℝ) * Real.sqrt (Real.log (N : ℝ)) ≤ κ₁ * (N : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hMle (Real.sqrt_nonneg (Real.log (N : ℝ)))
      calc (M : ℝ) * Real.sqrt (Real.log (N : ℝ)) ≤ κ₁ * ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ * Real.sqrt (Real.log (N : ℝ)) := this
        _ ≤ κ₁ * ((N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))) * Real.sqrt (Real.log (N : ℝ)) := by gcongr
        _ = κ₁ * (N : ℝ) ^ 2 := by field_simp
    have key : (M : ℝ) * Real.log W * Real.log (N : ℝ) ≤ A / 3 * Real.log (N : ℝ) := by
      calc (M : ℝ) * Real.log W * Real.log (N : ℝ) = (M * Real.sqrt (Real.log (N : ℝ))) * (Real.log W * Real.sqrt (Real.log (N : ℝ))) := by
            rw [show (M : ℝ) * Real.log W * Real.log (N : ℝ) = (M : ℝ) * Real.log W *
              (Real.sqrt (Real.log (N : ℝ)) * Real.sqrt (Real.log (N : ℝ))) by rw [hsq]]
            ring
        _ ≤ (κ₁ * (N : ℝ) ^ 2) * (Real.log W * Real.sqrt (Real.log (N : ℝ))) := by gcongr
        _ = (N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ)) / 3 * (3 * κ₁ * Real.log W) := by ring
        _ ≤ (N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ)) / 3 * Real.log (N : ℝ) := by gcongr
        _ = A / 3 * Real.log (N : ℝ) := by rw [hA]
    exact le_of_mul_le_mul_right key (by linarith)
  have hW₁d : W₁ ^ Q.natDegree ≤ Real.exp (A / 3) := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < W₁), ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    linarith
  -- Siegel
  let β := Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ × Fin (2 * N) × Fin (2 * N) × Fin M × Fin Q.natDegree
  have hβcard : Fintype.card β = ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ * (2 * N) * (2 * N) * M * Q.natDegree := by
    simp only [β, Fintype.card_prod, Fintype.card_fin]; ring
  have hβpos : 0 < Fintype.card β := by
    rw [hβcard]
    have h2N : 0 < 2 * N := by
      have : 3 ≤ N := (le_max_left _ _).trans hN.le
      omega
    positivity
  set K := Real.exp (κ₁ * A) with hK
  have hK1 : 1 ≤ K := Real.one_le_exp (mul_nonneg hκ₁.le hA0)
  obtain ⟨t, ht0, hts, htb⟩ := Transcendence.siegel_entrywise
    (fun (e : Fin R) (u : β) => B e u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2)
    hβpos (by rw [Fintype.card_fin, hβcard]; exact hR) hK1 (fun e u => hB _ _ _ _ _ _)
  have hqb : ∀ u : β, |((t u : ℤ) : ℝ)| ≤ Real.exp (A / 3) * K := by
    intro u
    refine (htb u).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [hβcard]; exact hnexp
  have hfinal : Real.exp (A / 3) * K ≤ Real.exp ((κ₁ + 2) * A) := by
    rw [hK, ← Real.exp_add]; apply Real.exp_le_exp.2; linarith
  refine ⟨fun i j k' μ ν => t (i, j, k', μ, ν), fun e => ?_, fun i j k' μ ν => (hqb _).trans hfinal, ?_, ?_⟩
  · have := hts e
    simp only [β, Fintype.sum_prod_type] at this
    exact this
  · obtain ⟨u, hu⟩ := Function.ne_iff.1 ht0
    obtain ⟨i, j, k', μ, ν⟩ := u
    refine ⟨i, j, k', c_ne_zero hQd hQmin (fun μ ν => t (i, j, k', μ, ν)) ?_⟩
    intro h
    exact hu (congrFun (congrFun h μ) ν)
  · intro i j k'
    have hterm : ∀ μ : Fin M, ∀ ν : Fin Q.natDegree,
        ‖((t (i, j, k', μ, ν) : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)‖
          ≤ Real.exp (A / 3) * K * (W ^ M * W₁ ^ Q.natDegree) := by
      intro μ ν
      rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_intCast]
      have hω : ‖ω‖ ^ (μ : ℕ) ≤ W ^ M :=
        (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans (pow_le_pow_right₀ hW1 μ.2.le)
      have hω₁ : ‖ω₁‖ ^ (ν : ℕ) ≤ W₁ ^ Q.natDegree :=
        (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans (pow_le_pow_right₀ hW₁1 ν.2.le)
      calc |((t (i, j, k', μ, ν) : ℤ) : ℝ)| * ‖ω‖ ^ (μ : ℕ) * ‖ω₁‖ ^ (ν : ℕ)
          ≤ (Real.exp (A / 3) * K) * W ^ M * W₁ ^ Q.natDegree := by gcongr; exact hqb _
        _ = Real.exp (A / 3) * K * (W ^ M * W₁ ^ Q.natDegree) := by ring
    have hMd : (M : ℝ) * Q.natDegree ≤ Real.exp (A / 3) := by
      refine le_trans ?_ hnexp
      push_cast
      have hS1' : (1 : ℝ) ≤ ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ := by exact_mod_cast hS1
      have h2N' : (1 : ℝ) ≤ 2 * N := by linarith
      have h1 : (1 : ℝ) ≤ ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ * (2 * N) * (2 * N) :=
        one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hS1' h2N') h2N'
      calc (M : ℝ) * Q.natDegree = 1 * ((M : ℝ) * Q.natDegree) := by ring
        _ ≤ (⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ * (2 * N) * (2 * N)) * ((M : ℝ) * Q.natDegree) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ * (2 * N) * (2 * N) * M * Q.natDegree := by ring
    calc ‖∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((t (i, j, k', μ, ν) : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)‖
        ≤ ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ‖((t (i, j, k', μ, ν) : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => norm_sum_le _ _)
      _ ≤ ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, Real.exp (A / 3) * K * (W ^ M * W₁ ^ Q.natDegree) :=
          Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun ν _ => hterm μ ν
      _ = ((M : ℝ) * Q.natDegree) * (Real.exp (A / 3) * K * (W ^ M * W₁ ^ Q.natDegree)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ Real.exp (A / 3) * (Real.exp (A / 3) * K * (Real.exp (A / 3) * Real.exp (A / 3))) := by
          gcongr
      _ ≤ Real.exp ((κ₁ + 2) * A) := by
          rw [hK, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.2; linarith

#print axioms solution
