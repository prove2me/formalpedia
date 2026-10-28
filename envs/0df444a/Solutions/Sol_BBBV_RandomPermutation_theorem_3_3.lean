-- Prove2me | solution 1 for BBBV.RandomPermutation.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-26T06:21:01.838525+00:00
-- url     : https://prove2.me/submissions/2daa00c0-6de3-4ded-aedb-9bb5feee1e17

import Definitions.Def_BBBV_RandomPermutation_QueryModel

/- The elementary norm and answer-translation arguments below adapt the proof of
BBBV.RandomOracle.theorem_3_5 by Prove2Me contributor sometik179,
submission e2e7a9e3-4271-44b5-b1f9-be6e2ccf812f (Apache-2.0).
The time-dependent, arbitrary-support hybrid argument is proved here. -/

noncomputable section
open Classical Finset BBBV.RandomPermutation
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace WentaoBBBVHybrid

variable {X R W : Type} [Fintype X] [Fintype R] [Fintype W] [AddCommGroup R]

private lemma oracle_some (f : X → R) (φ : State X R W) (x : X) (z : R) (w : W) :
    oracleOp f φ (some x, z, w) = φ (some x, z - f x, w) := by rfl

private lemma oracle_none (f : X → R) (φ : State X R W) (z : R) (w : W) :
    oracleOp f φ (none, z, w) = φ (none, z, w) := by rfl

private lemma norm_sub_sq (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_sub_le a b
  nlinarith [norm_nonneg (a - b), norm_nonneg a, norm_nonneg b,
    sq_nonneg (‖a‖ - ‖b‖)]

private lemma answer_translate (φ : State X R W) (y : X) (r : R) :
    (∑ z : R, ∑ w : W, ‖φ (some y, z - r, w)‖ ^ 2) = queryMag y φ := by
  unfold queryMag
  exact Fintype.sum_equiv (Equiv.subRight r) _ _ (fun _ => rfl)

private lemma queryMag_nonneg (y : X) (φ : State X R W) : 0 ≤ queryMag y φ := by
  exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

private lemma oracle_change_sq (f g : X → R) (S : Finset X)
    (hagree : ∀ x, x ∉ S → g x = f x) (φ : State X R W) :
    ‖oracleOp f φ - oracleOp g φ‖ ^ 2 ≤ 4 * ∑ x ∈ S, queryMag x φ := by
  classical
  have he : ‖oracleOp f φ - oracleOp g φ‖ ^ 2 =
      ∑ x : X, ∑ z : R, ∑ w : W,
        ‖φ (some x, z - f x, w) - φ (some x, z - g x, w)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fintype.sum_prod_type, PiLp.sub_apply, Fintype.sum_option]
    simp only [oracle_none, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, sum_const_zero, zero_add, oracle_some]
  rw [he]
  calc
    _ ≤ ∑ x : X, if x ∈ S then 4 * queryMag x φ else 0 := by
      apply sum_le_sum
      intro x _
      by_cases hx : x ∈ S
      · rw [if_pos hx]
        calc
          _ ≤ ∑ z : R, ∑ w : W,
              (2 * ‖φ (some x, z - f x, w)‖ ^ 2 +
               2 * ‖φ (some x, z - g x, w)‖ ^ 2) := by
            apply sum_le_sum; intro z _
            apply sum_le_sum; intro w _
            exact norm_sub_sq _ _
          _ = 4 * queryMag x φ := by
            simp_rw [sum_add_distrib, ← mul_sum]
            rw [answer_translate, answer_translate]
            ring
      · simp [hagree x hx, hx]
    _ = _ := by simp [← mul_sum]

private lemma oracle_change_le (f g : X → R) (S : Finset X)
    (hagree : ∀ x, x ∉ S → g x = f x) (φ : State X R W) :
    ‖oracleOp f φ - oracleOp g φ‖ ≤
      2 * Real.sqrt (∑ x ∈ S, queryMag x φ) := by
  have hs : 0 ≤ ∑ x ∈ S, queryMag x φ :=
    sum_nonneg fun x _ => queryMag_nonneg x φ
  have h := oracle_change_sq f g S hagree φ
  have hsq := Real.sq_sqrt hs
  nlinarith [Real.sqrt_nonneg (∑ x ∈ S, queryMag x φ),
    norm_nonneg (oracleOp f φ - oracleOp g φ)]

private lemma hybrid_sq {T : ℕ} (M : QueryAlg X R W T)
    (g₀ g₁ : Fin T → X → R) (S : Fin T → Finset X)
    (hagree : ∀ i x, x ∉ S i → g₁ i x = g₀ i x) :
    ‖final M g₀ - final M g₁‖ ^ 2 ≤
      4 * (T : ℝ) * ∑ i : Fin T, ∑ x ∈ S i, queryMag x (state M g₀ i.val) := by
  classical
  let q : ℕ → ℝ := fun i =>
    if h : i < T then ∑ x ∈ S ⟨i, h⟩, queryMag x (state M g₀ i) else 0
  have hq : ∀ i, 0 ≤ q i := by
    intro i
    dsimp [q]
    split_ifs
    · exact sum_nonneg fun x _ => queryMag_nonneg x _
    · exact le_rfl
  have hprefix : ∀ i, i ≤ T →
      ‖state M g₀ i - state M g₁ i‖ ≤
        2 * ∑ t ∈ range i, Real.sqrt (q t) := by
    intro i
    induction i with
    | zero => simp [state]
    | succ i ih =>
      intro hi
      have hit : i < T := by omega
      have ih' := ih (by omega)
      have hstep :
          ‖oracleOp (g₀ ⟨i, hit⟩) (state M g₀ i) -
              oracleOp (g₁ ⟨i, hit⟩) (state M g₀ i)‖ ≤
            2 * Real.sqrt (q i) := by
        simpa only [q, dif_pos hit] using
          oracle_change_le (g₀ ⟨i, hit⟩) (g₁ ⟨i, hit⟩) (S ⟨i, hit⟩)
            (hagree ⟨i, hit⟩) (state M g₀ i)
      have ht := norm_sub_le_norm_sub_add_norm_sub
        (oracleOp (g₀ ⟨i, hit⟩) (state M g₀ i))
        (oracleOp (g₁ ⟨i, hit⟩) (state M g₀ i))
        (oracleOp (g₁ ⟨i, hit⟩) (state M g₁ i))
      rw [← map_sub, (oracleOp (g₁ ⟨i, hit⟩)).norm_map] at ht
      have hrec : state M g₀ (i + 1) - state M g₁ (i + 1) =
          M.U ⟨i, hit⟩ (oracleOp (g₀ ⟨i, hit⟩) (state M g₀ i)) -
            M.U ⟨i, hit⟩ (oracleOp (g₁ ⟨i, hit⟩) (state M g₁ i)) := by
        simp only [state, Nat.rec_add_one, dif_pos hit]
      rw [hrec, ← map_sub, (M.U ⟨i, hit⟩).norm_map, sum_range_succ]
      linarith
  have hp := hprefix T le_rfl
  rw [← Fin.sum_univ_eq_sum_range] at hp
  have hc := sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin T))
    (fun _ => (1 : ℝ)) (fun i => Real.sqrt (q i.val))
  simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hc
  simp_rw [Real.sq_sqrt (hq _)] at hc
  have hn : 0 ≤ ∑ i : Fin T, Real.sqrt (q i.val) :=
    sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hqfin : ∀ i : Fin T, q i.val = ∑ x ∈ S i, queryMag x (state M g₀ i.val) := by
    intro i
    simp only [q, dif_pos i.isLt]
  change ‖final M g₀ - final M g₁‖ ≤ _ at hp
  have hs : ‖final M g₀ - final M g₁‖ ^ 2 ≤
      4 * (T : ℝ) * ∑ i : Fin T, q i.val := by
    nlinarith [norm_nonneg (final M g₀ - final M g₁)]
  simpa only [hqfin] using hs

end WentaoBBBVHybrid

open WentaoBBBVHybrid

theorem solution {X R W : Type} [Fintype X] [Fintype R] [Fintype W]
    [AddCommGroup R] {T : ℕ} (M : QueryAlg X R W T)
    (g₀ g₁ : Fin T → X → R) (F : Finset (Fin T × X))
    (hF₀ : ∀ i y, (i, y) ∉ F → g₁ i y = g₀ i y)
    (ε : ℝ) (hε : 0 < ε)
    (hF : (∑ p ∈ F, queryMag p.2 (state M g₀ p.1)) ≤ ε ^ 2 / (T : ℝ)) :
    ‖final M g₀ - final M g₁‖ ≤ 2 * ε := by
  classical
  let S : Fin T → Finset X := fun i => univ.filter fun y => (i, y) ∈ F
  have hagree : ∀ i y, y ∉ S i → g₁ i y = g₀ i y := by
    intro i y hy
    exact hF₀ i y (by simpa [S] using hy)
  have hmass : (∑ i : Fin T, ∑ x ∈ S i, queryMag x (state M g₀ i.val)) =
      ∑ p ∈ F, queryMag p.2 (state M g₀ p.1) := by
    simp only [S, sum_filter]
    symm
    calc
      _ = ∑ p : Fin T × X, if p ∈ F then queryMag p.2 (state M g₀ p.1) else 0 := by simp
      _ = _ := by rw [Fintype.sum_prod_type]
  have hh := hybrid_sq M g₀ g₁ S hagree
  rw [hmass] at hh
  by_cases hT : T = 0
  · subst T
    simp [final, state]
    linarith
  · have hTr : (0 : ℝ) < T := by exact_mod_cast (Nat.pos_of_ne_zero hT)
    have hb := (le_div_iff₀ hTr).mp hF
    nlinarith [norm_nonneg (final M g₀ - final M g₁)]
