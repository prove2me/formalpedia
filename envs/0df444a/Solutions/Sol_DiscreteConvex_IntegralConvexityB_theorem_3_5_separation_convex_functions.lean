-- Prove2me | solution 1 for DiscreteConvex.IntegralConvexityB.theorem_3_5_separation_convex_functions
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T02:17:04.134175+00:00
-- url     : https://prove2.me/submissions/06f8bb7e-426b-4106-a865-adad366965c6

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsProperConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsProperConcave
import Definitions.Def_DiscreteConvex_IntegralConvexityB_DomE
import Definitions.Def_DiscreteConvex_IntegralConvexityB_RelInt
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPolyhedralConcave
import Theorems.Thm_DiscreteConvex_IntegralConvexityB_theorem_3_9_farkas_lemma

open DiscreteConvex.IntegralConvexityB
open scoped BigOperators Matrix

variable {V : Type*} [Fintype V]

private lemma mem_domE_iff_epi {f : (V → ℝ) → EReal} (hf_nbot : NeverBot f) (x : V → ℝ) :
    x ∈ DomE f ↔ ∃ y : ℝ, (x, y) ∈ Epi f := by
  constructor
  · rintro ⟨h1, h2⟩
    lift f x to ℝ using ⟨h1, h2⟩ with y hy
    exact ⟨y, by simp [Epi, ← hy]⟩
  · rintro ⟨y, hy⟩
    refine ⟨?_, hf_nbot x⟩
    intro htop
    have hy' : (⊤ : EReal) ≤ (y : EReal) := htop ▸ hy
    exact EReal.coe_ne_top y (top_le_iff.mp hy')

private lemma mem_domE_iff_hypo {h : (V → ℝ) → EReal} (hh_ntop : NeverTop h) (x : V → ℝ) :
    x ∈ DomE h ↔ ∃ y : ℝ, (x, y) ∈ Hypo h := by
  constructor
  · rintro ⟨h1, h2⟩
    lift h x to ℝ using ⟨h1, h2⟩ with y hy
    exact ⟨y, by simp [Hypo, ← hy]⟩
  · rintro ⟨y, hy⟩
    refine ⟨hh_ntop x, ?_⟩
    intro hbot
    have hy' : (y : EReal) ≤ (⊥ : EReal) := hbot ▸ hy
    exact EReal.coe_ne_bot y (le_bot_iff.mp hy')

private lemma epi_ge_hypo_of_hge {f h : (V → ℝ) → EReal} (hge : ∀ x : V → ℝ, f x ≥ h x)
    {x : V → ℝ} {y1 y2 : ℝ} (h1 : (x, y1) ∈ Epi f) (h2 : (x, y2) ∈ Hypo h) :
    y2 ≤ y1 := by
  have h1' : f x ≤ (y1 : EReal) := h1
  have h2' : (y2 : EReal) ≤ h x := h2
  have h3 : (y2 : EReal) ≤ (y1 : EReal) := h2'.trans ((hge x).le.trans h1')
  exact EReal.coe_le_coe_iff.mp h3

private lemma sep_of_epi_hypo {f h : (V → ℝ) → EReal} (hf_nbot : NeverBot f) (hh_ntop : NeverTop h)
    (astar : ℝ) (pstar : V → ℝ)
    (hepi : ∀ x y1, (x, y1) ∈ Epi f → astar + dotProduct pstar x ≤ y1)
    (hhypo : ∀ x y2, (x, y2) ∈ Hypo h → y2 ≤ astar + dotProduct pstar x) :
    ∀ x : V → ℝ,
      f x ≥ (astar : EReal) + ((dotProduct pstar x : ℝ) : EReal) ∧
        (astar : EReal) + ((dotProduct pstar x : ℝ) : EReal) ≥ h x := by
  intro x
  rw [← EReal.coe_add]
  constructor
  · by_cases htop : f x = ⊤
    · rw [htop]; exact le_top
    · have hbot : f x ≠ ⊥ := hf_nbot x
      lift f x to ℝ using ⟨htop, hbot⟩ with y1 hy1
      have hle := hepi x y1 (by simp [Epi, ← hy1])
      exact EReal.coe_le_coe_iff.mpr hle
  · by_cases hbot : h x = ⊥
    · rw [hbot]; exact bot_le
    · have htop : h x ≠ ⊤ := hh_ntop x
      lift h x to ℝ using ⟨htop, hbot⟩ with y2 hy2
      have hle := hhypo x y2 (by simp [Hypo, ← hy2])
      exact EReal.coe_le_coe_iff.mpr hle

/-! ### Branch 2: Polyhedral Case via Farkas Lemma (Theorem 3.9) -/

private abbrev PolyRow (V : Type*) := V ⊕ (Bool ⊕ Unit)
private abbrev PolyCol (m1 m2 : ℕ) := (Fin m1 ⊕ Fin m2) ⊕ Unit

private def polyMatrix {m1 m2 : ℕ} (w1 : Fin m1 → V → ℝ) (c1 b1 : Fin m1 → ℝ)
    (w2 : Fin m2 → V → ℝ) (c2 b2 : Fin m2 → ℝ) : Matrix (PolyRow V) (PolyCol m1 m2) ℝ :=
  fun r col =>
    match r, col with
    | Sum.inl v, Sum.inl (Sum.inl i) => - w1 i v
    | Sum.inr (Sum.inl true), Sum.inl (Sum.inl i) => - c1 i
    | Sum.inr (Sum.inl false), Sum.inl (Sum.inl _) => 0
    | Sum.inr (Sum.inr ()), Sum.inl (Sum.inl i) => b1 i
    | Sum.inl v, Sum.inl (Sum.inr j) => - w2 j v
    | Sum.inr (Sum.inl true), Sum.inl (Sum.inr _) => 0
    | Sum.inr (Sum.inl false), Sum.inl (Sum.inr j) => - c2 j
    | Sum.inr (Sum.inr ()), Sum.inl (Sum.inr j) => b2 j
    | Sum.inl _, Sum.inr () => 0
    | Sum.inr (Sum.inl _), Sum.inr () => 0
    | Sum.inr (Sum.inr ()), Sum.inr () => 1

private def polyRhs : PolyRow V → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl true) => 1
  | Sum.inr (Sum.inl false) => -1
  | Sum.inr (Sum.inr ()) => 0

private lemma poly_vecMul_inl_inl {m1 m2 : ℕ} (w1 : Fin m1 → V → ℝ) (c1 b1 : Fin m1 → ℝ)
    (w2 : Fin m2 → V → ℝ) (c2 b2 : Fin m2 → ℝ) (y : PolyRow V → ℝ) (i : Fin m1) :
    Matrix.vecMul y (polyMatrix w1 c1 b1 w2 c2 b2) (Sum.inl (Sum.inl i)) =
      - (dotProduct (w1 i) (fun v => y (Sum.inl v)) + c1 i * y (Sum.inr (Sum.inl true))) +
        y (Sum.inr (Sum.inr ())) * b1 i := by
  simp only [Matrix.vecMul, dotProduct, polyMatrix, Fintype.sum_sum_type,
    Fintype.sum_bool, Fintype.sum_unique, mul_neg, mul_zero, add_zero]
  have hsum : ∑ x : V, -(y (Sum.inl x) * w1 i x) = - ∑ x : V, w1 i x * y (Sum.inl x) := by
    rw [Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  have hd : (default : Unit) = () := rfl
  rw [hsum, hd]
  ring

private lemma poly_vecMul_inl_inr {m1 m2 : ℕ} (w1 : Fin m1 → V → ℝ) (c1 b1 : Fin m1 → ℝ)
    (w2 : Fin m2 → V → ℝ) (c2 b2 : Fin m2 → ℝ) (y : PolyRow V → ℝ) (j : Fin m2) :
    Matrix.vecMul y (polyMatrix w1 c1 b1 w2 c2 b2) (Sum.inl (Sum.inr j)) =
      - (dotProduct (w2 j) (fun v => y (Sum.inl v)) + c2 j * y (Sum.inr (Sum.inl false))) +
        y (Sum.inr (Sum.inr ())) * b2 j := by
  simp only [Matrix.vecMul, dotProduct, polyMatrix, Fintype.sum_sum_type,
    Fintype.sum_bool, Fintype.sum_unique, mul_neg, mul_zero, zero_add]
  have hsum : ∑ x : V, -(y (Sum.inl x) * w2 j x) = - ∑ x : V, w2 j x * y (Sum.inl x) := by
    rw [Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  have hd : (default : Unit) = () := rfl
  rw [hsum, hd]
  ring

private lemma poly_vecMul_inr {m1 m2 : ℕ} (w1 : Fin m1 → V → ℝ) (c1 b1 : Fin m1 → ℝ)
    (w2 : Fin m2 → V → ℝ) (c2 b2 : Fin m2 → ℝ) (y : PolyRow V → ℝ) :
    Matrix.vecMul y (polyMatrix w1 c1 b1 w2 c2 b2) (Sum.inr ()) =
      y (Sum.inr (Sum.inr ())) := by
  simp only [Matrix.vecMul, dotProduct, polyMatrix, Fintype.sum_sum_type,
    Fintype.sum_unique, mul_zero, Finset.sum_const_zero, zero_add, mul_one]

private lemma poly_dot_rhs (y : PolyRow V → ℝ) :
    dotProduct y (polyRhs (V := V)) =
      y (Sum.inr (Sum.inl true)) - y (Sum.inr (Sum.inl false)) := by
  simp only [dotProduct, polyRhs, Fintype.sum_sum_type, Fintype.sum_bool,
    mul_zero, Finset.sum_const_zero, zero_add, add_zero, mul_one, mul_neg]
  ring

private lemma theorem_3_5_polyhedral (f h : (V → ℝ) → EReal)
    (hf : IsProperConvex f) (hh : IsProperConcave h)
    (hf_poly : IsPolyhedralConvex f) (hh_poly : IsPolyhedralConcave h)
    (hdom : (DomE f ∩ DomE h).Nonempty)
    (hge : ∀ x : V → ℝ, f x ≥ h x) :
    ∃ (astar : ℝ) (pstar : V → ℝ), ∀ x : V → ℝ,
      f x ≥ (astar : EReal) + ((dotProduct pstar x : ℝ) : EReal) ∧
        (astar : EReal) + ((dotProduct pstar x : ℝ) : EReal) ≥ h x := by
  rcases hf_poly with ⟨m1, w1, c1, b1, hepi_eq⟩
  rcases hh_poly with ⟨m2, w2, c2, b2, hhypo_eq⟩
  rcases hdom with ⟨x0, hx0_f, hx0_h⟩
  rcases (mem_domE_iff_epi hf.2.1 x0).mp hx0_f with ⟨y1_0, hy1_0⟩
  rcases (mem_domE_iff_hypo hh.2.1 x0).mp hx0_h with ⟨y2_0, hy2_0⟩
  have h_imp : ∀ (x : V → ℝ) (y1 y2 : ℝ),
      (∀ i : Fin m1, dotProduct (w1 i) x + c1 i * y1 ≤ b1 i) →
      (∀ j : Fin m2, dotProduct (w2 j) x + c2 j * y2 ≤ b2 j) →
      y2 ≤ y1 := by
    intro x y1 y2 h1 h2
    have he1 : (x, y1) ∈ Epi f := by rw [hepi_eq]; exact h1
    have hh2 : (x, y2) ∈ Hypo h := by rw [hhypo_eq]; exact h2
    exact epi_ge_hypo_of_hge hge he1 hh2
  have hx0_1 : ∀ i : Fin m1, dotProduct (w1 i) x0 + c1 i * y1_0 ≤ b1 i := by
    rw [hepi_eq] at hy1_0; exact hy1_0
  have hx0_2 : ∀ j : Fin m2, dotProduct (w2 j) x0 + c2 j * y2_0 ≤ b2 j := by
    rw [hhypo_eq] at hy2_0; exact hy2_0
  let A := polyMatrix w1 c1 b1 w2 c2 b2
  have hfarkas_cond : ∀ y : PolyRow V → ℝ,
      (∀ col, 0 ≤ Matrix.vecMul y A col) → 0 ≤ dotProduct y (polyRhs (V := V)) := by
    intro y hy
    rw [poly_dot_rhs]
    let x : V → ℝ := fun v => y (Sum.inl v)
    let y1 : ℝ := y (Sum.inr (Sum.inl true))
    let y2 : ℝ := y (Sum.inr (Sum.inl false))
    let t : ℝ := y (Sum.inr (Sum.inr ()))
    have ht : 0 ≤ t := by
      have := hy (Sum.inr ())
      rwa [poly_vecMul_inr] at this
    have hi : ∀ i : Fin m1, dotProduct (w1 i) x + c1 i * y1 ≤ t * b1 i := by
      intro i
      have := hy (Sum.inl (Sum.inl i))
      rw [poly_vecMul_inl_inl] at this
      linarith
    have hj : ∀ j : Fin m2, dotProduct (w2 j) x + c2 j * y2 ≤ t * b2 j := by
      intro j
      have := hy (Sum.inl (Sum.inr j))
      rw [poly_vecMul_inl_inr] at this
      linarith
    rcases ht.lt_or_eq with ht_pos | ht_zero
    · have h1' : ∀ i : Fin m1, dotProduct (w1 i) (t⁻¹ • x) + c1 i * (t⁻¹ * y1) ≤ b1 i := by
        intro i
        have hle := mul_le_mul_of_nonneg_left (hi i) (inv_nonneg.mpr ht_pos.le)
        rw [inv_mul_cancel_left₀ ht_pos.ne'] at hle
        rw [dotProduct_smul, smul_eq_mul]
        linarith
      have h2' : ∀ j : Fin m2, dotProduct (w2 j) (t⁻¹ • x) + c2 j * (t⁻¹ * y2) ≤ b2 j := by
        intro j
        have hle := mul_le_mul_of_nonneg_left (hj j) (inv_nonneg.mpr ht_pos.le)
        rw [inv_mul_cancel_left₀ ht_pos.ne'] at hle
        rw [dotProduct_smul, smul_eq_mul]
        linarith
      have hle := h_imp (t⁻¹ • x) (t⁻¹ * y1) (t⁻¹ * y2) h1' h2'
      have hle' := mul_le_mul_of_nonneg_left hle ht_pos.le
      rw [mul_inv_cancel_left₀ ht_pos.ne', mul_inv_cancel_left₀ ht_pos.ne'] at hle'
      linarith
    · have ht0 : t = 0 := ht_zero.symm
      by_contra hneg
      push_neg at hneg
      let s : ℝ := (|y1_0 - y2_0| + 1) / (y2 - y1)
      have hs_pos : 0 < s := by
        apply div_pos
        · positivity
        · linarith
      have h1' : ∀ i : Fin m1, dotProduct (w1 i) (x0 + s • x) + c1 i * (y1_0 + s * y1) ≤ b1 i := by
        intro i
        have hi0 := hi i
        rw [ht0, zero_mul] at hi0
        rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
        nlinarith [hx0_1 i, hi0, hs_pos]
      have h2' : ∀ j : Fin m2, dotProduct (w2 j) (x0 + s • x) + c2 j * (y2_0 + s * y2) ≤ b2 j := by
        intro j
        have hj0 := hj j
        rw [ht0, zero_mul] at hj0
        rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
        nlinarith [hx0_2 j, hj0, hs_pos]
      have hle := h_imp (x0 + s • x) (y1_0 + s * y1) (y2_0 + s * y2) h1' h2'
      have hs_eq : s * (y2 - y1) = |y1_0 - y2_0| + 1 :=
        div_mul_cancel₀ (|y1_0 - y2_0| + 1) (by linarith)
      have habs : y1_0 - y2_0 ≤ |y1_0 - y2_0| := le_abs_self (y1_0 - y2_0)
      linarith
  obtain ⟨lam, hlam_nn, hlam_eq⟩ :=
    (theorem_3_9_farkas_lemma A (polyRhs (V := V))).mpr hfarkas_cond
  let lam1 : Fin m1 → ℝ := fun i => lam (Sum.inl (Sum.inl i))
  let lam2 : Fin m2 → ℝ := fun j => lam (Sum.inl (Sum.inr j))
  let mu : ℝ := lam (Sum.inr ())
  have hlam1_nn : ∀ i, 0 ≤ lam1 i := fun i => hlam_nn (Sum.inl (Sum.inl i))
  have hlam2_nn : ∀ j, 0 ≤ lam2 j := fun j => hlam_nn (Sum.inl (Sum.inr j))
  have hmu_nn : 0 ≤ mu := hlam_nn (Sum.inr ())
  have hrow_v : ∀ v : V, ∑ i : Fin m1, lam1 i * w1 i v + ∑ j : Fin m2, lam2 j * w2 j v = 0 := by
    intro v
    have hv := congrFun hlam_eq (Sum.inl v)
    simp only [Matrix.mulVec, dotProduct, A, polyMatrix, polyRhs,
      Fintype.sum_sum_type, Fintype.sum_unique, zero_mul, add_zero] at hv
    change ∑ i : Fin m1, -w1 i v * lam1 i + ∑ j : Fin m2, -w2 j v * lam2 j = 0 at hv
    linarith [show ∑ i : Fin m1, -w1 i v * lam1 i = - ∑ i : Fin m1, lam1 i * w1 i v by
      rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun i _ => by ring,
      show ∑ j : Fin m2, -w2 j v * lam2 j = - ∑ j : Fin m2, lam2 j * w2 j v by
      rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun j _ => by ring]
  have hrow_y1 : ∑ i : Fin m1, lam1 i * c1 i = -1 := by
    have hy1 := congrFun hlam_eq (Sum.inr (Sum.inl true))
    simp only [Matrix.mulVec, dotProduct, A, polyMatrix, polyRhs,
      Fintype.sum_sum_type, Fintype.sum_unique, zero_mul, Finset.sum_const_zero, add_zero] at hy1
    change ∑ i : Fin m1, -c1 i * lam1 i = 1 at hy1
    linarith [show ∑ i : Fin m1, -c1 i * lam1 i = - ∑ i : Fin m1, lam1 i * c1 i by
      rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun i _ => by ring]
  have hrow_y2 : ∑ j : Fin m2, lam2 j * c2 j = 1 := by
    have hy2 := congrFun hlam_eq (Sum.inr (Sum.inl false))
    simp only [Matrix.mulVec, dotProduct, A, polyMatrix, polyRhs,
      Fintype.sum_sum_type, Fintype.sum_unique, zero_mul, Finset.sum_const_zero, zero_add, add_zero] at hy2
    change ∑ j : Fin m2, -c2 j * lam2 j = -1 at hy2
    linarith [show ∑ j : Fin m2, -c2 j * lam2 j = - ∑ j : Fin m2, lam2 j * c2 j by
      rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun j _ => by ring]
  have hrow_t : ∑ i : Fin m1, lam1 i * b1 i + ∑ j : Fin m2, lam2 j * b2 j ≤ 0 := by
    have ht := congrFun hlam_eq (Sum.inr (Sum.inr ()))
    simp only [Matrix.mulVec, dotProduct, A, polyMatrix, polyRhs,
      Fintype.sum_sum_type, Fintype.sum_unique, one_mul] at ht
    change ∑ i : Fin m1, b1 i * lam1 i + ∑ j : Fin m2, b2 j * lam2 j + mu = 0 at ht
    linarith [hmu_nn, show ∑ i : Fin m1, b1 i * lam1 i = ∑ i : Fin m1, lam1 i * b1 i by
      refine Finset.sum_congr rfl fun i _ => by ring,
      show ∑ j : Fin m2, b2 j * lam2 j = ∑ j : Fin m2, lam2 j * b2 j by
      refine Finset.sum_congr rfl fun j _ => by ring]
  let pstar : V → ℝ := fun v => ∑ i : Fin m1, lam1 i * w1 i v
  let astar : ℝ := - ∑ i : Fin m1, lam1 i * b1 i
  refine ⟨astar, pstar, sep_of_epi_hypo hf.2.1 hh.2.1 astar pstar ?_ ?_⟩
  · intro x y1 hxy1
    rw [hepi_eq] at hxy1
    have hsum_nn : 0 ≤ ∑ i : Fin m1, lam1 i * (b1 i - (dotProduct (w1 i) x + c1 i * y1)) := by
      refine Finset.sum_nonneg fun i _ => mul_nonneg (hlam1_nn i) ?_
      have := hxy1 i
      dsimp [LinFunc] at this
      linarith
    have hsum_eq : ∑ i : Fin m1, lam1 i * (b1 i - (dotProduct (w1 i) x + c1 i * y1)) =
        y1 - (astar + dotProduct pstar x) := by
      have hdot : dotProduct pstar x = ∑ i : Fin m1, lam1 i * dotProduct (w1 i) x := by
        dsimp [pstar, dotProduct]
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => by ring
      have hc : (∑ i : Fin m1, lam1 i * c1 i) * y1 = -y1 := by rw [hrow_y1]; ring
      calc ∑ i : Fin m1, lam1 i * (b1 i - (dotProduct (w1 i) x + c1 i * y1))
          = ∑ i : Fin m1, lam1 i * b1 i - ∑ i : Fin m1, lam1 i * dotProduct (w1 i) x -
              (∑ i : Fin m1, lam1 i * c1 i) * y1 := by
            rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun i _ => by ring
        _ = -astar - dotProduct pstar x - (-y1) := by
            rw [hdot, hc]; dsimp [astar]; ring
        _ = y1 - (astar + dotProduct pstar x) := by ring
    linarith
  · intro x y2 hxy2
    rw [hhypo_eq] at hxy2
    have hsum_nn : 0 ≤ ∑ j : Fin m2, lam2 j * (b2 j - (dotProduct (w2 j) x + c2 j * y2)) := by
      refine Finset.sum_nonneg fun j _ => mul_nonneg (hlam2_nn j) ?_
      have := hxy2 j
      dsimp [LinFunc] at this
      linarith
    have hpstar2 : ∀ v : V, ∑ j : Fin m2, lam2 j * w2 j v = - pstar v := by
      intro v; linarith [hrow_v v]
    have hdot2 : ∑ j : Fin m2, lam2 j * dotProduct (w2 j) x = - dotProduct pstar x := by
      dsimp [dotProduct]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      have : ∑ v : V, ∑ j : Fin m2, lam2 j * (w2 j v * x v) = ∑ v : V, (- pstar v) * x v := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← hpstar2 v, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [this]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun v _ => by ring
    have hc2 : (∑ j : Fin m2, lam2 j * c2 j) * y2 = y2 := by rw [hrow_y2]; ring
    have hsum_eq : ∑ j : Fin m2, lam2 j * (b2 j - (dotProduct (w2 j) x + c2 j * y2)) =
        ∑ j : Fin m2, lam2 j * b2 j + dotProduct pstar x - y2 := by
      calc ∑ j : Fin m2, lam2 j * (b2 j - (dotProduct (w2 j) x + c2 j * y2))
          = ∑ j : Fin m2, lam2 j * b2 j - ∑ j : Fin m2, lam2 j * dotProduct (w2 j) x -
              (∑ j : Fin m2, lam2 j * c2 j) * y2 := by
            rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ j : Fin m2, lam2 j * b2 j + dotProduct pstar x - y2 := by
            rw [hdot2, hc2]; ring
    linarith [hrow_t]

/-! ### Branch 1: Relative Interior Case via Geometric Hahn-Banach -/

private lemma relInt_shift_ball {S : Set (V → ℝ)} {x0 : V → ℝ} (hx0 : x0 ∈ RelInt S) :
    ∃ ε > 0, ∀ u ∈ vectorSpan ℝ S, ‖u‖ < ε → x0 + u ∈ S := by
  rcases hx0 with ⟨hx0_S, ε, hε, hsub⟩
  refine ⟨ε, hε, fun u hu hnorm => hsub ⟨?_, ?_⟩⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hnorm
  · have hx0_aff : x0 ∈ affineSpan ℝ S := subset_affineSpan ℝ S hx0_S
    have hdir : u ∈ (affineSpan ℝ S).direction := by
      rwa [direction_affineSpan]
    simpa [vadd_eq_add, add_comm] using AffineSubspace.vadd_mem_of_mem_direction hdir hx0_aff

private lemma comb_le_one_mem {E : Type*} [AddCommGroup E] [Module ℝ E]
    {K : Set E} (hK : Convex ℝ K) {p0 : E} (hp0 : p0 ∈ K)
    {n : ℕ} (t : Fin n → ℝ) (u : Fin n → E)
    (ht_nn : ∀ i, 0 ≤ t i) (ht_sum : ∑ i, t i ≤ 1) (hu : ∀ i, u i ∈ K) :
    ∑ i, t i • u i + (1 - ∑ i, t i) • p0 ∈ K := by
  let w : Fin (n + 1) → ℝ := Fin.cons (1 - ∑ i, t i) t
  let z : Fin (n + 1) → E := Fin.cons p0 u
  have hw_nn : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))), 0 ≤ w i := by
    intro i _
    refine Fin.cases ?_ ?_ i
    · simp only [w, Fin.cons_zero]; linarith
    · intro j; simp only [w, Fin.cons_succ]; exact ht_nn j
  have hw_sum : ∑ i : Fin (n + 1), w i = 1 := by
    rw [Fin.sum_univ_succ]
    simp only [w, Fin.cons_zero, Fin.cons_succ]
    ring
  have hz_mem : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))), z i ∈ K := by
    intro i _
    refine Fin.cases ?_ ?_ i
    · simp only [z, Fin.cons_zero]; exact hp0
    · intro j; simp only [z, Fin.cons_succ]; exact hu j
  have hmem := hK.sum_mem hw_nn hw_sum hz_mem
  rw [Fin.sum_univ_succ] at hmem
  simp only [w, z, Fin.cons_zero, Fin.cons_succ] at hmem
  rwa [add_comm] at hmem

private lemma theorem_3_5_relInt (f h : (V → ℝ) → EReal)
    (hf : IsProperConvex f) (hh : IsProperConcave h)
    (hri : (RelInt (DomE f) ∩ RelInt (DomE h)).Nonempty)
    (hge : ∀ x : V → ℝ, f x ≥ h x) :
    ∃ (astar : ℝ) (pstar : V → ℝ), ∀ x : V → ℝ,
      f x ≥ (astar : EReal) + ((dotProduct pstar x : ℝ) : EReal) ∧
        (astar : EReal) + ((dotProduct pstar x : ℝ) : EReal) ≥ h x := by
  classical
  rcases hri with ⟨x0, hx0_f, hx0_h⟩
  obtain ⟨ε1, hε1, hball1⟩ := relInt_shift_ball hx0_f
  obtain ⟨ε2, hε2, hball2⟩ := relInt_shift_ball hx0_h
  let W1 : Submodule ℝ (V → ℝ) := vectorSpan ℝ (DomE f)
  let W2 : Submodule ℝ (V → ℝ) := vectorSpan ℝ (DomE h)
  let W : Submodule ℝ (V → ℝ) := W1 ⊔ W2
  let Φ : (W1 × W2) →ₗ[ℝ] W :=
    (Submodule.inclusion (le_sup_left : W1 ≤ W)).comp (LinearMap.fst ℝ W1 W2) -
      (Submodule.inclusion (le_sup_right : W2 ≤ W)).comp (LinearMap.snd ℝ W1 W2)
  have hΦ_surj : Function.Surjective Φ := by
    rintro ⟨w, hw⟩
    rcases Submodule.mem_sup.mp hw with ⟨u, hu, v, hv, rfl⟩
    refine ⟨(⟨u, hu⟩, ⟨-v, W2.neg_mem hv⟩), ?_⟩
    ext
    simp [Φ]
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_rightInverse_of_surjective Φ (LinearMap.range_eq_top.mpr hΦ_surj)
  have hΨ_cont : Continuous Ψ := Ψ.continuous_of_finiteDimensional
  have hε_min : 0 < min ε1 ε2 := lt_min hε1 hε2
  obtain ⟨δ, hδ, hδ_ball⟩ := Metric.continuous_iff.mp hΨ_cont 0 (min ε1 ε2) hε_min
  have hΨ0 : Ψ 0 = 0 := map_zero Ψ
  have h_diff_dom : ∀ w : W, ‖w‖ < δ → ∃ x1 ∈ DomE f, ∃ x2 ∈ DomE h, w.1 = x1 - x2 := by
    intro w hw
    have hdist : dist (Ψ w) 0 < min ε1 ε2 := by
      rw [← hΨ0]
      exact hδ_ball w (by simpa [dist_zero_right] using hw)
    rw [dist_zero_right] at hdist
    have h1 : ‖(Ψ w).1.1‖ < ε1 :=
      (le_max_left ‖(Ψ w).1‖ ‖(Ψ w).2‖).trans_lt (hdist.trans_le (min_le_left _ _))
    have h2 : ‖(Ψ w).2.1‖ < ε2 :=
      (le_max_right ‖(Ψ w).1‖ ‖(Ψ w).2‖).trans_lt (hdist.trans_le (min_le_right _ _))
    refine ⟨x0 + (Ψ w).1.1, hball1 (Ψ w).1.1 (Ψ w).1.2 h1,
      x0 + (Ψ w).2.1, hball2 (Ψ w).2.1 (Ψ w).2.2 h2, ?_⟩
    have hΦΨ : Φ (Ψ w) = w := LinearMap.congr_fun hΨ w
    have hval : w.1 = (Ψ w).1.1 - (Ψ w).2.1 := congrArg Subtype.val hΦΨ.symm
    rw [hval]
    abel
  let K : Set (W × ℝ) :=
    {p | ∃ (x1 x2 : V → ℝ) (y1 y2 : ℝ),
      (x1, y1) ∈ Epi f ∧ (x2, y2) ∈ Hypo h ∧ p.1.1 = x1 - x2 ∧ p.2 = y1 - y2}
  have hK_conv : Convex ℝ K := by
    rintro ⟨w, r⟩ ⟨x1, x2, y1, y2, he1, hh1, hw1, hr1⟩
      ⟨w', r'⟩ ⟨x1', x2', y1', y2', he2, hh2, hw2, hr2⟩ a b ha hb hab
    refine ⟨a • x1 + b • x1', a • x2 + b • x2', a * y1 + b * y1', a * y2 + b * y2',
      hf.1 he1 he2 ha hb hab, hh.1 hh1 hh2 ha hb hab, ?_, ?_⟩
    · change a • w.1 + b • w'.1 = (a • x1 + b • x1') - (a • x2 + b • x2')
      change w.1 = x1 - x2 at hw1
      change w'.1 = x1' - x2' at hw2
      rw [hw1, hw2]; module
    · change a * r + b * r' = (a * y1 + b * y1') - (a * y2 + b * y2')
      change r = y1 - y2 at hr1
      change r' = y1' - y2' at hr2
      rw [hr1, hr2]; ring
  have hK_up : ∀ (w : W) (r t : ℝ), (w, r) ∈ K → r ≤ t → (w, t) ∈ K := by
    rintro w r t ⟨x1, x2, y1, y2, he1, hh1, hw, hr⟩ hrt
    refine ⟨x1, x2, y1 + (t - r), y2, ?_, hh1, hw, by linarith⟩
    change f x1 ≤ ((y1 + (t - r) : ℝ) : EReal)
    have he1' : f x1 ≤ (y1 : EReal) := he1
    exact he1'.trans (EReal.coe_le_coe_iff.mpr (by linarith))
  have hK_zero : ∀ r : ℝ, (0, r) ∈ K → 0 ≤ r := by
    rintro r ⟨x1, x2, y1, y2, he1, hh1, hw, hr⟩
    have hx : x1 = x2 := sub_eq_zero.mp hw.symm
    subst hx
    have hle := epi_ge_hypo_of_hge hge he1 hh1
    linarith
  have hK_dom : ∀ w : W, ‖w‖ < δ → ∃ r : ℝ, (w, r) ∈ K := by
    intro w hw
    obtain ⟨x1, hx1, x2, hx2, hwx⟩ := h_diff_dom w hw
    obtain ⟨y1, hy1⟩ := (mem_domE_iff_epi hf.2.1 x1).mp hx1
    obtain ⟨y2, hy2⟩ := (mem_domE_iff_hypo hh.2.1 x2).mp hx2
    exact ⟨y1 - y2, x1, x2, y1, y2, hy1, hy2, hwx, rfl⟩
  let d := Module.finrank ℝ W
  let b : Module.Basis (Fin d) ℝ W := Module.finBasis ℝ W
  let r0 : ℝ := δ / (2 * (∑ i : Fin d, ‖b i‖ + 1))
  have hr0_pos : 0 < r0 := by
    apply div_pos hδ
    have : 0 ≤ ∑ i : Fin d, ‖b i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
    linarith
  have hr0_norm : ∀ i : Fin d, ‖r0 • b i‖ < δ := by
    intro i
    rw [norm_smul, Real.norm_of_nonneg hr0_pos.le]
    have hi : ‖b i‖ ≤ ∑ j : Fin d, ‖b j‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg (b j)) (Finset.mem_univ i)
    have hden : 0 < 2 * (∑ j : Fin d, ‖b j‖ + 1) := by
      have : 0 ≤ ∑ j : Fin d, ‖b j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
      linarith
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith
  choose M_pos hM_pos using fun i : Fin d => hK_dom (r0 • b i) (hr0_norm i)
  choose M_neg hM_neg using fun i : Fin d => hK_dom (-(r0 • b i)) (by rw [norm_neg]; exact hr0_norm i)
  obtain ⟨M_0, hM_0⟩ := hK_dom 0 (by simpa using hδ)
  let M : ℝ := max M_0 (∑ i : Fin d, (|M_pos i| + |M_neg i|))
  have h0_M : ((0 : W), M) ∈ K := hK_up 0 M_0 M hM_0 (le_max_left _ _)
  have hpos_M : ∀ i : Fin d, (r0 • b i, M) ∈ K := by
    intro i
    refine hK_up (r0 • b i) (M_pos i) M (hM_pos i) ?_
    have h1 : M_pos i ≤ |M_pos i| + |M_neg i| :=
      (le_abs_self (M_pos i)).trans (le_add_of_nonneg_right (abs_nonneg (M_neg i)))
    have h2 : |M_pos i| + |M_neg i| ≤ ∑ j : Fin d, (|M_pos j| + |M_neg j|) :=
      Finset.single_le_sum (f := fun j => |M_pos j| + |M_neg j|) (fun j _ => by positivity) (Finset.mem_univ i)
    exact h1.trans (h2.trans (le_max_right M_0 _))
  have hneg_M : ∀ i : Fin d, (-(r0 • b i), M) ∈ K := by
    intro i
    refine hK_up (-(r0 • b i)) (M_neg i) M (hM_neg i) ?_
    have h1 : M_neg i ≤ |M_pos i| + |M_neg i| :=
      (le_abs_self (M_neg i)).trans (le_add_of_nonneg_left (abs_nonneg (M_pos i)))
    have h2 : |M_pos i| + |M_neg i| ≤ ∑ j : Fin d, (|M_pos j| + |M_neg j|) :=
      Finset.single_le_sum (f := fun j => |M_pos j| + |M_neg j|) (fun j _ => by positivity) (Finset.mem_univ i)
    exact h1.trans (h2.trans (le_max_right M_0 _))
  let U_W : Set W := {w : W | ∑ i : Fin d, |b.equivFun w i| < r0}
  have hU_W_open : IsOpen U_W := by
    refine isOpen_lt ?_ continuous_const
    refine continuous_finset_sum _ fun i _ => ?_
    exact continuous_abs.comp ((continuous_apply i).comp b.equivFun.toLinearMap.continuous_of_finiteDimensional)
  have h0_U_W : (0 : W) ∈ U_W := by
    simp [U_W, hr0_pos]
  have hU_sub_K : U_W ×ˢ Set.Ioi M ⊆ K := by
    rintro ⟨w, t⟩ ⟨hw_U, ht_M⟩
    refine hK_up w M t ?_ ht_M.le
    let c : Fin d → ℝ := fun i => b.equivFun w i / r0
    let t_w : Fin d → ℝ := fun i => |c i|
    let u_w : Fin d → W × ℝ := fun i => (if 0 ≤ c i then r0 • b i else -(r0 • b i), M)
    have ht_nn : ∀ i, 0 ≤ t_w i := fun i => abs_nonneg _
    have ht_sum : ∑ i : Fin d, t_w i ≤ 1 := by
      have h1 : ∑ i : Fin d, |c i| = (∑ i : Fin d, |b.equivFun w i|) / r0 := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp [c]
        rw [abs_div, abs_of_pos hr0_pos]
      rw [h1, div_le_one hr0_pos]
      exact hw_U.le
    have hu_mem : ∀ i : Fin d, u_w i ∈ K := by
      intro i
      dsimp [u_w]
      split_ifs
      · exact hpos_M i
      · exact hneg_M i
    have hcomb := comb_le_one_mem hK_conv h0_M t_w u_w ht_nn ht_sum hu_mem
    have hcomb_fst : (∑ i : Fin d, t_w i • u_w i + (1 - ∑ i : Fin d, t_w i) • ((0 : W), M)).1 = w := by
      change (LinearMap.fst ℝ W ℝ) (∑ i : Fin d, t_w i • u_w i + (1 - ∑ i : Fin d, t_w i) • ((0 : W), M)) = w
      rw [map_add, map_smul, map_sum]
      change ∑ i : Fin d, (t_w i • u_w i).1 + (1 - ∑ i : Fin d, t_w i) • (0 : W) = w
      rw [smul_zero, add_zero]
      have hstep : ∀ i : Fin d, (t_w i • u_w i).1 = (b.equivFun w i) • b i := by
        intro i
        change |c i| • (if 0 ≤ c i then r0 • b i else -(r0 • b i)) = (b.equivFun w i) • b i
        by_cases hci : 0 ≤ c i
        · rw [if_pos hci, abs_of_nonneg hci]
          dsimp [c]
          rw [smul_smul, div_mul_cancel₀ _ hr0_pos.ne']
        · rw [if_neg hci, abs_of_neg (not_le.mp hci)]
          dsimp [c]
          rw [smul_neg, neg_smul, neg_neg, smul_smul, div_mul_cancel₀ _ hr0_pos.ne']
      simp_rw [hstep]
      exact b.sum_equivFun w
    have hcomb_snd : (∑ i : Fin d, t_w i • u_w i + (1 - ∑ i : Fin d, t_w i) • ((0 : W), M)).2 = M := by
      change (LinearMap.snd ℝ W ℝ) (∑ i : Fin d, t_w i • u_w i + (1 - ∑ i : Fin d, t_w i) • ((0 : W), M)) = M
      rw [map_add, map_smul, map_sum]
      change ∑ i : Fin d, (t_w i * M) + (1 - ∑ i : Fin d, t_w i) * M = M
      rw [← Finset.sum_mul]
      ring
    have hcomb_eq : ∑ i : Fin d, t_w i • u_w i + (1 - ∑ i : Fin d, t_w i) • ((0 : W), M) = (w, M) :=
      Prod.ext hcomb_fst hcomb_snd
    rwa [hcomb_eq] at hcomb
  have hM1_int : ((0 : W), M + 1) ∈ interior K :=
    mem_interior.mpr ⟨U_W ×ˢ Set.Ioi M, hU_sub_K, hU_W_open.prod isOpen_Ioi, ⟨h0_U_W, by
      simp only [Set.mem_Ioi]; linarith⟩⟩
  have h0_not_int : ((0 : W), (0 : ℝ)) ∉ interior K := by
    intro h0_int
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0_int)
    have hmem : ((0 : W), -ε / 2) ∈ K := by
      apply hball
      rw [Metric.mem_ball, Prod.dist_eq]
      simp only [dist_self, dist_zero_right, Real.norm_eq_abs, max_lt_iff]
      refine ⟨hε, ?_⟩
      rw [abs_of_neg (by linarith)]
      linarith
    have := hK_zero (-ε / 2) hmem
    linarith
  obtain ⟨φ0, hφ0_int⟩ := geometric_hahn_banach_open_point hK_conv.interior isOpen_interior h0_not_int
  let φ : (W × ℝ) →L[ℝ] ℝ := -φ0
  have hφ_pos : ∀ p ∈ interior K, 0 < φ p := by
    intro p hp
    have hlt := hφ0_int p hp
    change φ0 p < φ0 0 at hlt
    rw [map_zero] at hlt
    change 0 < - φ0 p
    linarith
  have hφ_01_pos : 0 < φ (0, 1) := by
    let t0 : ℝ := |M + 1| + 1
    have ht0_pos : 0 < M + 1 + t0 := by
      have := neg_abs_le (M + 1)
      linarith
    have hmem_int : ((0 : W), M + 1 + t0) ∈ interior K :=
      mem_interior.mpr ⟨U_W ×ˢ Set.Ioi M, hU_sub_K, hU_W_open.prod isOpen_Ioi, ⟨h0_U_W, by
        simp only [Set.mem_Ioi]; linarith [abs_nonneg (M + 1)]⟩⟩
    have hpos := hφ_pos ((0 : W), M + 1 + t0) hmem_int
    have heq : ((0 : W), M + 1 + t0) = (M + 1 + t0) • ((0 : W), (1 : ℝ)) := by
      ext <;> simp
    rw [heq, map_smul, smul_eq_mul] at hpos
    exact (mul_pos_iff_of_pos_left ht0_pos).mp hpos
  obtain ⟨η, hη, hη_ball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hM1_int)
  have hφ_nonneg : ∀ p ∈ K, 0 ≤ φ p := by
    intro p hp
    by_contra hneg
    push_neg at hneg
    have hφ_M1 : 0 < φ (0, M + 1) := hφ_pos (0, M + 1) hM1_int
    let den : ℝ := φ (0, M + 1) - φ p
    have hden_pos : 0 < den := by dsimp [den]; linarith
    let θ : ℝ := (-φ p) / den
    have hθ_pos : 0 < θ := div_pos (by linarith) hden_pos
    have h1_sub_θ : 1 - θ = φ (0, M + 1) / den := by
      symm
      rw [eq_sub_iff_add_eq]
      dsimp [θ]
      rw [← add_div]
      have hnum : φ (0, M + 1) + -φ p = den := by dsimp [den]; ring
      rw [hnum, div_self hden_pos.ne']
    have h1_sub_pos : 0 < 1 - θ := by
      rw [h1_sub_θ]
      exact div_pos hφ_M1 hden_pos
    have hcombo_int : (1 - θ) • p + θ • ((0 : W), M + 1) ∈ interior K := by
      rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
      refine ⟨θ * η, mul_pos hθ_pos hη, fun z hz => ?_⟩
      let q : W × ℝ := ((0 : W), M + 1) + θ⁻¹ • (z - ((1 - θ) • p + θ • ((0 : W), M + 1)))
      have hq_ball : q ∈ Metric.ball ((0 : W), M + 1) η := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.mpr hθ_pos.le)]
        have hz' : ‖z - ((1 - θ) • p + θ • ((0 : W), M + 1))‖ < θ * η := by
          rwa [Metric.mem_ball, dist_eq_norm] at hz
        exact (inv_mul_lt_iff₀ hθ_pos).mpr hz'
      have hq_K : q ∈ K := hη_ball hq_ball
      have hz_eq : (1 - θ) • p + θ • q = z := by
        change (1 - θ) • p + θ • (((0 : W), M + 1) + θ⁻¹ • (z - ((1 - θ) • p + θ • ((0 : W), M + 1)))) = z
        rw [smul_add, smul_smul, mul_inv_cancel₀ hθ_pos.ne', one_smul, ← add_assoc, add_sub_cancel]
      rw [← hz_eq]
      exact hK_conv hp hq_K h1_sub_pos.le hθ_pos.le (sub_add_cancel 1 θ)
    have hpos := hφ_pos _ hcombo_int
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, h1_sub_θ] at hpos
    dsimp [θ] at hpos
    have hzero : φ (0, M + 1) / den * φ p + -φ p / den * φ (0, M + 1) = 0 := by ring
    linarith
  let c0 : ℝ := φ (0, 1)
  let L_W : W →ₗ[ℝ] ℝ :=
    { toFun := fun w => - (φ (w, 0)) / c0
      map_add' := fun w1 w2 => by
        have : (w1 + w2, (0 : ℝ)) = (w1, 0) + (w2, 0) := by ext <;> simp
        rw [this, map_add]; ring
      map_smul' := fun r w => by
        have : (r • w, (0 : ℝ)) = r • (w, (0 : ℝ)) := by ext <;> simp
        rw [this, map_smul, smul_eq_mul, RingHom.id_apply]; ring }
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
  let L : (V → ℝ) →ₗ[ℝ] ℝ :=
    L_W.comp ((LinearMap.fst ℝ W W').comp (Submodule.prodEquivOfIsCompl W W' hW').symm.toLinearMap)
  have hL_ext : ∀ w : W, L w.1 = L_W w := by
    intro w
    dsimp [L]
    have hprod : (Submodule.prodEquivOfIsCompl W W' hW') (w, 0) = w.1 := by
      change (w : V → ℝ) + (0 : V → ℝ) = w.1
      exact add_zero w.1
    have hsymm : (Submodule.prodEquivOfIsCompl W W' hW').symm w.1 = (w, 0) :=
      (Submodule.prodEquivOfIsCompl W W' hW').symm_apply_eq.mpr hprod.symm
    change L_W ((Submodule.prodEquivOfIsCompl W W' hW').symm w.1).1 = L_W w
    rw [hsymm]
  let pstar : V → ℝ := fun v => L (Pi.single v (1 : ℝ))
  have hL_dot : ∀ x : V → ℝ, L x = dotProduct pstar x := by
    intro x
    have hx : x = ∑ v : V, x v • (Pi.single v (1 : ℝ) : V → ℝ) := by
      ext v; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hx]
    rw [map_sum]
    dsimp [dotProduct, pstar]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have h_sep_ineq : ∀ (x1 x2 : V → ℝ) (y1 y2 : ℝ),
      (x1, y1) ∈ Epi f → (x2, y2) ∈ Hypo h →
      y2 - dotProduct pstar x2 ≤ y1 - dotProduct pstar x1 := by
    intro x1 x2 y1 y2 he1 hh2
    have hx1_dom : x1 ∈ DomE f := (mem_domE_iff_epi hf.2.1 x1).mpr ⟨y1, he1⟩
    have hx2_dom : x2 ∈ DomE h := (mem_domE_iff_hypo hh.2.1 x2).mpr ⟨y2, hh2⟩
    have hw1 : x1 - x0 ∈ W1 := vsub_mem_vectorSpan ℝ hx1_dom hx0_f.1
    have hw2 : x2 - x0 ∈ W2 := vsub_mem_vectorSpan ℝ hx2_dom hx0_h.1
    have hw : x1 - x2 ∈ W := by
      have : x1 - x2 = (x1 - x0) - (x2 - x0) := by abel
      rw [this]
      exact Submodule.sub_mem_sup hw1 hw2
    let w : W := ⟨x1 - x2, hw⟩
    have hmem_K : (w, y1 - y2) ∈ K := ⟨x1, x2, y1, y2, he1, hh2, rfl, rfl⟩
    have hφ_le := hφ_nonneg (w, y1 - y2) hmem_K
    have hdecomp : (w, y1 - y2) = (w, 0) + (y1 - y2) • ((0 : W), (1 : ℝ)) := by
      ext <;> simp
    rw [hdecomp, map_add, map_smul, smul_eq_mul] at hφ_le
    have hLW : φ (w, 0) = - c0 * L_W w := by
      change φ (w, 0) = - c0 * (- φ (w, 0) / c0)
      have hc0_ne : c0 ≠ 0 := hφ_01_pos.ne'
      rw [neg_mul, mul_comm c0, div_mul_cancel₀ _ hc0_ne, neg_neg]
    have hL_diff : L_W w = dotProduct pstar x1 - dotProduct pstar x2 := by
      rw [← hL_ext w]
      change L (x1 - x2) = _
      rw [map_sub, hL_dot, hL_dot]
    change 0 ≤ φ (w, 0) + (y1 - y2) * c0 at hφ_le
    rw [hLW, hL_diff] at hφ_le
    have : 0 ≤ c0 * ((y1 - dotProduct pstar x1) - (y2 - dotProduct pstar x2)) := by
      linarith
    have hdiff := (mul_nonneg_iff_of_pos_left hφ_01_pos).mp this
    linarith
  let S_hypo : Set ℝ := {v | ∃ x2 y2, (x2, y2) ∈ Hypo h ∧ v = y2 - dotProduct pstar x2}
  obtain ⟨y1_0, hy1_0⟩ := (mem_domE_iff_epi hf.2.1 x0).mp hx0_f.1
  obtain ⟨y2_0, hy2_0⟩ := (mem_domE_iff_hypo hh.2.1 x0).mp hx0_h.1
  have hS_ne : S_hypo.Nonempty := ⟨y2_0 - dotProduct pstar x0, x0, y2_0, hy2_0, rfl⟩
  have hS_bdd : BddAbove S_hypo := by
    refine ⟨y1_0 - dotProduct pstar x0, ?_⟩
    rintro v ⟨x2, y2, hh2, rfl⟩
    exact h_sep_ineq x0 x2 y1_0 y2 hy1_0 hh2
  let astar : ℝ := sSup S_hypo
  refine ⟨astar, pstar, sep_of_epi_hypo hf.2.1 hh.2.1 astar pstar ?_ ?_⟩
  · intro x1 y1 he1
    have hle : astar ≤ y1 - dotProduct pstar x1 := by
      refine csSup_le hS_ne ?_
      rintro v ⟨x2, y2, hh2, rfl⟩
      exact h_sep_ineq x1 x2 y1 y2 he1 hh2
    linarith
  · intro x2 y2 hh2
    have hle : y2 - dotProduct pstar x2 ≤ astar :=
      le_csSup hS_bdd ⟨x2, y2, hh2, rfl⟩
    linarith

theorem solution {V : Type*} [Fintype V] (f h : (V → ℝ) → EReal)
    (hf : IsProperConvex f) (hh : IsProperConcave h)
    (ha : (RelInt (DomE f) ∩ RelInt (DomE h)).Nonempty ∨
      (IsPolyhedralConvex f ∧ IsPolyhedralConcave h ∧ (DomE f ∩ DomE h).Nonempty))
    (hge : ∀ x : V → ℝ, f x ≥ h x) :
    ∃ (astar : ℝ) (pstar : V → ℝ), ∀ x : V → ℝ,
      f x ≥ (astar : EReal) + ((dotProduct pstar x : ℝ) : EReal) ∧
        (astar : EReal) + ((dotProduct pstar x : ℝ) : EReal) ≥ h x := by
  rcases ha with hri | ⟨hf_poly, hh_poly, hdom⟩
  · exact theorem_3_5_relInt f h hf hh hri hge
  · exact theorem_3_5_polyhedral f h hf hh hf_poly hh_poly hdom hge
