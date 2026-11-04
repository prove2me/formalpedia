-- Prove2me | solution 1 for ExtADMM.Orth.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @lisali126
-- created : 2026-11-04T02:35:30.973731+00:00
-- url     : https://prove2.me/submissions/b0fb5a3e-b10d-4920-8841-17639bdb21d3

import Mathlib
import Definitions.Def_ExtADMM_Orth_Setting

set_option autoImplicit false

open ExtADMM.Orth

/-- Transpose adjunction for the Euclidean pairing: `xᵀ(Aᵀl) = (Ax)ᵀl`. -/
theorem p2m_ll_tr {p n : ℕ} (A : Matrix (Fin p) (Fin n) ℝ) (x : Fin n → ℝ) (l : Fin p → ℝ) :
    dotProduct x (A.transpose.mulVec l) = dotProduct (A.mulVec x) l := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- `l ⬝ (r + t d) = l ⬝ r + t (l ⬝ d)`. -/
theorem p2m_lin_expand {p : ℕ} (l r d : Fin p → ℝ) (t : ℝ) :
    dotProduct l (r + t • d) = dotProduct l r + t * dotProduct l d := by
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul]

/-- `‖r + t d‖² = ‖r‖² + 2t (r ⬝ d) + t² ‖d‖²`. -/
theorem p2m_sq_expand {p : ℕ} (r d : Fin p → ℝ) (t : ℝ) :
    dotProduct (r + t • d) (r + t • d) =
      dotProduct r r + 2 * t * dotProduct r d + t ^ 2 * dotProduct d d := by
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm d r]
  ring

/-- If `a + t M ≥ 0` for every `t ∈ (0,1]`, then `a ≥ 0`. -/
theorem p2m_aux (a M : ℝ) (H : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ a + t * M) : 0 ≤ a := by
  by_contra hneg
  push_neg at hneg
  by_cases hM0 : M ≤ 0
  · have h1 := H 1 one_pos le_rfl
    linarith
  · have hM : 0 < M := not_le.mp hM0
    have hden : 0 < M - a := by linarith
    have hne : M - a ≠ 0 := ne_of_gt hden
    obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = -a / (M - a) := ⟨_, rfl⟩
    have ht : t * (M - a) = -a := by
      rw [ht_def]
      field_simp
    have ht0 : 0 < t := by
      rw [ht_def]
      exact div_pos (by linarith) hden
    have ht1 : t ≤ 1 := by
      rw [ht_def, div_le_one hden]
      linarith
    have h := H t ht0 ht1
    have key : (a + t * M) * (M - a) = -(a * a) := by linear_combination M * ht
    have h2 := mul_nonneg h hden.le
    rw [key] at h2
    have h3 := mul_pos_of_neg_of_neg hneg hneg
    linarith

/-- First-order optimality of one augmented-Lagrangian block subproblem.
If `x` minimizes `θ(y) - λᵀ(Ay + c) + (β/2)‖Ay + c‖²` over a convex set `X` with `θ` convex,
then `θ(y) - θ(x) + (y - x)ᵀ Aᵀ(-λ + β(Ax + c)) ≥ 0` for every `y ∈ X`. -/
theorem p2m_block_vi {n p : ℕ} (X : Set (Fin n → ℝ)) (θ : (Fin n → ℝ) → ℝ)
    (A : Matrix (Fin p) (Fin n) ℝ) (c lam : Fin p → ℝ) (β : ℝ)
    (hX : Convex ℝ X) (hθ : ConvexOn ℝ Set.univ θ) (x : Fin n → ℝ) (hx : x ∈ X)
    (hmin : ∀ y ∈ X,
      θ x - dotProduct lam (A.mulVec x + c) +
          β / 2 * dotProduct (A.mulVec x + c) (A.mulVec x + c) ≤
        θ y - dotProduct lam (A.mulVec y + c) +
          β / 2 * dotProduct (A.mulVec y + c) (A.mulVec y + c))
    (g : Fin n → ℝ) (hg : A.transpose.mulVec (-lam + β • (A.mulVec x + c)) = g)
    (y : Fin n → ℝ) (hy : y ∈ X) :
    0 ≤ θ y - θ x + dotProduct (y - x) g := by
  have H : ∀ t : ℝ, 0 < t → t ≤ 1 →
      0 ≤ (θ y - θ x - dotProduct lam (A.mulVec (y - x)) +
            β * dotProduct (A.mulVec x + c) (A.mulVec (y - x))) +
          t * (β / 2 * dotProduct (A.mulVec (y - x)) (A.mulVec (y - x))) := by
    intro t ht0 ht1
    have hz : (1 - t) • x + t • y ∈ X := hX hx hy (by linarith) ht0.le (by ring)
    have hθz : θ ((1 - t) • x + t • y) ≤ (1 - t) * θ x + t * θ y := by
      have h := hθ.2 (Set.mem_univ x) (Set.mem_univ y) (by linarith : (0 : ℝ) ≤ 1 - t)
        ht0.le (by ring)
      simp only [smul_eq_mul] at h
      exact h
    have hAz : A.mulVec ((1 - t) • x + t • y) + c =
        (A.mulVec x + c) + t • A.mulVec (y - x) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_sub]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    have hm := hmin _ hz
    rw [hAz] at hm
    rw [p2m_sq_expand] at hm
    rw [p2m_lin_expand] at hm
    have hprod : 0 ≤ t * ((θ y - θ x - dotProduct lam (A.mulVec (y - x)) +
            β * dotProduct (A.mulVec x + c) (A.mulVec (y - x))) +
          t * (β / 2 * dotProduct (A.mulVec (y - x)) (A.mulVec (y - x)))) := by
      nlinarith [hm, hθz]
    nlinarith [hprod, ht0]
  have ha := p2m_aux _ _ H
  rw [← hg, p2m_ll_tr, dotProduct_add, dotProduct_neg, dotProduct_smul, smul_eq_mul,
    dotProduct_comm (A.mulVec (y - x)) lam,
    dotProduct_comm (A.mulVec (y - x)) (A.mulVec x + c)]
  linarith [ha]

theorem solution {n1 n2 n3 p : ℕ} (P : Problem n1 n2 n3 p)
    (β : ℝ) (x1 : ℕ → Fin n1 → ℝ) (x2 : ℕ → Fin n2 → ℝ)
    (x3 : ℕ → Fin n3 → ℝ) (lam : ℕ → Fin p → ℝ)
    (hP : P.Standing) (hβ : 0 < β) (hrun : P.IsRun24 β x1 x2 x3 lam)
    (k : ℕ) :
    P.w x1 x2 x3 lam (k + 1) ∈ P.Omega ∧
      ∀ z ∈ P.Omega,
        0 ≤ P.theta z - P.theta (P.w x1 x2 x3 lam (k + 1)) +
          pair (z - P.w x1 x2 x3 lam (k + 1))
            (P.F (P.w x1 x2 x3 lam (k + 1)) +
              P.Qmul β (P.v x1 x3 lam k - P.v x1 x3 lam (k + 1))) := by
  obtain ⟨hX1c, -, hX2c, -, hX3c, -, hθ1, hθ2, hθ3, -⟩ := hP
  unfold Problem.IsRun24 at hrun
  obtain ⟨⟨hx2m, hx2min⟩, ⟨hx3m, hx3min⟩, hlam, ⟨hx1m, hx1min⟩⟩ := hrun k
  have hβ' : β ≠ 0 := ne_of_gt hβ
  refine ⟨?_, ?_⟩
  · show x1 (k + 1) ∈ P.X1 ∧ x2 (k + 1) ∈ P.X2 ∧ x3 (k + 1) ∈ P.X3
    exact ⟨hx1m, hx2m, hx3m⟩
  · intro z hz
    have hz' : z.x1 ∈ P.X1 ∧ z.x2 ∈ P.X2 ∧ z.x3 ∈ P.X3 := hz
    obtain ⟨hz1, hz2, hz3⟩ := hz'
    -- x₂-subproblem
    have h2 : 0 ≤ P.θ2 z.x2 - P.θ2 (x2 (k + 1)) +
        dotProduct (z.x2 - x2 (k + 1))
          (-(P.A2.transpose.mulVec (lam (k + 1))) +
            β • (P.A2.transpose.mulVec (P.A3.mulVec (x3 k - x3 (k + 1))))) := by
      refine p2m_block_vi P.X2 P.θ2 P.A2
        (P.A1.mulVec (x1 k) + P.A3.mulVec (x3 k) - P.b) (lam k) β hX2c hθ2
        (x2 (k + 1)) hx2m ?_ _ ?_ z.x2 hz2
      · intro y hy
        have hy' := hx2min y hy
        have hr : ∀ u, P.residual (x1 k) u (x3 k) =
            P.A2.mulVec u + (P.A1.mulVec (x1 k) + P.A3.mulVec (x3 k) - P.b) := by
          intro u
          simp only [Problem.residual]
          abel
        simp only [Problem.augLag, Problem.objective, hr] at hy'
        linarith
      · have hv : -(lam k) + β • (P.A2.mulVec (x2 (k + 1)) +
              (P.A1.mulVec (x1 k) + P.A3.mulVec (x3 k) - P.b)) =
            -(lam (k + 1)) + β • (P.A3.mulVec (x3 k - x3 (k + 1))) := by
          rw [hlam, Matrix.mulVec_sub]
          ext i
          simp only [Problem.residual, Pi.add_apply, Pi.neg_apply, Pi.sub_apply,
            Pi.smul_apply, smul_eq_mul]
          ring
        rw [hv, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_smul]
    -- x₃-subproblem
    have h3 : 0 ≤ P.θ3 z.x3 - P.θ3 (x3 (k + 1)) +
        dotProduct (z.x3 - x3 (k + 1)) (-(P.A3.transpose.mulVec (lam (k + 1))) + 0) := by
      refine p2m_block_vi P.X3 P.θ3 P.A3
        (P.A1.mulVec (x1 k) + P.A2.mulVec (x2 (k + 1)) - P.b) (lam k) β hX3c hθ3
        (x3 (k + 1)) hx3m ?_ _ ?_ z.x3 hz3
      · intro y hy
        have hy' := hx3min y hy
        have hr : ∀ u, P.residual (x1 k) (x2 (k + 1)) u =
            P.A3.mulVec u + (P.A1.mulVec (x1 k) + P.A2.mulVec (x2 (k + 1)) - P.b) := by
          intro u
          simp only [Problem.residual]
          abel
        simp only [Problem.augLag, Problem.objective, hr] at hy'
        linarith
      · have hv : -(lam k) + β • (P.A3.mulVec (x3 (k + 1)) +
              (P.A1.mulVec (x1 k) + P.A2.mulVec (x2 (k + 1)) - P.b)) =
            -(lam (k + 1)) := by
          rw [hlam]
          ext i
          simp only [Problem.residual, Pi.add_apply, Pi.neg_apply, Pi.sub_apply,
            Pi.smul_apply, smul_eq_mul]
          ring
        rw [hv, Matrix.mulVec_neg, add_zero]
    -- x₁-subproblem (solved last, with the updated multiplier)
    have h1 : 0 ≤ P.θ1 z.x1 - P.θ1 (x1 (k + 1)) +
        dotProduct (z.x1 - x1 (k + 1))
          (-(P.A1.transpose.mulVec (lam (k + 1))) +
            (-β • (P.A1.transpose.mulVec (P.A1.mulVec (x1 k - x1 (k + 1)))) +
              P.A1.transpose.mulVec (lam k - lam (k + 1)))) := by
      refine p2m_block_vi P.X1 P.θ1 P.A1
        (P.A2.mulVec (x2 (k + 1)) + P.A3.mulVec (x3 (k + 1)) - P.b) (lam (k + 1)) β hX1c hθ1
        (x1 (k + 1)) hx1m ?_ _ ?_ z.x1 hz1
      · intro y hy
        have hy' := hx1min y hy
        have hr : ∀ u, P.residual u (x2 (k + 1)) (x3 (k + 1)) =
            P.A1.mulVec u + (P.A2.mulVec (x2 (k + 1)) + P.A3.mulVec (x3 (k + 1)) - P.b) := by
          intro u
          simp only [Problem.residual]
          abel
        simp only [Problem.augLag, Problem.objective, hr] at hy'
        linarith
      · have hv : -(lam (k + 1)) + β • (P.A1.mulVec (x1 (k + 1)) +
              (P.A2.mulVec (x2 (k + 1)) + P.A3.mulVec (x3 (k + 1)) - P.b)) =
            -(lam (k + 1)) + (-β • (P.A1.mulVec (x1 k - x1 (k + 1))) +
              (lam k - lam (k + 1))) := by
          rw [hlam, Matrix.mulVec_sub]
          ext i
          simp only [Problem.residual, Pi.add_apply, Pi.neg_apply, Pi.sub_apply,
            Pi.smul_apply, smul_eq_mul]
          ring
        rw [hv, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_smul]
    -- λ-block: the multiplier component of F(w^{k+1}) + Q(v^k - v^{k+1}) vanishes
    have e4 : P.residual (x1 (k + 1)) (x2 (k + 1)) (x3 (k + 1)) +
        (P.A1.mulVec (x1 k - x1 (k + 1)) - β⁻¹ • (lam k - lam (k + 1))) = 0 := by
      rw [hlam, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hβ', one_smul]
      simp only [Problem.residual, Matrix.mulVec_sub]
      abel
    show 0 ≤ (P.θ1 z.x1 + P.θ2 z.x2 + P.θ3 z.x3) -
        (P.θ1 (x1 (k + 1)) + P.θ2 (x2 (k + 1)) + P.θ3 (x3 (k + 1))) +
      (dotProduct (z.x1 - x1 (k + 1))
          (-(P.A1.transpose.mulVec (lam (k + 1))) +
            (-β • (P.A1.transpose.mulVec (P.A1.mulVec (x1 k - x1 (k + 1)))) +
              P.A1.transpose.mulVec (lam k - lam (k + 1)))) +
        dotProduct (z.x2 - x2 (k + 1))
          (-(P.A2.transpose.mulVec (lam (k + 1))) +
            β • (P.A2.transpose.mulVec (P.A3.mulVec (x3 k - x3 (k + 1))))) +
        dotProduct (z.x3 - x3 (k + 1)) (-(P.A3.transpose.mulVec (lam (k + 1))) + 0) +
        dotProduct (z.lam - lam (k + 1))
          (P.residual (x1 (k + 1)) (x2 (k + 1)) (x3 (k + 1)) +
            (P.A1.mulVec (x1 k - x1 (k + 1)) - β⁻¹ • (lam k - lam (k + 1)))))
    rw [e4, dotProduct_zero]
    linarith [h1, h2, h3]
