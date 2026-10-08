-- Prove2me | solution 1 for BoydADMM.Prox.quadratic_xUpdate
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:27:06.889407+00:00
-- url     : https://prove2.me/submissions/6f9ec180-d8d8-456a-b93d-148ead5f889a

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix


namespace BoydADMM.Prox

theorem ipE {k : ℕ} (a b : EuclideanSpace ℝ (Fin k)) : inner ℝ a b = a.ofLp ⬝ᵥ b.ofLp := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

theorem nsqE {k : ℕ} (a : EuclideanSpace ℝ (Fin k)) : ‖a‖ ^ 2 = a.ofLp ⬝ᵥ a.ofLp := by
  rw [← real_inner_self_eq_norm_sq, ipE]

theorem quadObj_eq {n p : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (q : EuclideanSpace ℝ (Fin n)) (r : ℝ) (A : Matrix (Fin p) (Fin n) ℝ) (ρ : ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (y : EuclideanSpace ℝ (Fin n)) :
    quadObj P q r y + (ρ / 2) * ‖Matrix.toEuclideanLin A y - v‖ ^ 2 =
      (1 / 2) * (y.ofLp ⬝ᵥ ((P + ρ • (Aᵀ * A)) *ᵥ y.ofLp))
        - (ρ • (Aᵀ *ᵥ v.ofLp) - q.ofLp) ⬝ᵥ y.ofLp + (r + (ρ / 2) * (v.ofLp ⬝ᵥ v.ofLp)) := by
  unfold quadObj
  rw [ipE, ipE, nsqE]
  have h1 : (Matrix.toEuclideanLin P y).ofLp = P *ᵥ y.ofLp := rfl
  have h2 : (Matrix.toEuclideanLin A y - v).ofLp = A *ᵥ y.ofLp - v.ofLp := rfl
  rw [h1, h2]
  set u := y.ofLp
  set w := v.ofLp
  have hAA : (A *ᵥ u) ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ ((Aᵀ * A) *ᵥ u) := by
    rw [← mulVec_mulVec, dotProduct_mulVec (A *ᵥ u) A u, ← mulVec_transpose, dotProduct_comm]
  have hAv : (A *ᵥ u) ⬝ᵥ w = (Aᵀ *ᵥ w) ⬝ᵥ u := by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose]
  rw [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, smul_eq_mul]
  rw [hAA, dotProduct_comm w (A *ᵥ u), hAv]
  ring

theorem quad_core {n p : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (q : EuclideanSpace ℝ (Fin n)) (r : ℝ) (A : Matrix (Fin p) (Fin n) ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hinv : IsUnit (P + ρ • (Aᵀ * A))) :
    (P + ρ • (Aᵀ * A)).PosDef ∧
      ∀ (v : EuclideanSpace ℝ (Fin p)) (x : EuclideanSpace ℝ (Fin n)),
        IsXUpdate Set.univ (quadObj P q r) ρ A v x ↔
          x = Matrix.toEuclideanLin (P + ρ • (Aᵀ * A))⁻¹
            (ρ • Matrix.toEuclideanLin Aᵀ v - q) := by
  set M := P + ρ • (Aᵀ * A) with hM
  have hpsd : M.PosSemidef := by
    apply hP.add
    have := posSemidef_conjTranspose_mul_self A
    rw [conjTranspose_eq_transpose_of_trivial] at this
    exact this.smul hρ.le
  have hpd : M.PosDef := hpsd.posDef_iff_isUnit.mpr hinv
  refine ⟨hpd, ?_⟩
  intro v x
  have hsym : Mᵀ = M := by
    have := hpd.1.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  set b := ρ • (Aᵀ *ᵥ v.ofLp) - q.ofLp with hb
  have hbE : (ρ • Matrix.toEuclideanLin Aᵀ v - q).ofLp = b := rfl
  set s := M⁻¹ *ᵥ b with hs
  have hMs : M *ᵥ s = b := by
    rw [hs, mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det M).mp hinv), one_mulVec]
  have hxs : (Matrix.toEuclideanLin M⁻¹ (ρ • Matrix.toEuclideanLin Aᵀ v - q)).ofLp = s := by
    show M⁻¹ *ᵥ (ρ • Matrix.toEuclideanLin Aᵀ v - q).ofLp = s
    rw [hbE]
  -- completing the square
  have csq : ∀ u : Fin n → ℝ, (1 / 2) * (u ⬝ᵥ (M *ᵥ u)) - b ⬝ᵥ u =
      (1 / 2) * ((u - s) ⬝ᵥ (M *ᵥ (u - s))) - (1 / 2) * (s ⬝ᵥ b) := by
    intro u
    have e1 : s ⬝ᵥ (M *ᵥ u) = b ⬝ᵥ u := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hsym, hMs]
    rw [mulVec_sub, hMs]
    simp only [sub_dotProduct, dotProduct_sub]
    rw [e1, dotProduct_comm u b]
    ring
  have key : ∀ y : EuclideanSpace ℝ (Fin n),
      quadObj P q r y + (ρ / 2) * ‖Matrix.toEuclideanLin A y - v‖ ^ 2 =
        (1 / 2) * ((y.ofLp - s) ⬝ᵥ (M *ᵥ (y.ofLp - s))) - (1 / 2) * (s ⬝ᵥ b)
          + (r + (ρ / 2) * (v.ofLp ⬝ᵥ v.ofLp)) := by
    intro y
    rw [quadObj_eq, ← csq]
  have qnn : ∀ u : Fin n → ℝ, 0 ≤ u ⬝ᵥ (M *ᵥ u) := by
    intro u; have := hpsd.dotProduct_mulVec_nonneg u; simpa using this
  unfold IsXUpdate
  simp only [Set.mem_univ, true_and, forall_const, key]
  constructor
  · intro h
    have h1 := h (WithLp.toLp 2 s)
    simp only [WithLp.ofLp_toLp, sub_self, mulVec_zero, dotProduct_zero, mul_zero] at h1
    have h2 : (x.ofLp - s) ⬝ᵥ (M *ᵥ (x.ofLp - s)) ≤ 0 := by linarith
    by_contra hne
    have hne' : x.ofLp - s ≠ 0 := by
      intro h0
      apply hne
      have : x.ofLp = s := sub_eq_zero.mp h0
      ext i
      rw [← hxs] at this
      exact congrFun this i
    have := hpd.dotProduct_mulVec_pos hne'
    simp only [star_trivial] at this
    linarith
  · intro hx y
    have : x.ofLp = s := by rw [hx, hxs]
    rw [this]
    simp only [sub_self, mulVec_zero, dotProduct_zero, mul_zero]
    have := qnn (y.ofLp - s)
    linarith

end BoydADMM.Prox

open BoydADMM.Prox


theorem solution {n p : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (q : EuclideanSpace ℝ (Fin n)) (r : ℝ) (A : Matrix (Fin p) (Fin n) ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hinv : IsUnit (P + ρ • (Aᵀ * A))) :
    (P + ρ • (Aᵀ * A)).PosDef ∧
      ∀ (v : EuclideanSpace ℝ (Fin p)) (x : EuclideanSpace ℝ (Fin n)),
        IsXUpdate Set.univ (quadObj P q r) ρ A v x ↔
          x = Matrix.toEuclideanLin (P + ρ • (Aᵀ * A))⁻¹
            (ρ • Matrix.toEuclideanLin Aᵀ v - q) := by
  exact quad_core P hP q r A ρ hρ hinv
