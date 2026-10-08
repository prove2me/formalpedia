-- Prove2me | solution 1 for BoydADMM.Prox.quadratic_affine_kkt
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:32:08.232217+00:00
-- url     : https://prove2.me/submissions/3bd0d79a-2c64-46e7-9a9d-8ed13fca56ac

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix


namespace BoydADMM.Prox

theorem kipE {k : ℕ} (a b : EuclideanSpace ℝ (Fin k)) : inner ℝ a b = a.ofLp ⬝ᵥ b.ofLp := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

theorem k_psd {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (h : EuclideanSpace ℝ (Fin n)) : 0 ≤ inner ℝ h (Matrix.toEuclideanLin P h) := by
  rw [kipE]
  have := hP.dotProduct_mulVec_nonneg h.ofLp
  simpa using this

theorem k_sym {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (a b : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (Matrix.toEuclideanLin P a) b = inner ℝ a (Matrix.toEuclideanLin P b) := by
  rw [kipE, kipE]
  have hT : Pᵀ = P := by
    have := hP.1.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  show (P *ᵥ a.ofLp) ⬝ᵥ b.ofLp = a.ofLp ⬝ᵥ (P *ᵥ b.ofLp)
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]

/-- gradient -/
noncomputable def kG {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (q : EuclideanSpace ℝ (Fin n))
    (ρ : ℝ) (v x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanLin P x + ρ • x - ρ • v + q

theorem k_expand {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (q : EuclideanSpace ℝ (Fin n)) (r ρ : ℝ) (v x h : EuclideanSpace ℝ (Fin n)) :
    quadObj P q r (x + h) + (ρ / 2) * ‖x + h - v‖ ^ 2 =
      quadObj P q r x + (ρ / 2) * ‖x - v‖ ^ 2 + inner ℝ (kG P q ρ v x) h
        + (1 / 2) * (inner ℝ h (Matrix.toEuclideanLin P h) + ρ * inner ℝ h h) := by
  unfold quadObj kG
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  have hs := k_sym P hP x h
  have e : x + h - v = (x - v) + h := by abel
  rw [e, map_add]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm x h, real_inner_comm v x, real_inner_comm v h,
    real_inner_comm (Matrix.toEuclideanLin P x) h, hs]
  ring

theorem k_char {n m : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (q : EuclideanSpace ℝ (Fin n)) (r : ℝ) (F : Matrix (Fin m) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin m)) (ρ : ℝ) (hρ : 0 < ρ) (v x : EuclideanSpace ℝ (Fin n)) :
    IsProx (affineSet F g) (quadObj P q r) ρ v x ↔
      x ∈ affineSet F g ∧ ∀ h, Matrix.toEuclideanLin F h = 0 → inner ℝ (kG P q ρ v x) h = 0 := by
  have Qnn : ∀ h : EuclideanSpace ℝ (Fin n),
      0 ≤ inner ℝ h (Matrix.toEuclideanLin P h) + ρ * inner ℝ h h := fun h => by
    have := k_psd P hP h
    have := real_inner_self_nonneg (x := h)
    positivity
  constructor
  · rintro ⟨hx, hmin⟩
    refine ⟨hx, fun h hh => ?_⟩
    set a := inner ℝ (kG P q ρ v x) h
    set Q := inner ℝ h (Matrix.toEuclideanLin P h) + ρ * inner ℝ h h
    have hQ : 0 ≤ Q := Qnn h
    have key : ∀ t : ℝ, 0 ≤ t * a + (1 / 2) * (t ^ 2 * Q) := by
      intro t
      have hmem : x + t • h ∈ affineSet F g := by
        show Matrix.toEuclideanLin F (x + t • h) = g
        rw [map_add, map_smul, hh, smul_zero, add_zero]; exact hx
      have := hmin _ hmem
      rw [k_expand P hP q r ρ v x (t • h)] at this
      simp only [real_inner_smul_right, real_inner_smul_left, map_smul] at this
      have e : t ^ 2 * Q = t * (t * inner ℝ h (Matrix.toEuclideanLin P h)) + ρ * (t * (t * inner ℝ h h)) := by
        simp only [Q]; ring
      rw [e]; linarith
    by_contra ha
    have hD : 0 < Q + 1 := by linarith
    have := key (-a / (Q + 1))
    have e : -a / (Q + 1) * a + 1 / 2 * ((-a / (Q + 1)) ^ 2 * Q) = -(a ^ 2 * (Q + 2)) / (2 * (Q + 1) ^ 2) := by
      field_simp; ring
    rw [e] at this
    have : 0 < a ^ 2 * (Q + 2) := by positivity
    have : -(a ^ 2 * (Q + 2)) / (2 * (Q + 1) ^ 2) < 0 := by
      apply div_neg_of_neg_of_pos (by linarith) (by positivity)
    linarith
  · rintro ⟨hx, horth⟩
    refine ⟨hx, fun y hy => ?_⟩
    obtain ⟨h, rfl⟩ : ∃ h, y = x + h := ⟨y - x, by abel⟩
    have hh : Matrix.toEuclideanLin F h = 0 := by
      have e1 : Matrix.toEuclideanLin F (x + h) = g := hy
      have e2 : Matrix.toEuclideanLin F x = g := hx
      rw [map_add, e2] at e1
      simpa using e1
    rw [k_expand P hP q r ρ v x h, horth h hh]
    have := Qnn h
    linarith

theorem k_range {n m : ℕ} (F : Matrix (Fin m) (Fin n) ℝ) (a : EuclideanSpace ℝ (Fin n)) :
    (∀ h, Matrix.toEuclideanLin F h = 0 → inner ℝ a h = 0) ↔
      ∃ ν, Matrix.toEuclideanLin Fᵀ ν = a := by
  have hadj : Matrix.toEuclideanLin Fᵀ = LinearMap.adjoint (Matrix.toEuclideanLin F) := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, conjTranspose_eq_transpose_of_trivial]
  constructor
  · intro H
    have : a ∈ (LinearMap.ker (Matrix.toEuclideanLin F))ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      rw [real_inner_comm]
      exact H u (LinearMap.mem_ker.mp hu)
    rw [LinearMap.orthogonal_ker] at this
    obtain ⟨ν, hν⟩ := this
    exact ⟨ν, by rw [hadj]; exact hν⟩
  · rintro ⟨ν, rfl⟩ h hh
    rw [hadj, LinearMap.adjoint_inner_left, hh, inner_zero_right]

theorem k_uniq {n m : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (q : EuclideanSpace ℝ (Fin n)) (F : Matrix (Fin m) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin m)) (ρ : ℝ) (hρ : 0 < ρ) (v x1 x2 : EuclideanSpace ℝ (Fin n))
    (h1 : x1 ∈ affineSet F g ∧ ∀ h, Matrix.toEuclideanLin F h = 0 → inner ℝ (kG P q ρ v x1) h = 0)
    (h2 : x2 ∈ affineSet F g ∧ ∀ h, Matrix.toEuclideanLin F h = 0 → inner ℝ (kG P q ρ v x2) h = 0) :
    x1 = x2 := by
  have hk : Matrix.toEuclideanLin F (x1 - x2) = 0 := by
    have e1 : Matrix.toEuclideanLin F x1 = g := h1.1
    have e2 : Matrix.toEuclideanLin F x2 = g := h2.1
    rw [map_sub, e1, e2, sub_self]
  have a1 := h1.2 _ hk
  have a2 := h2.2 _ hk
  have e : kG P q ρ v x1 - kG P q ρ v x2 =
      Matrix.toEuclideanLin P (x1 - x2) + ρ • (x1 - x2) := by
    simp only [kG, map_sub, smul_sub]; abel
  have : inner ℝ (Matrix.toEuclideanLin P (x1 - x2) + ρ • (x1 - x2)) (x1 - x2) = 0 := by
    rw [← e, inner_sub_left, a1, a2, sub_self]
  rw [inner_add_left, real_inner_smul_left, real_inner_comm] at this
  have hp := k_psd P hP (x1 - x2)
  have hs : inner ℝ (x1 - x2) (x1 - x2) = 0 := by
    have := real_inner_self_nonneg (x := x1 - x2)
    nlinarith
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hs)

theorem k_exists {n m : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (q : EuclideanSpace ℝ (Fin n)) (r : ℝ) (F : Matrix (Fin m) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin m)) (ρ : ℝ) (hρ : 0 < ρ) (hne : (affineSet F g).Nonempty)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∃ x, IsProx (affineSet F g) (quadObj P q r) ρ v x := by
  obtain ⟨x0, hx0⟩ := hne
  set J : EuclideanSpace ℝ (Fin n) → ℝ := fun y => quadObj P q r y + (ρ / 2) * ‖y - v‖ ^ 2 with hJ
  have hPc : Continuous (Matrix.toEuclideanLin P) := LinearMap.continuous_of_finiteDimensional _
  have hFc : Continuous (Matrix.toEuclideanLin F) := LinearMap.continuous_of_finiteDimensional _
  have hJc : Continuous J := by
    simp only [hJ, quadObj]
    fun_prop
  have hS : IsClosed (affineSet F g) := isClosed_eq hFc continuous_const
  set a := ‖kG P q ρ v 0‖
  set j0 := J 0
  set j1 := J x0
  have bound : ∀ y, j0 - a * ‖y‖ + (ρ / 2) * ‖y‖ ^ 2 ≤ J y := by
    intro y
    have := k_expand P hP q r ρ v 0 y
    rw [zero_add] at this
    simp only [hJ, j0]
    rw [this]
    have h1 := real_inner_le_norm (kG P q ρ v 0) y
    have h2 := abs_real_inner_le_norm (kG P q ρ v 0) y
    have h3 := k_psd P hP y
    rw [real_inner_self_eq_norm_sq]
    nlinarith [abs_le.mp h2]
  set R := (2 * a + 2 * |j1 - j0| + 2) / ρ + 1 + ‖x0‖ with hR
  have ha : 0 ≤ a := norm_nonneg _
  have far : ∀ y, R < ‖y‖ → j1 < J y := by
    intro y hy
    have hb := bound y
    set t := ‖y‖
    have ht1 : (2 * a + 2 * |j1 - j0| + 2) / ρ + 1 < t := by
      have := norm_nonneg x0; linarith
    have hq : 2 * a + 2 * |j1 - j0| + 2 < ρ * t := by
      have h' : (2 * a + 2 * |j1 - j0| + 2) / ρ < t := by linarith
      rw [div_lt_iff₀ hρ] at h'; linarith
    have habs := le_abs_self (j1 - j0)
    have habs0 := abs_nonneg (j1 - j0)
    have t1 : 1 < t := by
      have : 0 ≤ (2 * a + 2 * |j1 - j0| + 2) / ρ := by positivity
      linarith
    nlinarith
  set K := affineSet F g ∩ Metric.closedBall 0 R
  have hK : IsCompact K := (isCompact_closedBall 0 R).inter_left hS
  have hx0K : x0 ∈ K := ⟨hx0, by
    rw [Metric.mem_closedBall, dist_zero_right]
    have : 0 ≤ (2 * a + 2 * |j1 - j0| + 2) / ρ := by positivity
    linarith⟩
  obtain ⟨xm, hxm, hmin⟩ := hK.exists_isMinOn ⟨x0, hx0K⟩ hJc.continuousOn
  refine ⟨xm, hxm.1, fun y hy => ?_⟩
  show J xm ≤ J y
  by_cases hy' : ‖y‖ ≤ R
  · exact hmin ⟨hy, by rw [Metric.mem_closedBall, dist_zero_right]; exact hy'⟩
  · push_neg at hy'
    have := far y hy'
    have := hmin hx0K
    simp only [Set.mem_setOf_eq] at this
    linarith

theorem kkt_core {n m : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (q : EuclideanSpace ℝ (Fin n)) (r : ℝ) (F : Matrix (Fin m) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin m)) (ρ : ℝ) (hρ : 0 < ρ) :
    (∀ (z u x : EuclideanSpace ℝ (Fin n)),
        IsProx (affineSet F g) (quadObj P q r) ρ (z - u) x ↔
          ∃ ν : EuclideanSpace ℝ (Fin m),
            Matrix.toEuclideanLin (P + ρ • (1 : Matrix (Fin n) (Fin n) ℝ)) x
                + Matrix.toEuclideanLin Fᵀ ν + (q - ρ • (z - u)) = 0 ∧
              Matrix.toEuclideanLin F x - g = 0) ∧
      ((affineSet F g).Nonempty →
        ∃ (M : Matrix (Fin n) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin n)),
          ∀ (v x : EuclideanSpace ℝ (Fin n)),
            IsProx (affineSet F g) (quadObj P q r) ρ v x ↔
              x = Matrix.toEuclideanLin M v + b) := by
  have hM1 : ∀ x : EuclideanSpace ℝ (Fin n),
      Matrix.toEuclideanLin (P + ρ • (1 : Matrix (Fin n) (Fin n) ℝ)) x =
        Matrix.toEuclideanLin P x + ρ • x := by
    intro x
    rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    congr 2
    ext i
    show ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x.ofLp) i = x i
    rw [one_mulVec]
  refine ⟨?_, ?_⟩
  · intro z u x
    rw [k_char P hP q r F g ρ hρ]
    have hS : x ∈ affineSet F g ↔ Matrix.toEuclideanLin F x - g = 0 := by
      rw [sub_eq_zero]; rfl
    have heq : ∀ ν, Matrix.toEuclideanLin (P + ρ • (1 : Matrix (Fin n) (Fin n) ℝ)) x
        + Matrix.toEuclideanLin Fᵀ ν + (q - ρ • (z - u)) =
          Matrix.toEuclideanLin Fᵀ ν + kG P q ρ (z - u) x := by
      intro ν; rw [hM1]; simp only [kG]; abel
    constructor
    · rintro ⟨hx, horth⟩
      have : ∀ h, Matrix.toEuclideanLin F h = 0 → inner ℝ (-kG P q ρ (z - u) x) h = 0 := by
        intro h hh; rw [inner_neg_left, horth h hh, neg_zero]
      obtain ⟨ν, hν⟩ := (k_range F _).mp this
      refine ⟨ν, ?_, hS.mp hx⟩
      rw [heq, hν, neg_add_cancel]
    · rintro ⟨ν, h1, h2⟩
      refine ⟨hS.mpr h2, ?_⟩
      rw [heq, add_eq_zero_iff_eq_neg] at h1
      have := (k_range F _).mpr ⟨ν, h1⟩
      intro h hh
      have := this h hh
      rw [inner_neg_left, neg_eq_zero] at this
      exact this
  · intro hne
    have hX : ∀ v, ∃ x, IsProx (affineSet F g) (quadObj P q r) ρ v x :=
      k_exists P hP q r F g ρ hρ hne
    choose X hXp using hX
    have hC : ∀ v, X v ∈ affineSet F g ∧ ∀ h, Matrix.toEuclideanLin F h = 0 →
        inner ℝ (kG P q ρ v (X v)) h = 0 := fun v => (k_char P hP q r F g ρ hρ v (X v)).mp (hXp v)
    have hFX : ∀ v, Matrix.toEuclideanLin F (X v) = g := fun v => (hC v).1
    have uniqX : ∀ v x, (x ∈ affineSet F g ∧ ∀ h, Matrix.toEuclideanLin F h = 0 →
        inner ℝ (kG P q ρ v x) h = 0) → x = X v := fun v x hx =>
      k_uniq P hP q F g ρ hρ v x (X v) hx (hC v)
    have hadd : ∀ v1 v2, X (v1 + v2) - X 0 = (X v1 - X 0) + (X v2 - X 0) := by
      intro v1 v2
      have : X v1 + X v2 - X 0 = X (v1 + v2) := by
        apply uniqX
        refine ⟨?_, fun h hh => ?_⟩
        · show Matrix.toEuclideanLin F (X v1 + X v2 - X 0) = g
          rw [map_sub, map_add, hFX, hFX, hFX]; abel
        · have e : kG P q ρ (v1 + v2) (X v1 + X v2 - X 0) =
              kG P q ρ v1 (X v1) + kG P q ρ v2 (X v2) - kG P q ρ 0 (X 0) := by
            simp only [kG, map_add, map_sub, smul_add, smul_sub, smul_zero]; abel
          rw [e, inner_sub_left, inner_add_left, (hC v1).2 h hh, (hC v2).2 h hh,
            (hC 0).2 h hh]
          simp
      rw [← this]; abel
    have hsmul : ∀ (c : ℝ) v, X (c • v) - X 0 = c • (X v - X 0) := by
      intro c v
      have : X 0 + c • (X v - X 0) = X (c • v) := by
        apply uniqX
        refine ⟨?_, fun h hh => ?_⟩
        · show Matrix.toEuclideanLin F (X 0 + c • (X v - X 0)) = g
          rw [map_add, map_smul, map_sub, hFX, hFX, sub_self, smul_zero, add_zero]
        · have e : kG P q ρ (c • v) (X 0 + c • (X v - X 0)) =
              (1 - c) • kG P q ρ 0 (X 0) + c • kG P q ρ v (X v) := by
            simp only [kG, map_add, map_sub, map_smul, smul_zero]
            module
          rw [e, inner_add_left, real_inner_smul_left, real_inner_smul_left,
            (hC v).2 h hh, (hC 0).2 h hh]
          simp
      rw [← this]; abel
    let L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
      { toFun := fun v => X v - X 0
        map_add' := hadd
        map_smul' := fun c v => by simpa using hsmul c v }
    refine ⟨Matrix.toEuclideanLin.symm L, X 0, fun v x => ?_⟩
    rw [LinearEquiv.apply_symm_apply]
    show _ ↔ x = (X v - X 0) + X 0
    rw [sub_add_cancel]
    constructor
    · intro hx
      exact uniqX v x ((k_char P hP q r F g ρ hρ v x).mp hx)
    · rintro rfl; exact hXp v

end BoydADMM.Prox

open BoydADMM.Prox


theorem solution {n m : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (q : EuclideanSpace ℝ (Fin n)) (r : ℝ) (F : Matrix (Fin m) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin m)) (ρ : ℝ) (hρ : 0 < ρ) :
    (∀ (z u x : EuclideanSpace ℝ (Fin n)),
        IsProx (affineSet F g) (quadObj P q r) ρ (z - u) x ↔
          ∃ ν : EuclideanSpace ℝ (Fin m),
            Matrix.toEuclideanLin (P + ρ • (1 : Matrix (Fin n) (Fin n) ℝ)) x
                + Matrix.toEuclideanLin Fᵀ ν + (q - ρ • (z - u)) = 0 ∧
              Matrix.toEuclideanLin F x - g = 0) ∧
      ((affineSet F g).Nonempty →
        ∃ (M : Matrix (Fin n) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin n)),
          ∀ (v x : EuclideanSpace ℝ (Fin n)),
            IsProx (affineSet F g) (quadObj P q r) ρ v x ↔
              x = Matrix.toEuclideanLin M v + b) := by
  exact kkt_core P hP q r F g ρ hρ
