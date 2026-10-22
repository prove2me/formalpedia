-- Prove2me | solution 1 for ChanceDetEquiv.PModel.fractional_38_eq_convex_39
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T11:10:54.640456+00:00
-- url     : https://prove2.me/submissions/8a1a0e77-d675-407a-b7e5-22b17c4c9e15

import Mathlib
import Definitions.Def_ChanceDetEquiv_PModel_Model

set_option autoImplicit false

namespace ChanceDetEquiv.PModel.Aux025

open MeasureTheory

/-- Jensen for the square on a probability space. -/
lemma sq_integral_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : MemLp Z 2 P) : (∫ ω, Z ω ∂P) ^ 2 ≤ ∫ ω, Z ω ^ 2 ∂P := by
  set m := ∫ ω, Z ω ∂P with hm
  have hZi : Integrable Z P := hZ.integrable (by norm_num)
  have h0 : 0 ≤ ∫ ω, (Z ω - m) ^ 2 ∂P := integral_nonneg (fun _ => sq_nonneg _)
  have hexp : (fun ω => (Z ω - m) ^ 2) = fun ω => (Z ω ^ 2 - (2 * m) * Z ω) + m ^ 2 := by
    funext ω; ring
  have i1 : Integrable (fun ω => Z ω ^ 2 - (2 * m) * Z ω) P := hZ.integrable_sq.sub (hZi.const_mul _)
  have i2 : Integrable (fun ω => Z ω ^ 2) P := hZ.integrable_sq
  have i3 : Integrable (fun ω => (2 * m) * Z ω) P := hZi.const_mul _
  rw [hexp, integral_add i1 (integrable_const _), integral_sub i2 i3, integral_const_mul,
    integral_const] at h0
  simp only [probReal_univ, one_smul] at h0
  rw [← hm] at h0
  nlinarith

/-- Expansion of the second moment of a two-term combination. -/
lemma integral_comb_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (r s : ℝ) :
    ∫ ω, (r * X ω + s * Y ω) ^ 2 ∂P =
      r ^ 2 * ∫ ω, X ω ^ 2 ∂P + 2 * r * s * ∫ ω, X ω * Y ω ∂P + s ^ 2 * ∫ ω, Y ω ^ 2 ∂P := by
  have hXY : Integrable (fun ω => X ω * Y ω) P := by
    have := hX.integrable_mul hY (p := 2) (q := 2)
    simpa [Pi.mul_def] using this
  have hexp : (fun ω => (r * X ω + s * Y ω) ^ 2) =
      fun ω => (r ^ 2 * X ω ^ 2 + (2 * r * s) * (X ω * Y ω)) + s ^ 2 * Y ω ^ 2 := by
    funext ω; ring
  have i1 : Integrable (fun ω => r ^ 2 * X ω ^ 2) P := hX.integrable_sq.const_mul _
  have i2 : Integrable (fun ω => (2 * r * s) * (X ω * Y ω)) P := hXY.const_mul _
  have i3 : Integrable (fun ω => s ^ 2 * Y ω ^ 2) P := hY.integrable_sq.const_mul _
  have i12 : Integrable (fun ω => r ^ 2 * X ω ^ 2 + (2 * r * s) * (X ω * Y ω)) P := i1.add i2
  rw [hexp, integral_add i12 i3, integral_add i1 i2,
    integral_const_mul, integral_const_mul, integral_const_mul]

lemma integral_comb {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (r s : ℝ) :
    ∫ ω, (r * X ω + s * Y ω) ∂P = r * ∫ ω, X ω ∂P + s * ∫ ω, Y ω ∂P := by
  rw [integral_add ((hX.integrable (by norm_num)).const_mul _)
      ((hY.integrable (by norm_num)).const_mul _), integral_const_mul, integral_const_mul]

/-- Convexity of a scaled (centered or raw) second-moment cone constraint. -/
lemma quad_comb {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (κ K2 a1 a2 l1 l2 : ℝ) (_hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hK : 0 ≤ K2)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2)
    (h1 : K2 * (∫ ω, X ω ^ 2 ∂P - κ * (∫ ω, X ω ∂P) ^ 2) ≤ a1 ^ 2)
    (h2 : K2 * (∫ ω, Y ω ^ 2 ∂P - κ * (∫ ω, Y ω ∂P) ^ 2) ≤ a2 ^ 2) :
    K2 * (∫ ω, (l1 * X ω + l2 * Y ω) ^ 2 ∂P - κ * (∫ ω, (l1 * X ω + l2 * Y ω) ∂P) ^ 2)
      ≤ (l1 * a1 + l2 * a2) ^ 2 := by
  set A := ∫ ω, X ω ^ 2 ∂P
  set B := ∫ ω, X ω * Y ω ∂P
  set C := ∫ ω, Y ω ^ 2 ∂P
  set mX := ∫ ω, X ω ∂P
  set mY := ∫ ω, Y ω ∂P
  have hq : ∀ r s : ℝ, 0 ≤ (r ^ 2 * A + 2 * r * s * B + s ^ 2 * C) - κ * (r * mX + s * mY) ^ 2 := by
    intro r s
    have hZ : MemLp (fun ω => r * X ω + s * Y ω) 2 P := (hX.const_mul r).add (hY.const_mul s)
    have j := sq_integral_le P _ hZ
    rw [integral_comb_sq P X Y hX hY, integral_comb P X Y hX hY] at j
    have : κ * (r * mX + s * mY) ^ 2 ≤ (r * mX + s * mY) ^ 2 := by
      have := sq_nonneg (r * mX + s * mY); nlinarith
    linarith
  set V1 := A - κ * mX ^ 2
  set V2 := C - κ * mY ^ 2
  set Cv := B - κ * mX * mY
  have hV1 : 0 ≤ V1 := by have := hq 1 0; simp only [V1]; nlinarith
  have hV2 : 0 ≤ V2 := by have := hq 0 1; simp only [V2]; nlinarith
  have hdisc : discrim V2 (2 * Cv) V1 ≤ 0 := by
    apply discrim_le_zero
    intro x
    have := hq 1 x
    simp only [V1, V2, Cv]; nlinarith
  rw [discrim] at hdisc
  have hCv : (K2 * Cv) ^ 2 ≤ (K2 * V1) * (K2 * V2) := by
    have : Cv ^ 2 ≤ V1 * V2 := by nlinarith
    have hK2 : 0 ≤ K2 ^ 2 := sq_nonneg _
    nlinarith
  have e1 : K2 * V1 ≤ a1 ^ 2 := h1
  have e2 : K2 * V2 ≤ a2 ^ 2 := h2
  have p1 : 0 ≤ K2 * V1 := mul_nonneg hK hV1
  have p2 : 0 ≤ K2 * V2 := mul_nonneg hK hV2
  have hprod : (K2 * Cv) ^ 2 ≤ (a1 * a2) ^ 2 := by
    calc (K2 * Cv) ^ 2 ≤ (K2 * V1) * (K2 * V2) := hCv
      _ ≤ a1 ^ 2 * a2 ^ 2 := mul_le_mul e1 e2 p2 (sq_nonneg _)
      _ = (a1 * a2) ^ 2 := by ring
  have hC' : K2 * Cv ≤ a1 * a2 := by
    exact (abs_le_of_sq_le_sq' hprod (mul_nonneg ha1 ha2)).2
  rw [integral_comb_sq P X Y hX hY, integral_comb P X Y hX hY]
  have key : K2 * ((l1 ^ 2 * A + 2 * l1 * l2 * B + l2 ^ 2 * C) - κ * (l1 * mX + l2 * mY) ^ 2)
      = l1 ^ 2 * (K2 * V1) + 2 * l1 * l2 * (K2 * Cv) + l2 ^ 2 * (K2 * V2) := by
    simp only [V1, V2, Cv]; ring
  rw [key]
  have t1 : l1 ^ 2 * (K2 * V1) ≤ l1 ^ 2 * a1 ^ 2 := mul_le_mul_of_nonneg_left e1 (sq_nonneg _)
  have t2 : l2 ^ 2 * (K2 * V2) ≤ l2 ^ 2 * a2 ^ 2 := mul_le_mul_of_nonneg_left e2 (sq_nonneg _)
  have t3 : 2 * l1 * l2 * (K2 * Cv) ≤ 2 * l1 * l2 * (a1 * a2) :=
    mul_le_mul_of_nonneg_left hC' (by positivity)
  nlinarith

open ChanceDetEquiv.PModel

section model
variable {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}

/-- The residual whose raw second moment is `sigmaBarSq`. -/
def rx (d : Model Ω m n) (i : Fin m) (D : Matrix (Fin n) (Fin m) ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  (d.A.mulVec (D.mulVec (d.b ω))) i - t * d.b ω i

/-- The residual whose raw second moment is `Vbar`. -/
def ry (d : Model Ω m n) (D : Matrix (Fin n) (Fin m) ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  (∑ j : Fin n, d.c ω j * (D.mulVec (d.b ω)) j) - t * d.z0

lemma AD_expand (A : Matrix (Fin m) (Fin n) ℝ) (D : Matrix (Fin n) (Fin m) ℝ) (x : Fin m → ℝ)
    (i : Fin m) :
    (A.mulVec (D.mulVec x)) i = ∑ j : Fin n, ∑ k : Fin m, (A i j * D j k) * x k := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

lemma rx_eq (d : Model Ω m n) (i : Fin m) (D : Matrix (Fin n) (Fin m) ℝ) (t : ℝ) :
    rx d i D t = fun ω => (∑ j : Fin n, ∑ k : Fin m, (d.A i j * D j k) * d.b ω k) - t * d.b ω i := by
  funext ω; simp only [rx, AD_expand]

lemma ry_eq (d : Model Ω m n) (D : Matrix (Fin n) (Fin m) ℝ) (t : ℝ) :
    ry d D t = fun ω => (∑ j : Fin n, ∑ k : Fin m, D j k * (d.c ω j * d.b ω k)) - t * d.z0 := by
  funext ω
  simp only [ry, Matrix.mulVec, dotProduct, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

lemma rx_memLp (d : Model Ω m n) (hM : MomentAssumptions d) (i : Fin m)
    (D : Matrix (Fin n) (Fin m) ℝ) (t : ℝ) : MemLp (rx d i D t) 2 d.P := by
  rw [rx_eq]
  exact (memLp_finsetSum _ fun j _ => memLp_finsetSum _ fun k _ => (hM.1 k).const_mul _).sub
    ((hM.1 i).const_mul t)

lemma ry_memLp (d : Model Ω m n) [IsProbabilityMeasure d.P] (hM : MomentAssumptions d)
    (D : Matrix (Fin n) (Fin m) ℝ) (t : ℝ) : MemLp (ry d D t) 2 d.P := by
  rw [ry_eq]
  exact (memLp_finsetSum _ fun j _ => memLp_finsetSum _ fun k _ =>
    (hM.2.2.1 j k).const_mul _).sub (memLp_const _)

lemma rx_integral (d : Model Ω m n) [IsProbabilityMeasure d.P] (hM : MomentAssumptions d)
    (i : Fin m) (D : Matrix (Fin n) (Fin m) ℝ) (t : ℝ) :
    ∫ ω, rx d i D t ω ∂d.P = - muBar d i D t := by
  have hb : ∀ k, Integrable (fun ω => d.b ω k) d.P := fun k => (hM.1 k).integrable (by norm_num)
  rw [rx_eq, integral_sub (integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      (hb k).const_mul _) ((hb i).const_mul _),
    integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => (hb k).const_mul _,
    integral_const_mul]
  have : ∀ j : Fin n, ∫ ω, ∑ k : Fin m, (d.A i j * D j k) * d.b ω k ∂d.P
      = ∑ k : Fin m, (d.A i j * D j k) * meanB d k := by
    intro j
    rw [integral_finsetSum _ fun k _ => (hb k).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]; rfl
  simp only [this, muBar, AD_expand]
  simp only [meanB]
  ring

lemma sum_mul_scal (f g : Fin n → ℝ) (a : ℝ) :
    ∑ j : Fin n, f j * (a * g j) = a * ∑ j : Fin n, f j * g j := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring

lemma rx_comb (d : Model Ω m n) (i : Fin m) (D1 D2 : Matrix (Fin n) (Fin m) ℝ)
    (t1 t2 a b : ℝ) :
    rx d i (a • D1 + b • D2) (a * t1 + b * t2) = fun ω => a * rx d i D1 t1 ω + b * rx d i D2 t2 ω := by
  funext ω
  simp only [rx, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma ry_comb (d : Model Ω m n) (D1 D2 : Matrix (Fin n) (Fin m) ℝ) (t1 t2 a b : ℝ) :
    ry d (a • D1 + b • D2) (a * t1 + b * t2) = fun ω => a * ry d D1 t1 ω + b * ry d D2 t2 ω := by
  funext ω
  simp only [ry, Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mul_add, Finset.sum_add_distrib, sum_mul_scal]
  ring

lemma meanObjective_comb (d : Model Ω m n) (D1 D2 : Matrix (Fin n) (Fin m) ℝ) (a b : ℝ) :
    meanObjective d (a • D1 + b • D2) = a * meanObjective d D1 + b * meanObjective d D2 := by
  simp only [meanObjective, Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => by ring

lemma meanObjective_smul (d : Model Ω m n) (D : Matrix (Fin n) (Fin m) ℝ) (s : ℝ) :
    meanObjective d (s • D) = s * meanObjective d D := by
  have := meanObjective_comb d D 0 s 0
  simpa using this

lemma rx_smul (d : Model Ω m n) (i : Fin m) (D : Matrix (Fin n) (Fin m) ℝ) (s : ℝ) (ω : Ω) :
    rx d i (s • D) s ω = s * rowResidual d i D ω := by
  simp only [rx, rowResidual, Matrix.smul_mulVec, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  ring

lemma ry_smul (d : Model Ω m n) (D : Matrix (Fin n) (Fin m) ℝ) (s : ℝ) (ω : Ω) :
    ry d (s • D) s ω = s * ((∑ j : Fin n, d.c ω j * (D.mulVec (d.b ω)) j) - d.z0) := by
  simp only [ry, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, sum_mul_scal]
  ring

lemma muBar_smul (d : Model Ω m n) (i : Fin m) (D : Matrix (Fin n) (Fin m) ℝ) (s : ℝ) :
    muBar d i (s • D) s = s * muRow d i D := by
  simp only [muBar, muRow, Matrix.smul_mulVec, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  ring

lemma sigmaBarSq_smul (d : Model Ω m n) (i : Fin m) (D : Matrix (Fin n) (Fin m) ℝ) (s : ℝ) :
    sigmaBarSq d i (s • D) s = s ^ 2 * sigmaSq d i D := by
  have : sigmaBarSq d i (s • D) s = ∫ ω, rx d i (s • D) s ω ^ 2 ∂d.P := rfl
  rw [this]
  simp only [rx_smul, mul_pow]
  rw [integral_const_mul]; rfl

lemma Vbar_smul (d : Model Ω m n) (D : Matrix (Fin n) (Fin m) ℝ) (s : ℝ) :
    Vbar d (s • D) s = s ^ 2 * V d D := by
  have : Vbar d (s • D) s = ∫ ω, ry d (s • D) s ω ^ 2 ∂d.P := rfl
  rw [this]
  simp only [ry_smul, mul_pow]
  rw [integral_const_mul]; rfl

end model

end ChanceDetEquiv.PModel.Aux025

namespace ChanceDetEquiv.PModel.Aux025

open ChanceDetEquiv.PModel MeasureTheory

lemma lim_aux (a b s : ℝ) (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → (1 - ε) * a + ε * b ≤ s) : a ≤ s := by
  by_contra hlt
  push Not at hlt
  have hc : 0 < |a - b| + 1 := by positivity
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min 1 ((a - s) / (2 * (|a - b| + 1))) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by
    rw [hε]; exact lt_min one_pos (div_pos (by linarith) (by positivity))
  have hε1 : ε ≤ 1 := by rw [hε]; exact min_le_left _ _
  have hε2 : ε ≤ (a - s) / (2 * (|a - b| + 1)) := by rw [hε]; exact min_le_right _ _
  have h3 : ε * (2 * (|a - b| + 1)) ≤ a - s := (le_div_iff₀ (by positivity)).1 hε2
  have h4 : ε * (a - b) ≤ ε * |a - b| := mul_le_mul_of_nonneg_left (le_abs_self _) hε0.le
  have h1 := h ε hε0 hε1
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}

lemma convex39 (d : Model Ω m n) [IsProbabilityMeasure d.P] (hM : MomentAssumptions d) :
    Convex ℝ (feasible39 d) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨Dx, vx, v0x, wx, tx⟩ := x
  obtain ⟨Dy, vy, v0y, wy, ty⟩ := y
  simp only [feasible39, Set.mem_setOf_eq] at hx hy
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := hy
  subst hx4
  subst hy4
  simp only [Prod.smul_mk, Prod.mk_add_mk, feasible39, Set.mem_setOf_eq, smul_eq_mul,
    Pi.add_apply, Pi.smul_apply]
  refine ⟨?_, ?_, fun i => ?_, ?_, ?_⟩
  · rw [meanObjective_comb]
    have e1 := mul_le_mul_of_nonneg_left hx1 ha
    have e2 := mul_le_mul_of_nonneg_left hy1 hb
    nlinarith
  · have hV : Vbar d (a • Dx + b • Dy) (a * tx + b * ty) =
        ∫ ω, (a * ry d Dx tx ω + b * ry d Dy ty ω) ^ 2 ∂d.P := by
      show ∫ ω, ry d (a • Dx + b • Dy) (a * tx + b * ty) ω ^ 2 ∂d.P = _
      simp only [ry_comb]
    have hVx : Vbar d Dx tx = ∫ ω, ry d Dx tx ω ^ 2 ∂d.P := rfl
    have hVy : Vbar d Dy ty = ∫ ω, ry d Dy ty ω ^ 2 ∂d.P := rfl
    have q := quad_comb d.P _ _ (ry_memLp d hM Dx tx) (ry_memLp d hM Dy ty) 0 1 1 1 a b le_rfl
      zero_le_one zero_le_one zero_le_one zero_le_one ha hb
      (by rw [← hVx]; nlinarith) (by rw [← hVy]; nlinarith)
    rw [hV]
    nlinarith [q]
  · obtain ⟨hxa, hxb, hxc⟩ := hx3 i
    obtain ⟨hya, hyb, hyc⟩ := hy3 i
    have hmu : muBar d i (a • Dx + b • Dy) (a * tx + b * ty) =
        a * muBar d i Dx tx + b * muBar d i Dy ty := by
      have e := rx_integral d hM i (a • Dx + b • Dy) (a * tx + b * ty)
      rw [rx_comb, integral_comb d.P _ _ (rx_memLp d hM i Dx tx) (rx_memLp d hM i Dy ty),
        rx_integral d hM, rx_integral d hM] at e
      linarith
    refine ⟨?_, ?_, add_nonneg (mul_nonneg ha hxc) (mul_nonneg hb hyc)⟩
    · rw [hmu]; nlinarith [mul_le_mul_of_nonneg_left hxa ha, mul_le_mul_of_nonneg_left hya hb]
    · have hs : sigmaBarSq d i (a • Dx + b • Dy) (a * tx + b * ty) =
          ∫ ω, (a * rx d i Dx tx ω + b * rx d i Dy ty ω) ^ 2 ∂d.P := by
        show ∫ ω, rx d i (a • Dx + b • Dy) (a * tx + b * ty) ω ^ 2 ∂d.P = _
        simp only [rx_comb]
      have hm2 : muBar d i (a • Dx + b • Dy) (a * tx + b * ty) ^ 2 =
          (∫ ω, (a * rx d i Dx tx ω + b * rx d i Dy ty ω) ∂d.P) ^ 2 := by
        rw [← neg_sq, ← rx_integral d hM, rx_comb d i Dx Dy tx ty a b]
      have hsx : sigmaBarSq d i Dx tx = ∫ ω, rx d i Dx tx ω ^ 2 ∂d.P := rfl
      have hsy : sigmaBarSq d i Dy ty = ∫ ω, rx d i Dy ty ω ^ 2 ∂d.P := rfl
      have h1 : K d i ^ 2 * (∫ ω, rx d i Dx tx ω ^ 2 ∂d.P - 1 * (∫ ω, rx d i Dx tx ω ∂d.P) ^ 2)
          ≤ vx i ^ 2 := by
        rw [rx_integral d hM, neg_sq, ← hsx]; nlinarith
      have h2 : K d i ^ 2 * (∫ ω, rx d i Dy ty ω ^ 2 ∂d.P - 1 * (∫ ω, rx d i Dy ty ω ∂d.P) ^ 2)
          ≤ vy i ^ 2 := by
        rw [rx_integral d hM, neg_sq, ← hsy]; nlinarith
      have q := quad_comb d.P _ _ (rx_memLp d hM i Dx tx) (rx_memLp d hM i Dy ty) 1 (K d i ^ 2)
        (vx i) (vy i) a b zero_le_one le_rfl (sq_nonneg _) hxc hyc ha hb h1 h2
      rw [hs, hm2]
      nlinarith [q]
  · linarith
  · exact add_nonneg (mul_nonneg ha hx5) (mul_nonneg hb hy5)

lemma fwd (d : Model Ω m n) (p : Point38 m n) (hp : p ∈ feasible38 d) :
    forward p ∈ feasible39 d ∧ value39 (forward p) = value38 p := by
  obtain ⟨D, v, v0, w0⟩ := p
  simp only [feasible38, Set.mem_setOf_eq] at hp
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hs0 : 0 < 1 / w0 := one_div_pos.mpr h4
  have hsw : 1 / w0 * w0 = 1 := by field_simp
  refine ⟨?_, ?_⟩
  · simp only [forward, feasible39, Set.mem_setOf_eq]
    refine ⟨?_, ?_, fun i => ?_, hsw, hs0.le⟩
    · rw [meanObjective_smul]
      have := mul_le_mul_of_nonneg_left h1 hs0.le
      linarith
    · rw [Vbar_smul]
      have := mul_nonneg (sq_nonneg (1 / w0)) h2
      nlinarith
    · obtain ⟨a1, a2, a3⟩ := h3 i
      simp only [Pi.smul_apply, smul_eq_mul]
      refine ⟨?_, ?_, mul_nonneg hs0.le a3⟩
      · rw [muBar_smul]
        have := mul_le_mul_of_nonneg_left a1 hs0.le
        linarith
      · rw [sigmaBarSq_smul, muBar_smul]
        have := mul_nonneg (sq_nonneg (1 / w0)) a2
        nlinarith
  · simp only [forward, value39, value38]
    ring

lemma bwd (d : Model Ω m n) (q : Point39 m n) (hq : q ∈ feasible39 d) (ht : 0 < q.2.2.2.2) :
    backward q ∈ feasible38 d ∧ value38 (backward q) = value39 q := by
  obtain ⟨Db, vb, v0b, w0b, t⟩ := q
  simp only at ht
  simp only [feasible39, Set.mem_setOf_eq] at hq
  obtain ⟨h1, h2, h3, h4, h5⟩ := hq
  subst h4
  have htne : t ≠ 0 := ht.ne'
  have hu : t * t⁻¹ = 1 := mul_inv_cancel₀ htne
  have hD : Db = t • (t⁻¹ • Db) := by rw [smul_smul, hu, one_smul]
  have hu0 : 0 < t⁻¹ := inv_pos.mpr ht
  refine ⟨?_, ?_⟩
  · simp only [backward, feasible38, Set.mem_setOf_eq]
    rw [hD] at h1 h2 h3
    rw [meanObjective_smul] at h1
    rw [Vbar_smul] at h2
    refine ⟨?_, ?_, fun i => ?_, hu0⟩
    · have := mul_le_mul_of_nonneg_left h1 hu0.le
      have e : t⁻¹ * (t * meanObjective d (t⁻¹ • Db) - v0b) =
          meanObjective d (t⁻¹ • Db) - t⁻¹ * v0b := by field_simp
      have e2 : t⁻¹ * (t * d.z0) = d.z0 := by field_simp
      rw [e, e2] at this
      exact this
    · have hle : t ^ 2 * V d (t⁻¹ • Db) ≤ 1 := by nlinarith
      have hV : V d (t⁻¹ • Db) ≤ (t⁻¹) ^ 2 := by
        calc V d (t⁻¹ • Db) = (t⁻¹) ^ 2 * (t ^ 2 * V d (t⁻¹ • Db)) := by field_simp
          _ ≤ (t⁻¹) ^ 2 * 1 := mul_le_mul_of_nonneg_left hle (sq_nonneg _)
          _ = (t⁻¹) ^ 2 := mul_one _
      linarith
    · obtain ⟨a1, a2, a3⟩ := h3 i
      rw [muBar_smul] at a1 a2
      rw [sigmaBarSq_smul] at a2
      simp only [Pi.smul_apply, smul_eq_mul]
      refine ⟨?_, ?_, mul_nonneg hu0.le a3⟩
      · have := mul_nonneg hu0.le a1
        have e : t⁻¹ * (t * muRow d i (t⁻¹ • Db) - vb i) = muRow d i (t⁻¹ • Db) - t⁻¹ * vb i := by
          field_simp
        rw [e] at this
        linarith
      · have := mul_nonneg (sq_nonneg t⁻¹) a2
        have e : (t⁻¹) ^ 2 * (-(K d i ^ 2) * (t ^ 2 * sigmaSq d i (t⁻¹ • Db)) +
            K d i ^ 2 * (t * muRow d i (t⁻¹ • Db)) ^ 2 + vb i ^ 2) =
            -(K d i ^ 2) * sigmaSq d i (t⁻¹ • Db) + K d i ^ 2 * muRow d i (t⁻¹ • Db) ^ 2 +
              (t⁻¹ * vb i) ^ 2 := by
          field_simp
        rw [e] at this
        linarith
  · simp only [backward, value38, value39]
    field_simp

end ChanceDetEquiv.PModel.Aux025

open ChanceDetEquiv.PModel MeasureTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (d : Model Ω m n) [IsProbabilityMeasure d.P]
    (hm : 0 < m) (hn : 0 < n)
    (hMoments : MomentAssumptions d) (hNormal : NormalRows d)
    (hConfidence : Confidence d)
    (hNonempty : (feasible38 d).Nonempty) :
    Convex ℝ (feasible39 d) ∧
      (∀ p : Point38 m n, p ∈ feasible38 d →
        forward p ∈ feasible39 d ∧ value39 (forward p) = value38 p) ∧
      sSup (values38 d) = sSup (values39 d) := by
  have hconv := ChanceDetEquiv.PModel.Aux025.convex39 d hMoments
  refine ⟨hconv, fun p hp => ChanceDetEquiv.PModel.Aux025.fwd d p hp, ?_⟩
  apply le_antisymm
  · apply sSup_le_sSup
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨forward p, (ChanceDetEquiv.PModel.Aux025.fwd d p hp).1,
      by simp only [(ChanceDetEquiv.PModel.Aux025.fwd d p hp).2]⟩
  · apply sSup_le
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨p0, hp0⟩ := hNonempty
    have hb0 : ((value38 p0 : ℝ) : EReal) ≤ sSup (values38 d) := le_sSup ⟨p0, hp0, rfl⟩
    have key : ∀ q' ∈ feasible39 d, 0 < q'.2.2.2.2 →
        ((value39 q' : ℝ) : EReal) ≤ sSup (values38 d) := by
      intro q' hq' ht'
      obtain ⟨hm', hv⟩ := ChanceDetEquiv.PModel.Aux025.bwd d q' hq' ht'
      exact le_sSup ⟨backward q', hm', by simp only [hv]⟩
    have ht0 : 0 ≤ q.2.2.2.2 := hq.2.2.2.2
    rcases ht0.lt_or_eq with htpos | htz
    · exact key q hq htpos
    · obtain ⟨hf0, -⟩ := ChanceDetEquiv.PModel.Aux025.fwd d p0 hp0
      have hw0 : 0 < p0.2.2.2 := hp0.2.2.2
      have hft : 0 < (forward p0).2.2.2.2 := by
        simp only [forward]; exact one_div_pos.mpr hw0
      by_cases hS : sSup (values38 d) = ⊤
      · rw [hS]; exact le_top
      have hSb : sSup (values38 d) ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hb0
      rw [← EReal.coe_toReal hS hSb, EReal.coe_le_coe_iff]
      apply ChanceDetEquiv.PModel.Aux025.lim_aux _ (value39 (forward p0))
      intro ε hε0 hε1
      have hmem := hconv hq hf0 (by linarith : (0:ℝ) ≤ 1 - ε) hε0.le (by ring)
      have htε : 0 < ((1 - ε) • q + ε • forward p0).2.2.2.2 := by
        simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        rw [← htz]
        have := mul_pos hε0 hft
        linarith
      have h := key _ hmem htε
      rw [← EReal.coe_toReal hS hSb, EReal.coe_le_coe_iff] at h
      have hv : value39 ((1 - ε) • q + ε • forward p0) =
          (1 - ε) * value39 q + ε * value39 (forward p0) := by
        simp only [value39, Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [hv] at h
      exact h
