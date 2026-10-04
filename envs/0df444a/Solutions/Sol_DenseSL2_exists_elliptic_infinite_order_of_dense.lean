-- Prove2me | solution 1 for DenseSL2.exists_elliptic_infinite_order_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T06:51:55.079493+00:00
-- url     : https://prove2.me/submissions/80670251-1e68-4670-9a01-e3354502fba1

import Theorems.Thm_CyclotomicTrace_finite_add_inv_rootOfUnity
import Mathlib


section
section
open MeasureTheory Matrix Filter Topology

namespace CyclotomicTrace

open Polynomial

end CyclotomicTrace

end
end

section
section
/-!
# A dense subgroup of `SL(2, ℝ)` contains an elliptic element of infinite order

Route (ported from Lodha–Moore statement 7, part G1):
* Jørgensen's sequence `B₀ = B`, `B_{n+1} = B_n A B_n⁻¹` gives, inside a two-generator subgroup
  of `Γ`, nontrivial elements `x n ≠ ±1` tending to `1`;
* a finitely generated subring of `ℝ` contains only finitely many numbers `z + z⁻¹` with `z` a
  root of unity (`CyclotomicTrace.finite_add_inv_rootOfUnity`);
* density gives four elliptic elements of `Γ` whose matrices span `M₂(ℝ)`; if every elliptic
  element of the finitely generated group were of finite order, the traces `tr (y i * x n)` would
  be eventually constant, so the trace pairing against `x n - 1` would vanish on a basis, forcing
  `x n = 1`.
-/

open Matrix Filter Topology

namespace DenseSL2

/-- `SL(2, ℝ)`. -/
abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- The entries of an element of `SL(2, ℝ)`. -/
abbrev ent (g : SL2) (i j : Fin 2) : ℝ := (g : Matrix (Fin 2) (Fin 2) ℝ) i j

/-- The trace of an element of `SL(2, ℝ)`. -/
def tr (a : SL2) : ℝ := ent a 0 0 + ent a 1 1

/-- `a` is elliptic of infinite order (modulo `±1`). -/
def IsEllInf (a : SL2) : Prop := |tr a| < 2 ∧ ∀ n : ℕ, 0 < n → a ^ n ≠ 1 ∧ a ^ n ≠ -1

/-! ### Entries -/

lemma slr_ext {A B : SL2} (h : ∀ i j, ent A i j = ent B i j) : A = B := by
  ext i j
  exact h i j

lemma ent_mul (A B : SL2) (i j : Fin 2) :
    ent (A * B) i j = ent A i 0 * ent B 0 j + ent A i 1 * ent B 1 j := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

lemma ent_one (i j : Fin 2) : ent (1 : SL2) i j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [ent]

lemma det_ent (g : SL2) : ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 = 1 := by
  have h := g.2
  rw [Matrix.det_fin_two] at h
  exact h

/-- An element of `SL(2, ℝ)` from its entries. -/
def mk2 (p q r s : ℝ) (h : p * s - q * r = 1) : SL2 :=
  ⟨!![p, q; r, s], by rw [Matrix.det_fin_two_of]; exact h⟩

@[simp] lemma ent_mk2_00 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 0 0 = p := rfl
@[simp] lemma ent_mk2_01 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 0 1 = q := rfl
@[simp] lemma ent_mk2_10 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 1 0 = r := rfl
@[simp] lemma ent_mk2_11 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 1 1 = s := rfl

@[simp] lemma ent_inv_00 (g : SL2) : ent g⁻¹ 0 0 = ent g 1 1 := by
  simp [ent, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

@[simp] lemma ent_inv_01 (g : SL2) : ent g⁻¹ 0 1 = - ent g 0 1 := by
  simp [ent, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

@[simp] lemma ent_inv_10 (g : SL2) : ent g⁻¹ 1 0 = - ent g 1 0 := by
  simp [ent, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

@[simp] lemma ent_inv_11 (g : SL2) : ent g⁻¹ 1 1 = ent g 0 0 := by
  simp [ent, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

lemma continuous_ent (i j : Fin 2) : Continuous (fun g : SL2 => ent g i j) :=
  continuous_subtype_val.matrix_elem i j

lemma continuous_tr : Continuous tr :=
  (continuous_ent 0 0).add (continuous_ent 1 1)

lemma tendsto_of_ent {f : ℕ → SL2} {A : SL2}
    (h : ∀ i j, Tendsto (fun n => ent (f n) i j) atTop (𝓝 (ent A i j))) :
    Tendsto f atTop (𝓝 A) := by
  have hind : Topology.IsInducing (fun g : SL2 => (g : Matrix (Fin 2) (Fin 2) ℝ)) :=
    Topology.IsInducing.subtypeVal
  exact hind.tendsto_nhds_iff.2 (tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => h i j)

lemma tr_eq_trace (a : SL2) : Matrix.trace (a : Matrix (Fin 2) (Fin 2) ℝ) = tr a := by
  rw [Matrix.trace_fin_two]
  rfl

/-- Density: every nonempty open set meets `Γ`. -/
lemma exists_mem_of_isOpen (Γ : Subgroup SL2) (hΓ : Dense (Γ : Set SL2)) {U : Set SL2}
    (hU : IsOpen U) (hne : U.Nonempty) : ∃ g ∈ Γ, g ∈ U := by
  obtain ⟨g, hgU, hgΓ⟩ := hΓ.inter_open_nonempty U hU hne
  exact ⟨g, hgΓ, hgU⟩

/-! ### Jørgensen's identity -/

/-- `γ(A, B) = tr [A, B] - 2`. -/
def gam (A B : SL2) : ℝ := tr (A * B * A⁻¹ * B⁻¹) - 2

/-- The Fricke formula `γ(A, B) = x² + y² + z² - x y z - 4`. -/
lemma gam_eq (A B : SL2) :
    gam A B = tr A ^ 2 + tr B ^ 2 + tr (A * B) ^ 2 - tr A * tr B * tr (A * B) - 4 := by
  have hA := det_ent A
  have hB := det_ent B
  simp only [gam, tr, ent_mul, ent_inv_00, ent_inv_01, ent_inv_10, ent_inv_11]
  linear_combination ((ent B 0 0 + ent B 1 1) ^ 2 -
      2 * (ent B 0 0 * ent B 1 1 - ent B 0 1 * ent B 1 0)) * hA +
    ((ent A 0 0 + ent A 1 1) ^ 2 - 2) * hB

lemma tr_conj (A B : SL2) : tr (B * A * B⁻¹) = tr A := by
  have hB := det_ent B
  simp only [tr, ent_mul, ent_inv_00, ent_inv_01, ent_inv_10, ent_inv_11]
  linear_combination (ent A 0 0 + ent A 1 1) * hB

lemma tr_mul_conj (A B : SL2) :
    tr (A * (B * A * B⁻¹)) = tr A * tr B * tr (A * B) - tr B ^ 2 - tr (A * B) ^ 2 + 2 := by
  have hA := det_ent A
  have hB := det_ent B
  simp only [tr, ent_mul, ent_inv_00, ent_inv_01, ent_inv_10, ent_inv_11]
  linear_combination (-(ent B 0 0 + ent B 1 1) ^ 2 +
      2 * (ent B 0 0 * ent B 1 1 - ent B 0 1 * ent B 1 0)) * hA + 2 * hB

/-- Jørgensen's identity `γ(A, B A B⁻¹) = γ(A, B) (γ(A, B) - β(A))`, `β(A) = tr² A - 4`. -/
lemma gam_conj (A B : SL2) :
    gam A (B * A * B⁻¹) = gam A B * (gam A B - (tr A ^ 2 - 4)) := by
  rw [gam_eq A (B * A * B⁻¹), gam_eq A B, tr_conj, tr_mul_conj]
  ring

lemma gam_eq_zero_of_commute {A B : SL2} (h : Commute A B) : gam A B = 0 := by
  rw [gam, h.eq, mul_inv_cancel_right, mul_inv_cancel]
  simp [tr, ent_one]
  norm_num

lemma continuous_gam_left (B : SL2) : Continuous (fun A => gam A B) :=
  (continuous_tr.comp (((continuous_id.mul continuous_const).mul continuous_inv).mul
    continuous_const)).sub continuous_const

lemma continuous_gam_right (A : SL2) : Continuous (fun B => gam A B) :=
  (continuous_tr.comp (((continuous_const.mul continuous_id).mul continuous_const).mul
    continuous_inv)).sub continuous_const

/-! ### The entrywise `ℓ¹` norm -/

/-- The real matrix of an element of `SL(2, ℝ)`. -/
def M (g : SL2) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => ent g i j

lemma M_apply (g : SL2) (i j : Fin 2) : M g i j = ent g i j := rfl

lemma M_mul (g h : SL2) : M (g * h) = M g * M h := by
  ext i j
  simp [M, ent_mul, Matrix.mul_apply, Fin.sum_univ_two]

lemma M_one : M 1 = 1 := by
  ext i j
  simp only [M, Matrix.of_apply, ent_one, Matrix.one_apply]

/-- The entrywise `ℓ¹` norm of a `2 × 2` real matrix. -/
def nn (X : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  |X 0 0| + |X 0 1| + |X 1 0| + |X 1 1|

lemma nn_nonneg (X : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ nn X := by
  unfold nn; positivity

lemma abs_le_nn (X : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) : |X i j| ≤ nn X := by
  unfold nn
  have := abs_nonneg (X 0 0); have := abs_nonneg (X 0 1)
  have := abs_nonneg (X 1 0); have := abs_nonneg (X 1 1)
  fin_cases i <;> fin_cases j <;> simp <;> linarith

lemma nn_add (X Y : Matrix (Fin 2) (Fin 2) ℝ) : nn (X + Y) ≤ nn X + nn Y := by
  simp only [nn, Matrix.add_apply]
  linarith [abs_add_le (X 0 0) (Y 0 0), abs_add_le (X 0 1) (Y 0 1), abs_add_le (X 1 0) (Y 1 0),
    abs_add_le (X 1 1) (Y 1 1)]

lemma nn_sub (X Y : Matrix (Fin 2) (Fin 2) ℝ) : nn (X - Y) ≤ nn X + nn Y := by
  simp only [nn, Matrix.sub_apply]
  linarith [abs_sub (X 0 0) (Y 0 0), abs_sub (X 0 1) (Y 0 1), abs_sub (X 1 0) (Y 1 0),
    abs_sub (X 1 1) (Y 1 1)]

lemma abs_mul_add_le (a b c d : ℝ) : |a * b + c * d| ≤ |a| * |b| + |c| * |d| := by
  rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _

lemma nn_mul (X Y : Matrix (Fin 2) (Fin 2) ℝ) : nn (X * Y) ≤ nn X * nn Y := by
  simp only [nn, Matrix.mul_apply, Fin.sum_univ_two]
  have h1 := abs_mul_add_le (X 0 0) (Y 0 0) (X 0 1) (Y 1 0)
  have h2 := abs_mul_add_le (X 0 0) (Y 0 1) (X 0 1) (Y 1 1)
  have h3 := abs_mul_add_le (X 1 0) (Y 0 0) (X 1 1) (Y 1 0)
  have h4 := abs_mul_add_le (X 1 0) (Y 0 1) (X 1 1) (Y 1 1)
  have a1 := abs_nonneg (X 0 0); have a2 := abs_nonneg (X 0 1)
  have a3 := abs_nonneg (X 1 0); have a4 := abs_nonneg (X 1 1)
  have b1 := abs_nonneg (Y 0 0); have b2 := abs_nonneg (Y 0 1)
  have b3 := abs_nonneg (Y 1 0); have b4 := abs_nonneg (Y 1 1)
  nlinarith [mul_nonneg a1 b3, mul_nonneg a1 b4, mul_nonneg a2 b1, mul_nonneg a2 b2,
    mul_nonneg a3 b3, mul_nonneg a3 b4, mul_nonneg a4 b1, mul_nonneg a4 b2]

lemma nn_M_inv (g : SL2) : nn (M g⁻¹) = nn (M g) := by
  simp only [nn, M_apply, ent_inv_00, ent_inv_01, ent_inv_10, ent_inv_11, abs_neg]
  ring

lemma nn_sub_comm (X Y : Matrix (Fin 2) (Fin 2) ℝ) : nn (X - Y) = nn (Y - X) := by
  simp only [nn, Matrix.sub_apply]
  rw [abs_sub_comm (X 0 0), abs_sub_comm (X 0 1), abs_sub_comm (X 1 0), abs_sub_comm (X 1 1)]

lemma continuous_nn_M (C : Matrix (Fin 2) (Fin 2) ℝ) :
    Continuous (fun g : SL2 => nn (M g - C)) := by
  simp only [nn, Matrix.sub_apply, M_apply]
  exact (((((continuous_ent 0 0).sub continuous_const).abs.add
    ((continuous_ent 0 1).sub continuous_const).abs).add
    ((continuous_ent 1 0).sub continuous_const).abs).add
    ((continuous_ent 1 1).sub continuous_const).abs)

/-- The Zassenhaus-type estimate for one step of Jørgensen's iteration. -/
lemma nn_step (A B : SL2) :
    nn (M (B * A * B⁻¹) - M A) ≤
      2 * nn (M A - 1) * (nn (M A) + nn (M B - M A)) * nn (M B - M A) := by
  set X := M B
  set Y := M A
  set Xi := M B⁻¹
  have hX : X * Xi = 1 := by rw [← M_mul, mul_inv_cancel, M_one]
  have e1 : (X - Y) * (Y - 1) - (Y - 1) * (X - Y) = X * Y - Y * X := by noncomm_ring
  have e2 : M (B * A * B⁻¹) - Y = ((X - Y) * (Y - 1) - (Y - 1) * (X - Y)) * Xi := by
    rw [e1, sub_mul, mul_assoc Y X Xi, hX, mul_one, M_mul, M_mul]
  have hXi : nn Xi = nn X := nn_M_inv B
  have hXle : nn X ≤ nn Y + nn (X - Y) := by
    have := nn_add Y (X - Y)
    rwa [add_sub_cancel] at this
  have hE := nn_nonneg (X - Y)
  have hF := nn_nonneg (Y - 1)
  have hC : nn ((X - Y) * (Y - 1) - (Y - 1) * (X - Y)) ≤ 2 * nn (Y - 1) * nn (X - Y) := by
    have := nn_sub ((X - Y) * (Y - 1)) ((Y - 1) * (X - Y))
    have := nn_mul (X - Y) (Y - 1)
    have := nn_mul (Y - 1) (X - Y)
    linarith
  rw [e2]
  calc nn (((X - Y) * (Y - 1) - (Y - 1) * (X - Y)) * Xi)
      ≤ nn ((X - Y) * (Y - 1) - (Y - 1) * (X - Y)) * nn Xi := nn_mul _ _
    _ ≤ (2 * nn (Y - 1) * nn (X - Y)) * (nn Y + nn (X - Y)) := by
        rw [hXi]
        exact mul_le_mul hC hXle (nn_nonneg _) (by positivity)
    _ = 2 * nn (Y - 1) * (nn Y + nn (X - Y)) * nn (X - Y) := by ring

/-! ### Jørgensen's sequence -/

/-- `B₀ = B`, `B_{n+1} = B_n A B_n⁻¹`. -/
def seqB (A B : SL2) : ℕ → SL2
  | 0 => B
  | n + 1 => seqB A B n * A * (seqB A B n)⁻¹

lemma seqB_mem (A B : SL2) (n : ℕ) : seqB A B n ∈ Subgroup.closure ({A, B} : Set SL2) := by
  have hA : A ∈ Subgroup.closure ({A, B} : Set SL2) := Subgroup.subset_closure (by simp)
  induction n with
  | zero => exact Subgroup.subset_closure (by simp [seqB])
  | succ n ih => exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ih hA) (Subgroup.inv_mem _ ih)

lemma gam_seqB_pos (A B : SL2) (hA : |tr A| < 2) (hB : 0 < gam A B) (n : ℕ) :
    0 < gam A (seqB A B n) := by
  have hb : tr A ^ 2 - 4 < 0 := by
    have := abs_lt.1 hA
    nlinarith
  induction n with
  | zero => exact hB
  | succ n ih =>
    show 0 < gam A (seqB A B n * A * (seqB A B n)⁻¹)
    rw [gam_conj]
    exact mul_pos ih (by linarith)

lemma nn_seqB_le (A B : SL2) {ρ : ℝ} (hρ : 2 * nn (M A - 1) * (nn (M A) + 1) = ρ) (hρ1 : ρ ≤ 1)
    (hB : nn (M B - M A) ≤ 1) (n : ℕ) : nn (M (seqB A B n) - M A) ≤ ρ ^ n := by
  have hρ0 : 0 ≤ ρ := by
    rw [← hρ]; have := nn_nonneg (M A - 1); have := nn_nonneg (M A); positivity
  induction n with
  | zero => simpa [seqB] using hB
  | succ n ih =>
    have hstep := nn_step A (seqB A B n)
    set e := nn (M (seqB A B n) - M A)
    have he0 : 0 ≤ e := nn_nonneg _
    have he1 : e ≤ 1 := ih.trans (pow_le_one₀ hρ0 hρ1)
    have hf := nn_nonneg (M A - 1)
    have ha := nn_nonneg (M A)
    have h1 : 2 * nn (M A - 1) * (nn (M A) + e) * e ≤ ρ * e := by
      rw [← hρ]
      have : 2 * nn (M A - 1) * (nn (M A) + e) ≤ 2 * nn (M A - 1) * (nn (M A) + 1) := by
        have : 0 ≤ 2 * nn (M A - 1) := by positivity
        exact mul_le_mul_of_nonneg_left (by linarith) this
      exact mul_le_mul_of_nonneg_right this he0
    calc nn (M (seqB A B (n + 1)) - M A) ≤ 2 * nn (M A - 1) * (nn (M A) + e) * e := hstep
      _ ≤ ρ * e := h1
      _ ≤ ρ * ρ ^ n := mul_le_mul_of_nonneg_left ih hρ0
      _ = ρ ^ (n + 1) := by ring

lemma tendsto_seqB (A B : SL2) (hρ1 : 2 * nn (M A - 1) * (nn (M A) + 1) < 1)
    (hB : nn (M B - M A) ≤ 1) : Tendsto (seqB A B) atTop (𝓝 A) := by
  set ρ := 2 * nn (M A - 1) * (nn (M A) + 1) with hρ
  have hρ0 : 0 ≤ ρ := by
    have := nn_nonneg (M A - 1); have := nn_nonneg (M A); positivity
  have hpow : Tendsto (fun n : ℕ => ρ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
  apply tendsto_of_ent
  intro i j
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hpow
  have h1 := abs_le_nn (M (seqB A B n) - M A) i j
  simp only [Matrix.sub_apply, M_apply] at h1
  rw [Real.norm_eq_abs]
  exact h1.trans (nn_seqB_le A B hρ.symm hρ1.le hB n)

/-! ### The explicit pair and the choice by density -/

/-- An elliptic element close to `1`. -/
noncomputable def A₀ : SL2 := mk2 1 (-(1 / 20)) (1 / 20) (1 - (1 / 20) ^ 2) (by ring)

/-- `diag(5/4, 4/5)`. -/
noncomputable def B₀ : SL2 := mk2 (5 / 4) 0 0 (4 / 5) (by norm_num)

lemma A₀_tr : |tr A₀| < 2 := by
  simp only [tr, A₀, ent_mk2_00, ent_mk2_11]
  rw [abs_lt]; constructor <;> norm_num

lemma A₀_nn : 2 * nn (M A₀ - 1) * (nn (M A₀) + 1) < 1 := by
  simp only [nn, Matrix.sub_apply, M_apply, A₀, ent_mk2_00, ent_mk2_01, ent_mk2_10, ent_mk2_11,
    Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
  norm_num [abs_of_pos, abs_of_neg]

lemma A₀B₀_gam : 0 < gam A₀ B₀ := by
  rw [gam_eq]
  simp only [tr, ent_mul, A₀, B₀, ent_mk2_00, ent_mk2_01, ent_mk2_10, ent_mk2_11]
  norm_num

lemma A₀B₀_nn : nn (M B₀ - M A₀) < 1 := by
  simp only [nn, Matrix.sub_apply, M_apply, A₀, B₀, ent_mk2_00, ent_mk2_01, ent_mk2_10,
    ent_mk2_11]
  norm_num [abs_of_pos, abs_of_neg]

/-- Jørgensen: a two-generator subgroup of `Γ` with elements `≠ ±1` tending to `1`. -/
theorem exists_closure_seq_tendsto_one (Γ : Subgroup SL2) (hΓ : Dense (Γ : Set SL2)) :
    ∃ A ∈ Γ, ∃ B ∈ Γ, ∃ x : ℕ → SL2,
      (∀ n, x n ∈ Subgroup.closure ({A, B} : Set SL2)) ∧ (∀ n, x n ≠ 1 ∧ x n ≠ -1) ∧
      Tendsto x atTop (𝓝 1) := by
  -- choose `A`
  set UA : Set SL2 := {A | |tr A| < 2} ∩ {A | 2 * nn (M A - 1) * (nn (M A - 0) + 1) < 1} ∩
    {A | 0 < gam A B₀} ∩ {A | nn (M A - M B₀) < 1} with hUA
  have hUAo : IsOpen UA := by
    refine ((((isOpen_lt continuous_tr.abs continuous_const).inter ?_).inter
      (isOpen_lt continuous_const (continuous_gam_left B₀))).inter
      (isOpen_lt (continuous_nn_M (M B₀)) continuous_const))
    exact isOpen_lt ((continuous_const.mul (continuous_nn_M 1)).mul
      ((continuous_nn_M 0).add continuous_const)) continuous_const
  have hA₀ : A₀ ∈ UA := by
    refine ⟨⟨⟨A₀_tr, ?_⟩, A₀B₀_gam⟩, ?_⟩
    · simpa using A₀_nn
    · show nn (M A₀ - M B₀) < 1
      rw [nn_sub_comm]; exact A₀B₀_nn
  obtain ⟨A, hAΓ, ⟨⟨⟨hAtr, hAnn⟩, hAgam⟩, hAB₀⟩⟩ := exists_mem_of_isOpen Γ hΓ hUAo ⟨A₀, hA₀⟩
  replace hAnn : 2 * nn (M A - 1) * (nn (M A) + 1) < 1 := by simpa using hAnn
  -- choose `B`
  set VB : Set SL2 := {B | 0 < gam A B} ∩ {B | nn (M B - M A) < 1} with hVB
  have hVBo : IsOpen VB :=
    (isOpen_lt continuous_const (continuous_gam_right A)).inter
      (isOpen_lt (continuous_nn_M (M A)) continuous_const)
  have hB₀ : B₀ ∈ VB := by
    refine ⟨hAgam, ?_⟩
    show nn (M B₀ - M A) < 1
    rw [nn_sub_comm]; exact hAB₀
  obtain ⟨B, hBΓ, hBgam, hBnn⟩ := exists_mem_of_isOpen Γ hΓ hVBo ⟨B₀, hB₀⟩
  -- the sequence
  refine ⟨A, hAΓ, B, hBΓ, fun n => seqB A B n * A⁻¹, fun n => ?_, fun n => ?_, ?_⟩
  · have hA : A ∈ Subgroup.closure ({A, B} : Set SL2) := Subgroup.subset_closure (by simp)
    exact Subgroup.mul_mem _ (seqB_mem A B n) (Subgroup.inv_mem _ hA)
  · have hpos := gam_seqB_pos A B hAtr hBgam n
    constructor
    · intro h
      rw [mul_inv_eq_one] at h
      rw [h, gam_eq_zero_of_commute (Commute.refl A)] at hpos
      exact lt_irrefl _ hpos
    · intro h
      rw [mul_inv_eq_iff_eq_mul] at h
      have hc : Commute A (-1 * A) := ((Commute.neg_one_left A).symm).mul_right (Commute.refl A)
      rw [h, gam_eq_zero_of_commute hc] at hpos
      exact lt_irrefl _ hpos
  · have h := (tendsto_seqB A B hAnn hBnn.le).mul (tendsto_const_nhds (x := A⁻¹))
    rwa [mul_inv_cancel] at h

/-! ### The trace-pairing argument -/

/-- Entries of elements of `closure F` lie in any subring containing the entries of `F`. -/
lemma ent_mem_of_mem_closure (F : Finset SL2) (R : Subring ℝ)
    (hF : ∀ g ∈ F, ∀ i j, ent g i j ∈ R) {g : SL2} (hg : g ∈ Subgroup.closure (F : Set SL2)) :
    ∀ i j, ent g i j ∈ R := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hF x hx
  | one =>
    intro i j
    rw [ent_one]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  | mul x y _ _ hx hy =>
    intro i j
    rw [ent_mul]
    exact R.add_mem (R.mul_mem (hx _ _) (hy _ _)) (R.mul_mem (hx _ _) (hy _ _))
  | inv x _ hx =>
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩ <;> rw [Fin.forall_fin_two] <;> refine ⟨?_, ?_⟩
    · rw [ent_inv_00]; exact hx 1 1
    · rw [ent_inv_01]; exact R.neg_mem (hx 0 1)
    · rw [ent_inv_10]; exact R.neg_mem (hx 1 0)
    · rw [ent_inv_11]; exact hx 0 0

/-- If `a ^ N = 1` (`N > 0`), then `tr a = z + z⁻¹` for a root of unity `z`: take `z` an
eigenvalue of `a` over `ℂ`. -/
lemma exists_root_of_pow_eq_one (a : SL2) {N : ℕ} (hN : 0 < N) (ha : a ^ N = 1) :
    ∃ z : ℂ, (∃ n : ℕ, 0 < n ∧ z ^ n = 1) ∧ ((tr a : ℝ) : ℂ) = z + z⁻¹ := by
  set t : ℂ := ((tr a : ℝ) : ℂ) with ht
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z * z - t * z + 1 = 0 := by
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (discrim (1 : ℂ) (-t) 1)
    obtain ⟨x, hx⟩ := exists_quadratic_eq_zero (one_ne_zero) ⟨s, hs⟩
    exact ⟨x, by linear_combination hx⟩
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hzinv : z⁻¹ = t - z := by
    have h : z * (t - z) = 1 := by linear_combination -hz
    exact (eq_inv_of_mul_eq_one_right h).symm
  refine ⟨z, ⟨N, hN, ?_⟩, by rw [hzinv]; ring⟩
  let φ : ℝ →+* ℂ := Complex.ofRealHom
  let M : Matrix (Fin 2) (Fin 2) ℂ := φ.mapMatrix (a : Matrix (Fin 2) (Fin 2) ℝ)
  have hM : ∀ i j, M i j = (ent a i j : ℂ) := fun i j => rfl
  have hdet0 := det_ent a
  have hdet : (M - z • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_zero, sub_zero, mul_one, hM]
    have h1 : ((ent a 0 0 : ℝ) : ℂ) * (ent a 1 1 : ℂ) - (ent a 0 1 : ℂ) * (ent a 1 0 : ℂ) = 1 := by
      exact_mod_cast hdet0
    have h2 : t = (ent a 0 0 : ℂ) + (ent a 1 1 : ℂ) := by rw [ht, tr]; push_cast; rfl
    linear_combination h1 + hz + z * h2
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hMv : M *ᵥ v = z • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.smul_mulVec, Matrix.one_mulVec] at hv
    exact hv
  have hpow : ∀ k : ℕ, (M ^ k) *ᵥ v = z ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_smul, ih, smul_smul, ← pow_succ']
  have hMN : M ^ N = 1 := by
    simp only [M]
    rw [← map_pow, ← Matrix.SpecialLinearGroup.coe_pow, ha, Matrix.SpecialLinearGroup.coe_one,
      map_one]
  have hN' := hpow N
  rw [hMN, Matrix.one_mulVec] at hN'
  by_contra hne
  apply hv0
  have h0 : (1 - z ^ N) • v = 0 := by rw [sub_smul, one_smul, ← hN', sub_self]
  exact (smul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 (Ne.symm hne))

/-- A convergent sequence eventually lying in a finite set is eventually constant. -/
lemma eventually_eq_of_tendsto_of_finite {u : ℕ → ℝ} {L : ℝ} {T : Set ℝ} (hT : T.Finite)
    (hu : Tendsto u atTop (𝓝 L)) (hev : ∀ᶠ n in atTop, u n ∈ T) : ∀ᶠ n in atTop, u n = L := by
  have hC : IsClosed (T \ {L}) := (hT.sdiff).isClosed
  have h2 : ∀ᶠ n in atTop, u n ∈ (T \ {L})ᶜ :=
    hu.eventually (hC.isOpen_compl.mem_nhds (by simp))
  filter_upwards [hev, h2] with n h1 h2
  by_contra hne
  exact h2 ⟨h1, hne⟩

/-- Trace of `y * x` in terms of entries. -/
lemma tr_mul (y x : SL2) :
    tr (y * x) = ent y 0 0 * ent x 0 0 + ent y 0 1 * ent x 1 0 + ent y 1 0 * ent x 0 1 +
      ent y 1 1 * ent x 1 1 := by
  rw [tr, ent_mul, ent_mul]
  ring

/-- The trace-pairing argument. -/
theorem exists_ellInf_of_seq (F : Finset SL2) (x : ℕ → SL2)
    (hx : ∀ n, x n ∈ Subgroup.closure (F : Set SL2)) (hx1 : ∀ n, x n ≠ 1 ∧ x n ≠ -1)
    (hlim : Tendsto x atTop (𝓝 1)) (y : Fin 4 → SL2)
    (hy : ∀ i, y i ∈ Subgroup.closure (F : Set SL2)) (hyell : ∀ i, |tr (y i)| < 2)
    (hind : LinearIndependent ℝ (fun i => Matrix.of fun j k => ent (y i) j k)) :
    ∃ a ∈ Subgroup.closure (F : Set SL2), IsEllInf a := by
  classical
  by_contra hcon
  push Not at hcon
  set s : Finset ℝ :=
    F.biUnion fun g => Finset.univ.image fun p : Fin 2 × Fin 2 => ent g p.1 p.2 with hs
  set R : Subring ℝ := Subring.closure (s : Set ℝ) with hR
  have hent : ∀ g ∈ Subgroup.closure (F : Set SL2), ∀ i j, ent g i j ∈ R := by
    intro g hg
    refine ent_mem_of_mem_closure F R (fun g hg i j => Subring.subset_closure ?_) hg
    simp only [hs, Finset.coe_biUnion, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_iUnion, Set.mem_range, Finset.mem_coe]
    exact ⟨g, hg, (i, j), rfl⟩
  set T : Set ℝ := {r : ℝ | r ∈ Subring.closure (s : Set ℝ) ∧
      ∃ z : ℂ, (∃ n : ℕ, 0 < n ∧ z ^ n = 1) ∧ (r : ℂ) = z + z⁻¹} with hT
  have hTfin : T.Finite := CyclotomicTrace.finite_add_inv_rootOfUnity s
  -- an elliptic element of `closure F` has trace in `T`
  have hkey : ∀ g ∈ Subgroup.closure (F : Set SL2), |tr g| < 2 → tr g ∈ T := by
    intro g hg hlt
    refine ⟨R.add_mem (hent g hg 0 0) (hent g hg 1 1), ?_⟩
    have hne := hcon g hg
    simp only [IsEllInf, not_and, not_forall] at hne
    obtain ⟨m, hm, hm'⟩ := hne hlt
    have hsq : g ^ (m * 2) = 1 := by
      rw [pow_mul]
      by_cases h1 : g ^ m = 1
      · rw [h1, one_pow]
      · have h2 : g ^ m = -1 := by
          by_contra h2
          exact hm' h1 h2
        rw [h2, pow_two, neg_one_mul, neg_neg]
    exact exists_root_of_pow_eq_one g (by omega) hsq
  -- traces converge
  have hxent : ∀ j k, Tendsto (fun n => ent (x n) j k) atTop (𝓝 (ent (1 : SL2) j k)) :=
    fun j k => ((continuous_ent j k).tendsto 1).comp hlim
  have htr : ∀ i, Tendsto (fun n => tr (y i * x n)) atTop (𝓝 (tr (y i))) := by
    intro i
    have h := (((tendsto_const_nhds (x := ent (y i) 0 0)).mul (hxent 0 0)).add
      ((tendsto_const_nhds (x := ent (y i) 0 1)).mul (hxent 1 0))).add
      ((tendsto_const_nhds (x := ent (y i) 1 0)).mul (hxent 0 1)) |>.add
      ((tendsto_const_nhds (x := ent (y i) 1 1)).mul (hxent 1 1))
    simp only [ent_one, Fin.isValue, if_true, mul_one, zero_ne_one, one_ne_zero, if_false,
      mul_zero, add_zero] at h
    simp only [tr_mul]
    convert h using 2
    rw [tr]
  have hev : ∀ i, ∀ᶠ n in atTop, tr (y i * x n) = tr (y i) := by
    intro i
    refine eventually_eq_of_tendsto_of_finite hTfin (htr i) ?_
    have hlt : ∀ᶠ n in atTop, |tr (y i * x n)| < 2 :=
      (htr i).eventually ((isOpen_lt continuous_abs continuous_const).mem_nhds (hyell i))
    filter_upwards [hlt] with n hn
    exact hkey _ (Subgroup.mul_mem _ (hy i) (hx n)) hn
  obtain ⟨n, hn⟩ := (eventually_all.2 hev).exists
  -- the trace pairing against `x n - 1` vanishes on a basis
  set D : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun j k => ent (x n) j k - ent (1 : SL2) j k
    with hD
  let f : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] ℝ :=
    (Matrix.traceLinearMap (Fin 2) ℝ ℝ) ∘ₗ (LinearMap.mulRight ℝ D)
  have hf : ∀ Y, f Y = (Y * D).trace := fun Y => rfl
  have hfY : ∀ i, f (Matrix.of fun j k => ent (y i) j k) = 0 := by
    intro i
    rw [hf, Matrix.trace_fin_two]
    have h := hn i
    rw [tr_mul, tr] at h
    simp only [hD, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, ent_one, Fin.isValue,
      if_true, zero_ne_one, one_ne_zero, if_false]
    linear_combination h
  have hcard : Fintype.card (Fin 4) = Module.finrank ℝ (Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [Module.finrank_matrix]; simp
  let b := basisOfLinearIndependentOfCardEqFinrank hind hcard
  have hf0 : f = 0 := b.ext fun i => by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    exact hfY i
  have hDz : ∀ j k, D j k = 0 := by
    intro j k
    have h := congrArg (fun g => g (Matrix.of fun p q => if p = k ∧ q = j then (1 : ℝ) else 0)) hf0
    simp only [LinearMap.zero_apply, hf, Matrix.trace_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.of_apply] at h
    fin_cases j <;> fin_cases k <;> simpa using h
  apply (hx1 n).1
  apply slr_ext
  intro j k
  have := hDz j k
  simp only [hD, Matrix.of_apply] at this
  linarith

/-! ### Four linearly independent elliptic elements -/

/-- The four entries of `g`, as a vector. -/
def vec (g : SL2) : Fin 4 → ℝ := ![ent g 0 0, ent g 0 1, ent g 1 0, ent g 1 1]

/-- The `4 × 4` determinant of the entry vectors of four elements. -/
def D4 (v : Fin 4 → SL2) : ℝ := (Matrix.of fun i => vec (v i)).det

lemma continuous_vec : Continuous vec := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_ent 0 0
  · exact continuous_ent 0 1
  · exact continuous_ent 1 0
  · exact continuous_ent 1 1

/-- Flattening a `2 × 2` matrix. -/
def flat : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun M := ![M 0 0, M 0 1, M 1 0, M 1 1]
  map_add' M N := by
    ext i; fin_cases i <;> simp
  map_smul' c M := by
    ext i; fin_cases i <;> simp

lemma linearIndependent_of_D4 (v : Fin 4 → SL2) (h : D4 v ≠ 0) :
    LinearIndependent ℝ (fun i => Matrix.of fun j k => ent (v i) j k) := by
  apply LinearIndependent.of_comp flat
  have e : (flat ∘ fun i => Matrix.of fun j k => ent (v i) j k) =
      fun i => (Matrix.of fun i => vec (v i)) i := by
    funext i; ext j; fin_cases j <;> rfl
  rw [e]
  exact Matrix.linearIndependent_rows_of_det_ne_zero h

lemma step (Γ : Subgroup SL2) (hΓ : Dense (Γ : Set SL2)) (v : Fin 4 → SL2) (k : Fin 4)
    (htr : ∀ i, |tr (v i)| < 2) (hD : D4 v ≠ 0) :
    ∃ g ∈ Γ, (∀ i, |tr (Function.update v k g i)| < 2) ∧
      D4 (Function.update v k g) ≠ 0 := by
  classical
  set U : Set SL2 := {g | |tr g| < 2} ∩ {g | D4 (Function.update v k g) ≠ 0} with hUdef
  have hcont : Continuous fun g : SL2 => D4 (Function.update v k g) := by
    unfold D4
    apply Continuous.matrix_det
    have hu : Continuous fun g : SL2 => Function.update v k g :=
      continuous_const.update k continuous_id
    apply continuous_pi; intro i
    exact continuous_vec.comp ((continuous_apply i).comp hu)
  have hU : IsOpen U :=
    (isOpen_lt (continuous_abs.comp continuous_tr) continuous_const).inter
      (isOpen_ne_fun hcont continuous_const)
  have hne : U.Nonempty := ⟨v k, htr k, by simpa using hD⟩
  obtain ⟨g, hgΓ, hgU⟩ := exists_mem_of_isOpen Γ hΓ hU hne
  refine ⟨g, hgΓ, fun i => ?_, hgU.2⟩
  by_cases hi : i = k
  · subst hi; simpa using hgU.1
  · simpa [Function.update_of_ne hi] using htr i

/-- Four explicit elliptic matrices. -/
def R0 : SL2 := mk2 0 (-1) 1 0 (by norm_num)
def R1 : SL2 := mk2 1 (-1) 1 0 (by norm_num)
def R2 : SL2 := mk2 0 (-1) 1 1 (by norm_num)
def R3 : SL2 := mk2 1 (-2) 1 (-1) (by norm_num)

lemma D4_R : D4 ![R0, R1, R2, R3] ≠ 0 := by
  simp [D4, vec, R0, R1, R2, R3, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  norm_num

lemma tr_R : ∀ i, |tr (![R0, R1, R2, R3] i)| < 2 := by
  intro i
  fin_cases i <;> simp [tr, R0, R1, R2, R3]

/-- Four linearly independent elliptic elements of `Γ`. -/
theorem exists_four_elliptic (Γ : Subgroup SL2) (hΓ : Dense (Γ : Set SL2)) :
    ∃ y : Fin 4 → SL2, (∀ i, y i ∈ Γ) ∧ (∀ i, |tr (y i)| < 2) ∧
      LinearIndependent ℝ (fun i => Matrix.of fun j k => ent (y i) j k) := by
  classical
  have key : ∀ m : ℕ, m ≤ 4 → ∃ v : Fin 4 → SL2, (∀ i, |tr (v i)| < 2) ∧ D4 v ≠ 0 ∧
      ∀ i : Fin 4, i.val < m → v i ∈ Γ := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨![R0, R1, R2, R3], tr_R, D4_R, fun i hi => absurd hi (by omega)⟩
    | succ m ih =>
      intro hm
      obtain ⟨v, htr, hD, hmem⟩ := ih (by omega)
      obtain ⟨g, hgΓ, htr', hD'⟩ := step Γ hΓ v ⟨m, by omega⟩ htr hD
      refine ⟨Function.update v ⟨m, by omega⟩ g, htr', hD', fun i hi => ?_⟩
      by_cases h : i = ⟨m, by omega⟩
      · rw [h, Function.update_self]; exact hgΓ
      · rw [Function.update_of_ne h]
        apply hmem
        have : i.val ≠ m := fun h' => h (Fin.ext h')
        omega
  obtain ⟨v, htr, hD, hmem⟩ := key 4 le_rfl
  exact ⟨v, fun i => hmem i i.2, htr, linearIndependent_of_D4 v hD⟩

/-! ### Assembly -/

theorem exists_elliptic_infinite_order_of_dense (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hΓ : Dense (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ))) :
    ∃ a ∈ Γ, |Matrix.trace (a : Matrix (Fin 2) (Fin 2) ℝ)| < 2 ∧
      ∀ n : ℕ, 0 < n → a ^ n ≠ 1 ∧ a ^ n ≠ -1 := by
  classical
  obtain ⟨A, hA, B, hB, x, hx, hx1, hlim⟩ := exists_closure_seq_tendsto_one Γ hΓ
  obtain ⟨y, hyΓ, hyell, hind⟩ := exists_four_elliptic Γ hΓ
  set F : Finset SL2 := {A, B, y 0, y 1, y 2, y 3} with hF
  have hAB : Subgroup.closure ({A, B} : Set SL2) ≤ Subgroup.closure (F : Set SL2) :=
    Subgroup.closure_mono (by
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl <;> simp [hF])
  have hyF : ∀ i, y i ∈ Subgroup.closure (F : Set SL2) := fun i =>
    Subgroup.subset_closure (by fin_cases i <;> simp [hF])
  obtain ⟨a, ha, hell, hord⟩ :=
    exists_ellInf_of_seq F x (fun n => hAB (hx n)) hx1 hlim y hyF hyell hind
  have hFΓ : (F : Set SL2) ⊆ Γ := by
    intro g hg
    simp only [hF, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hA, hB, hyΓ 0, hyΓ 1, hyΓ 2, hyΓ 3]
  refine ⟨a, (Subgroup.closure_le _).2 hFΓ ha, ?_, hord⟩
  rw [tr_eq_trace]
  exact hell

end DenseSL2

end
end

section
open DenseSL2

theorem solution (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hΓ : Dense (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ))) :
    ∃ a ∈ Γ, |Matrix.trace (a : Matrix (Fin 2) (Fin 2) ℝ)| < 2 ∧
      ∀ n : ℕ, 0 < n → a ^ n ≠ 1 ∧ a ^ n ≠ -1 := by
  apply DenseSL2.exists_elliptic_infinite_order_of_dense <;> assumption

end
