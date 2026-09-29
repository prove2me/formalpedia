-- Prove2me | solution 1 for CannonFloydParry.exists_homeomorph_image_of_isIntegralProjective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T20:05:27.642397+00:00
-- url     : https://prove2.me/submissions/40062e8b-3123-4988-bbe7-7a7374b0c8a7

import Definitions.Def_CannonFloydParry_PIP
import Mathlib

namespace CannonFloydParry.S7

open Matrix

variable {n : ℕ}

/-- The real matrix of an integer matrix. -/
noncomputable abbrev rM (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  A.map (Int.cast : ℤ → ℝ)

lemma rM_mul (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) : rM (A * B) = rM A * rM B := by
  simp only [rM]
  exact Matrix.map_mul (f := Int.castRingHom ℝ)

lemma rM_one : rM (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) = 1 := by
  simp only [rM]
  exact Matrix.map_one _ Int.cast_zero Int.cast_one

lemma glAct_eq (A : GL (Fin (n + 1)) ℤ) (x : Fin (n + 1) → ℝ) :
    glAct A x = rM (A : Matrix _ _ ℤ) *ᵥ x := rfl

lemma glAct_inv_glAct (A : GL (Fin (n + 1)) ℤ) (x : Fin (n + 1) → ℝ) :
    glAct A⁻¹ (glAct A x) = x := by
  rw [glAct_eq, glAct_eq, Matrix.mulVec_mulVec, ← rM_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, rM_one, Matrix.one_mulVec]

lemma glAct_smul (A : GL (Fin (n + 1)) ℤ) (c : ℝ) (x : Fin (n + 1) → ℝ) :
    glAct A (c • x) = c • glAct A x := by
  rw [glAct_eq, glAct_eq, Matrix.mulVec_smul]

lemma glAct_ne_zero (A : GL (Fin (n + 1)) ℤ) {x : Fin (n + 1) → ℝ} (hx : x ≠ 0) :
    glAct A x ≠ 0 := by
  intro h
  apply hx
  rw [← glAct_inv_glAct A x, h, glAct_eq, Matrix.mulVec_zero]

lemma continuous_glAct (A : GL (Fin (n + 1)) ℤ) : Continuous (glAct A) := by
  show Continuous fun x => rM (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) *ᵥ x
  exact Continuous.matrix_mulVec continuous_const continuous_id

lemma sum_abs_pos {x : Fin (n + 1) → ℝ} (hx : x ≠ 0) : 0 < ∑ i, |x i| := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact lt_of_lt_of_le (abs_pos.mpr hi)
    (Finset.single_le_sum (f := fun i => |x i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))

lemma rho_smul {c : ℝ} (hc : 0 < c) (y : Fin (n + 1) → ℝ) : rho (c • y) = rho y := by
  unfold rho
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc, ← Finset.mul_sum, smul_smul]
  congr 1
  by_cases hs : ∑ i, |y i| = 0
  · simp [hs]
  · field_simp

lemma rho_of_mem {x : Fin (n + 1) → ℝ} (hx : x ∈ Simplex n) : rho x = x := by
  unfold rho
  have : ∑ i, |x i| = 1 := by
    rw [← hx.2]; exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (hx.1 i)
  simp [this]

lemma ne_zero_of_mem {x : Fin (n + 1) → ℝ} (hx : x ∈ Simplex n) : x ≠ 0 := by
  rintro rfl
  have := hx.2
  simp at this

lemma rho_eq_smul (y : Fin (n + 1) → ℝ) : rho y = (∑ i, |y i|)⁻¹ • y := rfl

lemma continuous_rho_comp {X : Type*} [TopologicalSpace X] {g : X → Fin (n + 1) → ℝ}
    (hg : Continuous g) (h0 : ∀ x, g x ≠ 0) : Continuous fun x => rho (g x) := by
  simp only [rho_eq_smul]
  refine Continuous.smul (Continuous.inv₀ ?_ fun x => (sum_abs_pos (h0 x)).ne') hg
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).comp hg |>.abs

/-- Key identity: `ρ (A⁻¹ ρ (A x)) = x` for `x ∈ Δₙ`. -/
lemma rho_glAct_inv_rho_glAct (A : GL (Fin (n + 1)) ℤ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ Simplex n) : rho (glAct A⁻¹ (rho (glAct A x))) = x := by
  have hs := sum_abs_pos (glAct_ne_zero A (ne_zero_of_mem hx))
  rw [rho_eq_smul (glAct A x), glAct_smul, glAct_inv_glAct, rho_smul (inv_pos.mpr hs),
    rho_of_mem hx]

theorem exists_homeomorph_image_of_isIntegralProjective' {n : ℕ} {U : Set (Simplex n)}
    {f : Simplex n → Simplex n} (hf : IsIntegralProjective U f) :
    ∃ e : U ≃ₜ f '' U, ∀ x : U, (e x : Simplex n) = f x := by
  obtain ⟨A, hA⟩ := hf
  -- the inverse formula
  have key : ∀ x ∈ U, rho (glAct A⁻¹ (f x : Fin (n + 1) → ℝ)) = x := by
    intro x hx
    rw [(hA x hx).2]
    exact rho_glAct_inv_rho_glAct A x.2
  have hinv : ∀ y : f '' U, ∃ x ∈ U, rho (glAct A⁻¹ ((y : Simplex n) : Fin (n + 1) → ℝ)) = x
      ∧ f x = y := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨x, hx, key x hx, rfl⟩
  let g : f '' U → U := fun y =>
    ⟨⟨rho (glAct A⁻¹ ((y : Simplex n) : Fin (n + 1) → ℝ)), by
        obtain ⟨x, _, h, _⟩ := hinv y; rw [h]; exact x.2⟩, by
        obtain ⟨x, hx, h, _⟩ := hinv y
        have : (⟨rho (glAct A⁻¹ ((y : Simplex n) : Fin (n + 1) → ℝ)), by rw [h]; exact x.2⟩ :
          Simplex n) = x := Subtype.ext h
        rw [this]; exact hx⟩
  let e : U ≃ f '' U :=
    { toFun := fun x => ⟨f x, x, x.2, rfl⟩
      invFun := g
      left_inv := by
        intro x
        apply Subtype.ext; apply Subtype.ext
        exact key x x.2
      right_inv := by
        intro y
        obtain ⟨x, hx, h, hfy⟩ := hinv y
        apply Subtype.ext
        have : (g y : Simplex n) = x := Subtype.ext h
        show f (g y : Simplex n) = y
        rw [this, hfy] }
  have hcont : Continuous e := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have : (fun x : U => ((f x : Simplex n) : Fin (n + 1) → ℝ)) =
        fun x : U => rho (glAct A ((x : Simplex n) : Fin (n + 1) → ℝ)) := by
      funext x; exact (hA x x.2).2
    show Continuous (fun x : U => ((f x : Simplex n) : Fin (n + 1) → ℝ))
    rw [this]
    exact continuous_rho_comp ((continuous_glAct A).comp
      (continuous_subtype_val.comp continuous_subtype_val))
      fun x => glAct_ne_zero A (ne_zero_of_mem x.1.2)
  have hcont' : Continuous e.symm := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_rho_comp ((continuous_glAct _).comp
      (continuous_subtype_val.comp continuous_subtype_val))
      fun y => glAct_ne_zero _ (ne_zero_of_mem y.1.2)
  exact ⟨⟨e, hcont, hcont'⟩, fun x => rfl⟩

end CannonFloydParry.S7

open CannonFloydParry in
theorem solution {n : ℕ} {U : Set (Simplex n)}
    {f : Simplex n → Simplex n} (hf : IsIntegralProjective U f) :
    ∃ e : U ≃ₜ f '' U, ∀ x : U, (e x : Simplex n) = f x := by
  exact S7.exists_homeomorph_image_of_isIntegralProjective' hf
