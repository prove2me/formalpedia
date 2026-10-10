-- Prove2me | solution 1 for ConleyZehnder.exists_rotation_mul_mem_spStar
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T22:08:56.866522+00:00
-- url     : https://prove2.me/submissions/01f55488-7559-4f07-be2c-8ccc1f3a4b9e

import Definitions.Def_ConleyZehnder_Setting
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Real.Pi.Bounds

open ConleyZehnder Matrix Complex ComplexOrder

namespace CZ10R

variable {n : ℕ}

abbrev CMat (n : ℕ) := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ

/-- Real matrices as complex matrices. -/
abbrev cx (M : Mat n) : CMat n := Complex.ofRealHom.mapMatrix M

theorem cx_det (M : Mat n) : (cx M).det = (M.det : ℂ) :=
  (RingHom.map_det Complex.ofRealHom M).symm

theorem cJ_sq : cx (J₀ n) * cx (J₀ n) = -1 := by
  rw [← map_mul, J_squared, map_neg, map_one]

/-- `(a • 1 + b • J)(c • 1 + d • J) = (ac - bd) • 1 + (ad + bc) • J` when `J² = -1`. -/
theorem key_identity (P J : CMat n) (hJ : J * J = -1) (c s : ℂ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (1 - P * (c • 1 + s • J)) *
        ((1 / 2 : ℂ) • (1 - I • J) + (c + s * I) • ((1 / 2 : ℂ) • (1 + I • J))) =
      ((1 / 2 : ℂ) • (1 - I • J) - P * ((1 / 2 : ℂ) • (1 + I • J))) +
        (c + s * I) • ((1 / 2 : ℂ) • (1 + I • J) - P * ((1 / 2 : ℂ) • (1 - I • J))) := by
  have hPJJ : P * J * J = -P := by rw [Matrix.mul_assoc, hJ, Matrix.mul_neg, Matrix.mul_one]
  have e : (1 - P * (c • 1 + s • J)) *
        ((1 / 2 : ℂ) • (1 - I • J) + (c + s * I) • ((1 / 2 : ℂ) • (1 + I • J))) =
      ((1 / 2 : ℂ) • (1 - I • J) - P * ((1 / 2 : ℂ) • (1 + I • J))) +
        (c + s * I) • ((1 / 2 : ℂ) • (1 + I • J) - P * ((1 / 2 : ℂ) • (1 - I • J))) -
        ((c ^ 2 + s ^ 2 - 1) / 2) • (P + I • (P * J)) := by
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one, hJ, hPJJ, ← Matrix.mul_assoc]
    match_scalars <;> ring_nf <;> simp only [I_sq] <;> ring
  rw [e, hcs]; simp

/-- Block matrix with diagonal blocks. -/
noncomputable def blk (a b c d : Fin n → ℝ) : Mat n :=
  fromBlocks (diagonal a) (diagonal b) (diagonal c) (diagonal d)

theorem blk_symp (a b c d : Fin n → ℝ) (h : ∀ j, a j * d j - b j * c j = 1) :
    IsSymplectic (blk a b c d) := by
  unfold IsSymplectic blk
  rw [SymplecticGroup.mem_iff]
  simp only [Matrix.J, fromBlocks_transpose, diagonal_transpose, fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, Matrix.mul_one, zero_add, add_zero,
    diagonal_mul_diagonal]
  congr 1
  · ext i j; by_cases hij : i = j <;> simp [diagonal_apply, hij] <;> ring
  · ext i j; by_cases hij : i = j <;> simp [diagonal_apply, hij]
    · subst hij; linarith [h i]
  · ext i j; by_cases hij : i = j <;> simp [diagonal_apply, hij]
    · subst hij; rw [one_apply_eq]; linarith [h i]
  · ext i j; by_cases hij : i = j <;> simp [diagonal_apply, hij] <;> ring

/-- The rotation `e^{θ J₀} = cos θ · Id + sin θ · J₀`. -/
noncomputable def rot (θ : ℝ) : Mat n := Real.cos θ • (1 : Mat n) + Real.sin θ • J₀ n

theorem rot_eq (θ : ℝ) : rot (n := n) θ = blk (fun _ => Real.cos θ) (fun _ => -Real.sin θ)
    (fun _ => Real.sin θ) (fun _ => Real.cos θ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    by_cases hij : i = j <;> simp [rot, blk, Matrix.J, diagonal_apply, one_apply, hij]

theorem rot_symp (θ : ℝ) : IsSymplectic (rot (n := n) θ) := by
  rw [rot_eq]; exact blk_symp _ _ _ _ fun _ => by nlinarith [Real.sin_sq_add_cos_sq θ]

theorem cx_smul (r : ℝ) (M : Mat n) :
    Complex.ofRealHom.mapMatrix (r • M) = (r : ℂ) • Complex.ofRealHom.mapMatrix M := by
  ext i j; simp

theorem cx_transpose (M : Mat n) : (cx M)ᴴ = cx Mᵀ := by
  ext i j; simp [conjTranspose_apply]

/-- The constant term `Π⁻ - A Π⁺` is invertible for symplectic `A`. -/
theorem B_det_ne_zero (A : Mat n) (hA : IsSymplectic A) :
    ((1 / 2 : ℂ) • (1 - I • cx (J₀ n)) - cx A * ((1 / 2 : ℂ) • (1 + I • cx (J₀ n)))).det ≠ 0 := by
  set J := cx (J₀ n) with hJdef
  set P := cx A
  have hJ : J * J = -1 := cJ_sq
  set Pa : CMat n := (1 / 2 : ℂ) • (1 + I • J)
  set Pb : CMat n := (1 / 2 : ℂ) • (1 - I • J)
  have hJb : J * Pb = I • Pb := by
    simp only [Pb, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, hJ]
    match_scalars <;> ring_nf <;> simp only [I_sq] <;> ring
  have hJa : J * Pa = (-I) • Pa := by
    simp only [Pa, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, hJ]
    match_scalars <;> ring_nf <;> simp only [I_sq] <;> ring
  have hab : Pa + Pb = 1 := by
    simp only [Pa, Pb]; module
  have hsympl : Pᴴ * J * P = J := by
    rw [cx_transpose, hJdef, ← map_mul, ← map_mul]
    exact congrArg _ ((SymplecticGroup.mem_iff').1 hA)
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set u := Pa *ᵥ v
  set w := Pb *ᵥ v
  have hw : w = P *ᵥ u := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, sub_eq_zero] at hv
    exact hv
  have hΩw : star w ⬝ᵥ (J *ᵥ w) = I * (star w ⬝ᵥ w) := by
    have : J *ᵥ w = I • w := by
      simp only [w, Matrix.mulVec_mulVec, hJb, Matrix.smul_mulVec]
    rw [this, dotProduct_smul, smul_eq_mul]
  have hΩu : star u ⬝ᵥ (J *ᵥ u) = -I * (star u ⬝ᵥ u) := by
    have : J *ᵥ u = (-I) • u := by
      simp only [u, Matrix.mulVec_mulVec, hJa, Matrix.smul_mulVec]
    rw [this, dotProduct_smul, smul_eq_mul]
  have hΩP : star w ⬝ᵥ (J *ᵥ w) = star u ⬝ᵥ (J *ᵥ u) := by
    rw [hw, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hsympl]
  rw [hΩw, hΩu] at hΩP
  have hsum : star w ⬝ᵥ w + star u ⬝ᵥ u = 0 := by
    have h2 : I * (star w ⬝ᵥ w + star u ⬝ᵥ u) = 0 := by linear_combination hΩP
    exact (mul_eq_zero.1 h2).resolve_left I_ne_zero
  obtain ⟨hw0, hu0⟩ := (add_eq_zero_iff_of_nonneg (dotProduct_star_self_nonneg w)
    (dotProduct_star_self_nonneg u)).1 hsum
  rw [dotProduct_star_self_eq_zero] at hw0 hu0
  apply hv0
  rw [← Matrix.one_mulVec v, ← hab, Matrix.add_mulVec]
  change u + w = 0
  rw [hw0, hu0, add_zero]

/-- A nonzero value at `0` forces a nonzero value somewhere on the unit circle. -/
theorem exists_unit_det_ne_zero (B C : CMat n) (hB : B.det ≠ 0) :
    ∃ θ : ℝ, (B + exp (θ * I) • C).det ≠ 0 := by
  let q : Polynomial ℂ :=
    (B.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • C.map Polynomial.C).det
  have hq : ∀ z, q.eval z = (B + z • C).det := fun z => by
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp <;> ring
  have hq0 : q ≠ 0 := by
    intro h
    apply hB
    have := hq 0
    rw [h, Polynomial.eval_zero, zero_smul, add_zero] at this
    exact this.symm
  by_contra hall
  push_neg at hall
  apply hq0
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine Set.infinite_of_injOn_mapsTo (f := fun θ : ℝ => exp (θ * I)) (s := Set.Ioo 0 1)
    ?_ ?_ (Set.Ioo_infinite (by norm_num))
  · intro a ha b hb hab
    obtain ⟨k, hk⟩ := exp_eq_exp_iff_exists_int.1 hab
    have hk' : ((a : ℂ)) = b + k * (2 * Real.pi) := by
      apply mul_right_cancel₀ I_ne_zero
      rw [hk]; push_cast; ring
    have hk'' : a = b + k * (2 * Real.pi) := by exact_mod_cast hk'
    have hk0 : (k : ℝ) = 0 := by
      rcases lt_trichotomy k 0 with h | h | h
      · have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h
        nlinarith [Real.pi_gt_three, ha.1, ha.2, hb.1, hb.2]
      · simp [h]
      · have : (1 : ℝ) ≤ k := by exact_mod_cast h
        nlinarith [Real.pi_gt_three, ha.1, ha.2, hb.1, hb.2]
    rw [hk'', hk0]; ring
  · intro θ _
    show Polynomial.IsRoot q _
    rw [Polynomial.IsRoot.def, hq]
    exact hall θ

end CZ10R

open CZ10R

theorem solution {n : ℕ} (A : Mat n) (hA : IsSymplectic A) :
    ∃ θ : ℝ, A * (Real.cos θ • (1 : Mat n) + Real.sin θ • J₀ n) ∈ SpStar n := by
  obtain ⟨θ, hθ⟩ := exists_unit_det_ne_zero _
    ((1 / 2 : ℂ) • (1 + I • cx (J₀ n)) - cx A * ((1 / 2 : ℂ) • (1 - I • cx (J₀ n))))
    (B_det_ne_zero A hA)
  have hR : IsSymplectic (Real.cos θ • (1 : Mat n) + Real.sin θ • J₀ n) := rot_symp θ
  refine ⟨θ, Submonoid.mul_mem _ hA hR, ?_⟩
  have hz : exp (θ * I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := by
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have hcs : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  rw [hz, ← key_identity (cx A) (cx (J₀ n)) cJ_sq _ _ hcs, det_mul] at hθ
  have h1 := left_ne_zero_of_mul hθ
  have hmap : cx (1 - A * (Real.cos θ • (1 : Mat n) + Real.sin θ • J₀ n)) =
      1 - cx A * ((Real.cos θ : ℂ) • 1 + (Real.sin θ : ℂ) • cx (J₀ n)) := by
    simp only [cx, map_sub, map_one, map_mul, map_add, cx_smul]
  rw [← hmap, cx_det] at h1
  exact_mod_cast h1
