-- Prove2me | solution 1 for DetANN.mgg_quadratic_form_bound
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-14T21:33:03.358604+00:00
-- url     : https://prove2.me/submissions/44476419-9778-4e07-98c6-c1f07621c659

import Mathlib
import Theorems.Thm_DetANN_mgg_fourier_inequality

open DetANN

namespace MGGAred

variable {m : ℕ} [NeZero m]

/-- The bilinear pairing `⟨x, y⟩ = x₁y₁ + x₂y₂` on `ℤ_m²`. -/
def dot (x y : ZMod m × ZMod m) : ZMod m := x.1 * y.1 + x.2 * y.2

/-- One-dimensional orthogonality: `∑_y ψ(u y) = m [u = 0]`. -/
lemma sum_char_1d (u : ZMod m) :
    ∑ y : ZMod m, ZMod.stdAddChar (u * y) = if u = 0 then (m : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod m) ℂ)) u
    (ZMod.isPrimitive_stdAddChar m)
  rw [ZMod.card, Nat.cast_ite, Nat.cast_zero] at h
  rw [← h]
  exact Finset.sum_congr rfl (fun y _ => by rw [mul_comm])

/-- Two-dimensional orthogonality: `∑_y ψ(⟨u, y⟩) = m² [u = 0]`. -/
lemma orth (u : ZMod m × ZMod m) :
    ∑ y : ZMod m × ZMod m, ZMod.stdAddChar (dot u y) = if u = 0 then (m : ℂ) ^ 2 else 0 := by
  rw [Fintype.sum_prod_type]
  simp only [dot, AddChar.map_add_eq_mul]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [sum_char_1d, sum_char_1d]
  by_cases h1 : u.1 = 0 <;> by_cases h2 : u.2 = 0 <;> simp [h1, h2, Prod.ext_iff, sq]

/-- The Fourier transform `F(y) = ∑_x f(x) ψ(⟨x, y⟩)`. -/
noncomputable def FT (f : ZMod m × ZMod m → ℝ) (y : ZMod m × ZMod m) : ℂ :=
  ∑ x, (f x : ℂ) * ZMod.stdAddChar (dot x y)

lemma conj_FT (f : ZMod m × ZMod m → ℝ) (y : ZMod m × ZMod m) :
    starRingEnd ℂ (FT f y) = ∑ x, (f x : ℂ) * ZMod.stdAddChar (-dot x y) := by
  unfold FT
  rw [map_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [map_mul, Complex.conj_ofReal, AddChar.map_neg_eq_conj]

/-- Twisted Parseval: `∑_y conj F(y) · ∑_w g(w) ψ(⟨L w, y⟩) = m² ∑_x f(x) g(L⁻¹ x)`. -/
lemma parseval_twist (f g : ZMod m × ZMod m → ℝ) (L : (ZMod m × ZMod m) ≃ (ZMod m × ZMod m)) :
    ∑ y, starRingEnd ℂ (FT f y) * ∑ w, (g w : ℂ) * ZMod.stdAddChar (dot (L w) y) =
      (m : ℂ) ^ 2 * ∑ x, (f x : ℂ) * g (L.symm x) := by
  have hterm : ∀ x w y, (f x : ℂ) * ZMod.stdAddChar (-dot x y) *
      ((g w : ℂ) * ZMod.stdAddChar (dot (L w) y)) =
      ((f x : ℂ) * g w) * ZMod.stdAddChar (dot (L w - x) y) := by
    intro x w y
    have : dot (L w - x) y = -dot x y + dot (L w) y := by simp only [dot]; simp; ring
    rw [this, AddChar.map_add_eq_mul]
    ring
  simp_rw [conj_FT, Finset.sum_mul, Finset.mul_sum, hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, orth, sub_eq_zero]
  rw [← L.symm.sum_comp]
  simp only [Equiv.apply_symm_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ x]
  simp only [Finset.mem_univ, if_true]
  ring

/-- `w ↦ T₁⁻¹ w - c e₁` and its inverse `x ↦ T₁ x + c e₁`. -/
def L1 (c : ZMod m) : (ZMod m × ZMod m) ≃ (ZMod m × ZMod m) where
  toFun w := (w.1 - 2 * w.2 - c, w.2)
  invFun x := (x.1 + (2 * x.2 + c), x.2)
  left_inv w := by ext <;> dsimp; ring
  right_inv x := by ext <;> dsimp; ring

/-- `w ↦ T₂⁻¹ w - c e₂` and its inverse `x ↦ T₂ x + c e₂`. -/
def L2 (c : ZMod m) : (ZMod m × ZMod m) ≃ (ZMod m × ZMod m) where
  toFun w := (w.1, w.2 - 2 * w.1 - c)
  invFun x := (x.1, x.2 + (2 * x.1 + c))
  left_inv w := by ext <;> dsimp; ring
  right_inv x := by ext <;> dsimp; ring

/-- Affine rule for `T₁`: `F(T₂⁻¹ y) ψ(-c y₁) = ∑_w f(w) ψ(⟨L1 c w, y⟩)`. -/
lemma shift1 (f : ZMod m × ZMod m → ℝ) (c : ZMod m) (y : ZMod m × ZMod m) :
    FT f (y.1, y.2 - 2 * y.1) * ZMod.stdAddChar (-(c * y.1)) =
      ∑ w, (f w : ℂ) * ZMod.stdAddChar (dot (L1 c w) y) := by
  unfold FT
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [dot, L1, Equiv.coe_fn_mk]
  ring

/-- Affine rule for `T₂`: `F(T₁⁻¹ y) ψ(-c y₂) = ∑_w f(w) ψ(⟨L2 c w, y⟩)`. -/
lemma shift2 (f : ZMod m × ZMod m → ℝ) (c : ZMod m) (y : ZMod m × ZMod m) :
    FT f (y.1 - 2 * y.2, y.2) * ZMod.stdAddChar (-(c * y.2)) =
      ∑ w, (f w : ℂ) * ZMod.stdAddChar (dot (L2 c w) y) := by
  unfold FT
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [dot, L2, Equiv.coe_fn_mk]
  ring

end MGGAred

open MGGAred in
theorem solution (m : ℕ) [NeZero m] (f : ZMod m × ZMod m → ℝ)
    (hf : ∑ z, f z = 0) :
    |∑ z, f z * (f (z.1 + 2 * z.2, z.2) + f (z.1 + (2 * z.2 + 1), z.2) +
        f (z.1, z.2 + 2 * z.1) + f (z.1, z.2 + (2 * z.1 + 1)))|
      ≤ 5 * Real.sqrt 2 / 2 * ∑ z, f z ^ 2 := by
  set SA := ∑ z, f z * (f (z.1 + 2 * z.2, z.2) + f (z.1 + (2 * z.2 + 1), z.2) +
        f (z.1, z.2 + 2 * z.1) + f (z.1, z.2 + (2 * z.1 + 1))) with hSA
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  -- F(0) = ∑ f = 0
  have hF0 : FT f 0 = 0 := by
    unfold FT
    simp only [dot, Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero, AddChar.map_zero_eq_one,
      mul_one]
    rw [← Complex.ofReal_sum, hf, Complex.ofReal_zero]
  have hB := mgg_fourier_inequality m (FT f) hF0
  -- child B's sum equals m² · SA
  have key : ∑ y, starRingEnd ℂ (FT f y) *
      (FT f (y.1, y.2 - 2 * y.1) * (1 + ZMod.stdAddChar (-y.1)) +
        FT f (y.1 - 2 * y.2, y.2) * (1 + ZMod.stdAddChar (-y.2))) = (m : ℂ) ^ 2 * (SA : ℂ) := by
    have hsplit : ∀ y : ZMod m × ZMod m, starRingEnd ℂ (FT f y) *
        (FT f (y.1, y.2 - 2 * y.1) * (1 + ZMod.stdAddChar (-y.1)) +
          FT f (y.1 - 2 * y.2, y.2) * (1 + ZMod.stdAddChar (-y.2))) =
        starRingEnd ℂ (FT f y) * (FT f (y.1, y.2 - 2 * y.1) * ZMod.stdAddChar (-(0 * y.1))) +
        starRingEnd ℂ (FT f y) * (FT f (y.1, y.2 - 2 * y.1) * ZMod.stdAddChar (-(1 * y.1))) +
        starRingEnd ℂ (FT f y) * (FT f (y.1 - 2 * y.2, y.2) * ZMod.stdAddChar (-(0 * y.2))) +
        starRingEnd ℂ (FT f y) * (FT f (y.1 - 2 * y.2, y.2) * ZMod.stdAddChar (-(1 * y.2))) := by
      intro y
      simp only [zero_mul, neg_zero, AddChar.map_zero_eq_one, one_mul]
      ring
    simp_rw [hsplit, shift1, shift2]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      parseval_twist, parseval_twist, parseval_twist, parseval_twist]
    rw [hSA]
    push_cast
    simp only [L1, L2, Equiv.coe_fn_symm_mk, add_zero]
    rw [← mul_add, ← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun z _ => ?_)
    ring
  -- Parseval: ∑ |F|² = m² ∑ f²
  have hpars : ∑ y, ‖FT f y‖ ^ 2 = (m : ℝ) ^ 2 * ∑ x, f x ^ 2 := by
    have h := parseval_twist f f (Equiv.refl _)
    have hl : ∀ y, starRingEnd ℂ (FT f y) * ∑ w, (f w : ℂ) *
        ZMod.stdAddChar (dot ((Equiv.refl (ZMod m × ZMod m)) w) y) = ((‖FT f y‖ ^ 2 : ℝ) : ℂ) := by
      intro y
      have : ∑ w, (f w : ℂ) * ZMod.stdAddChar (dot ((Equiv.refl (ZMod m × ZMod m)) w) y) =
          FT f y := rfl
      rw [this, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [hl] at h
    simp only [Equiv.refl_symm, Equiv.refl_apply] at h
    have h' : ((∑ y, ‖FT f y‖ ^ 2 : ℝ) : ℂ) = (((m : ℝ) ^ 2 * ∑ x, f x ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum, h]
      push_cast
      congr 1
      refine Finset.sum_congr rfl (fun x _ => by ring)
    exact_mod_cast h'
  rw [key, hpars, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs] at hB
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  nlinarith
