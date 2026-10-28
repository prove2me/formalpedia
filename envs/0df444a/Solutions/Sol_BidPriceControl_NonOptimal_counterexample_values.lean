-- Prove2me | solution 1 for BidPriceControl.NonOptimal.counterexample_values
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:48:12.063765+00:00
-- url     : https://prove2.me/submissions/6b57b72d-b9d0-4307-88f9-c8d2b46daa48

import Mathlib
import Definitions.Def_BidPriceControl_NonOptimal_Model
import Definitions.Def_BidPriceControl_NonOptimal_CounterExample

open MeasureTheory

namespace Aux_BidPriceControl_counterexample
open BidPriceControl.NonOptimal

theorem int2 (f : (Fin 3 → ℝ) → ℝ) (c1 c2 : ENNReal) (h1 : c1 ≠ ⊤) (h2 : c2 ≠ ⊤)
    (x1 x2 : Fin 3 → ℝ) :
    ∫ r, f r ∂(c1 • Measure.dirac x1 + c2 • Measure.dirac x2) =
      c1.toReal * f x1 + c2.toReal * f x2 := by
  have i1 : Integrable f (c1 • Measure.dirac x1) :=
    (integrable_dirac (by simp)).smul_measure h1
  have i2 : Integrable f (c2 • Measure.dirac x2) :=
    (integrable_dirac (by simp)).smul_measure h2
  rw [integral_add_measure i1 i2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  simp [smul_eq_mul]

theorem int3 (f : (Fin 3 → ℝ) → ℝ) (c1 c2 c3 : ENNReal) (h1 : c1 ≠ ⊤) (h2 : c2 ≠ ⊤)
    (h3 : c3 ≠ ⊤) (x1 x2 x3 : Fin 3 → ℝ) :
    ∫ r, f r ∂(c1 • Measure.dirac x1 + c2 • Measure.dirac x2 + c3 • Measure.dirac x3) =
      c1.toReal * f x1 + c2.toReal * f x2 + c3.toReal * f x3 := by
  have i1 : Integrable f (c1 • Measure.dirac x1) :=
    (integrable_dirac (by simp)).smul_measure h1
  have i2 : Integrable f (c2 • Measure.dirac x2) :=
    (integrable_dirac (by simp)).smul_measure h2
  have i3 : Integrable f (c3 • Measure.dirac x3) :=
    (integrable_dirac (by simp)).smul_measure h3
  rw [integral_add_measure (i1.add_measure i2) i3, integral_add_measure i1 i2,
    integral_smul_measure, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, integral_dirac]
  simp [smul_eq_mul]

theorem fold_eq {s : Finset (Fin 3)} {b v : ℝ} {f : Fin 3 → ℝ}
    (hb : b ≤ v) (hf : ∀ x ∈ s, f x ≤ v) (hv : v ≤ b ∨ ∃ x ∈ s, v ≤ f x) :
    s.fold max b f = v :=
  le_antisymm ((Finset.fold_max_le v).mpr ⟨hb, hf⟩) ((Finset.le_fold_max v).mpr hv)

end Aux_BidPriceControl_counterexample

open BidPriceControl.NonOptimal Aux_BidPriceControl_counterexample in
theorem solution :
    optValue ceA ceLaw 1 ![1, 1] = 400 ∧ optValue ceA ceLaw 1 ![1, 0] = 0 ∧
    optValue ceA ceLaw 1 ![0, 1] = 0 ∧ optValue ceA ceLaw 1 ![0, 0] = 0 ∧
    optValue ceA ceLaw 2 ceX = 440 := by
  have hV0 : ∀ y, optValue ceA ceLaw 0 y = 0 := fun y => rfl
  have hlaw1 : ceLaw 1 = (4 / 5 : ENNReal) • Measure.dirac ![500, 0, 0] +
      (1 / 5 : ENNReal) • Measure.dirac ![0, 0, 0] := rfl
  have hlaw2 : ceLaw 2 = (2 / 5 : ENNReal) • Measure.dirac ![500, 0, 0] +
      (3 / 10 : ENNReal) • Measure.dirac ![0, 250, 0] +
      (3 / 10 : ENNReal) • Measure.dirac ![0, 0, 250] := rfl
  have hV1 : ∀ y, optValue ceA ceLaw 1 y = ∫ r, (Finset.univ.filter (fun j => Fits ceA y j)).fold
      max 0 (fun j => r j + 0) ∂(ceLaw 1) := by
    intro y
    rw [optValue]
    simp only [hV0]
  have hf11 : (Finset.univ.filter (fun j => Fits ceA ![1, 1] j)) = Finset.univ := by decide
  have hf10 : (Finset.univ.filter (fun j => Fits ceA ![1, 0] j)) = {1} := by decide
  have hf01 : (Finset.univ.filter (fun j => Fits ceA ![0, 1] j)) = {2} := by decide
  have hf00 : (Finset.univ.filter (fun j => Fits ceA ![0, 0] j)) = ∅ := by decide
  have ne1 : (4 / 5 : ENNReal) ≠ ⊤ := ENNReal.div_ne_top (by simp) (by simp)
  have ne2 : (1 / 5 : ENNReal) ≠ ⊤ := ENNReal.div_ne_top (by simp) (by simp)
  have t1 : (4 / 5 : ENNReal).toReal = 4 / 5 := by rw [ENNReal.toReal_div]; norm_num
  have t2 : (1 / 5 : ENNReal).toReal = 1 / 5 := by rw [ENNReal.toReal_div]; norm_num
  have A1 : optValue ceA ceLaw 1 ![1, 1] = 400 := by
    rw [hV1, hf11, hlaw1, int2 _ _ _ ne1 ne2, t1, t2]
    rw [fold_eq (v := 500) (by norm_num) (by intro x _; fin_cases x <;> simp)
        (Or.inr ⟨0, Finset.mem_univ _, by simp⟩)]
    rw [fold_eq (v := 0) le_rfl (by intro x _; fin_cases x <;> simp) (Or.inl le_rfl)]
    norm_num
  have A2 : optValue ceA ceLaw 1 ![1, 0] = 0 := by
    rw [hV1, hf10, hlaw1, int2 _ _ _ ne1 ne2]
    rw [fold_eq (v := 0) le_rfl (by intro x hx; rw [Finset.mem_singleton] at hx; subst hx; simp)
        (Or.inl le_rfl)]
    rw [fold_eq (v := 0) le_rfl (by intro x hx; rw [Finset.mem_singleton] at hx; subst hx; simp)
        (Or.inl le_rfl)]
    norm_num
  have A3 : optValue ceA ceLaw 1 ![0, 1] = 0 := by
    rw [hV1, hf01, hlaw1, int2 _ _ _ ne1 ne2]
    rw [fold_eq (v := 0) le_rfl (by intro x hx; rw [Finset.mem_singleton] at hx; subst hx; simp)
        (Or.inl le_rfl)]
    rw [fold_eq (v := 0) le_rfl (by intro x hx; rw [Finset.mem_singleton] at hx; subst hx; simp)
        (Or.inl le_rfl)]
    norm_num
  have A4 : optValue ceA ceLaw 1 ![0, 0] = 0 := by
    rw [hV1, hf00, hlaw1, int2 _ _ _ ne1 ne2]
    simp
  refine ⟨A1, A2, A3, A4, ?_⟩
  have hc0 : ceX - column ceA 0 = ![0, 0] := by decide
  have hc1 : ceX - column ceA 1 = ![0, 1] := by decide
  have hc2 : ceX - column ceA 2 = ![1, 0] := by decide
  have hceX : ceX = ![1, 1] := rfl
  have hfX : (Finset.univ.filter (fun j => Fits ceA ceX j)) = Finset.univ := by decide
  have hV2 : optValue ceA ceLaw 2 ceX = ∫ r, (Finset.univ.filter (fun j => Fits ceA ceX j)).fold
      max (optValue ceA ceLaw 1 ceX) (fun j => r j + optValue ceA ceLaw 1 (ceX - column ceA j))
      ∂(ceLaw 2) := by
    rw [optValue]
  have hfun : ∀ j : Fin 3, optValue ceA ceLaw 1 (ceX - column ceA j) = 0 := by
    intro j; fin_cases j
    · show optValue ceA ceLaw 1 (ceX - column ceA 0) = 0; rw [hc0, A4]
    · show optValue ceA ceLaw 1 (ceX - column ceA 1) = 0; rw [hc1, A3]
    · show optValue ceA ceLaw 1 (ceX - column ceA 2) = 0; rw [hc2, A2]
  rw [hV2, hfX, hlaw2]
  have A1' : optValue ceA ceLaw 1 ceX = 400 := A1
  simp only [hfun, add_zero]
  rw [A1']
  have n1 : (2 / 5 : ENNReal) ≠ ⊤ := ENNReal.div_ne_top (by simp) (by simp)
  have n2 : (3 / 10 : ENNReal) ≠ ⊤ := ENNReal.div_ne_top (by simp) (by simp)
  rw [int3 _ _ _ _ n1 n2 n2]
  rw [fold_eq (v := 500) (by norm_num) (by intro x _; fin_cases x <;> simp)
      (Or.inr ⟨0, Finset.mem_univ _, by simp⟩)]
  rw [fold_eq (v := 400) le_rfl (by intro x _; fin_cases x <;> simp <;> norm_num) (Or.inl le_rfl)]
  rw [fold_eq (v := 400) le_rfl (by intro x _; fin_cases x <;> simp <;> norm_num) (Or.inl le_rfl)]
  have u1 : (2 / 5 : ENNReal).toReal = 2 / 5 := by rw [ENNReal.toReal_div]; norm_num
  have u2 : (3 / 10 : ENNReal).toReal = 3 / 10 := by rw [ENNReal.toReal_div]; norm_num
  rw [u1, u2]
  norm_num
