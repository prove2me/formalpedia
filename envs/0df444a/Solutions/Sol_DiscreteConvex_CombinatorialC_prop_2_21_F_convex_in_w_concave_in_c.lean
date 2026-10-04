-- Prove2me | solution 1 for DiscreteConvex.CombinatorialC.prop_2_21_F_convex_in_w_concave_in_c
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T01:07:52.781771+00:00
-- url     : https://prove2.me/submissions/e17622ff-7464-4ae7-94cc-a04e5a2c53ba

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_FVal

set_option autoImplicit false

namespace D51a1bfcAux

open DiscreteConvex.CombinatorialC

theorem boundary_comb {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] (src dst : A → V)
    (a b : ℝ) (x y : A → ℝ) (v : V) :
    Boundary src dst (a • x + b • y) v = a * Boundary src dst x v + b * Boundary src dst y v := by
  unfold Boundary
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem feas_comb {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] (src dst : A → V)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (c1 c2 x y : A → ℝ)
    (hx : IsFeasibleCirc src dst c1 x) (hy : IsFeasibleCirc src dst c2 y) :
    IsFeasibleCirc src dst (a • c1 + b • c2) (a • x + b • y) := by
  refine ⟨fun e => ?_, fun v => ?_⟩
  · obtain ⟨h1, h2⟩ := hx.1 e
    obtain ⟨h3, h4⟩ := hy.1 e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · positivity
    · nlinarith [mul_le_mul_of_nonneg_left h2 ha, mul_le_mul_of_nonneg_left h4 hb]
  · rw [boundary_comb, hx.2 v, hy.2 v]; ring

theorem bdd {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] (src dst : A → V)
    (w c : A → ℝ) :
    BddAbove {t : ℝ | ∃ xi : A → ℝ, IsFeasibleCirc src dst c xi ∧ t = dotProduct w xi} := by
  refine ⟨∑ e, |w e| * |c e|, ?_⟩
  rintro t ⟨xi, hxi, rfl⟩
  unfold dotProduct
  refine Finset.sum_le_sum fun e _ => ?_
  obtain ⟨h1, h2⟩ := hxi.1 e
  calc w e * xi e ≤ |w e * xi e| := le_abs_self _
    _ = |w e| * |xi e| := abs_mul _ _
    _ ≤ |w e| * |c e| := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2

theorem nonempty {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] (src dst : A → V)
    (w c : A → ℝ) (hc : 0 ≤ c) :
    {t : ℝ | ∃ xi : A → ℝ, IsFeasibleCirc src dst c xi ∧ t = dotProduct w xi}.Nonempty := by
  refine ⟨0, 0, ⟨fun e => ⟨le_refl _, hc e⟩, fun v => ?_⟩, by simp⟩
  simp [Boundary]

theorem le_F {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] (src dst : A → V)
    (w c xi : A → ℝ) (h : IsFeasibleCirc src dst c xi) :
    dotProduct w xi ≤ FVal src dst w c :=
  le_csSup (bdd src dst w c) ⟨xi, h, rfl⟩

theorem aux_sup {S1 S2 : Set ℝ} {M a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : S1.Nonempty) (h2 : S2.Nonempty) (hb1 : BddAbove S1) (hb2 : BddAbove S2)
    (h : ∀ x ∈ S1, ∀ y ∈ S2, a * x + b * y ≤ M) : a * sSup S1 + b * sSup S2 ≤ M := by
  have e1 := Real.sSup_smul_of_nonneg ha S1
  have e2 := Real.sSup_smul_of_nonneg hb S2
  simp only [smul_eq_mul] at e1 e2
  rw [← e1, ← e2, ← csSup_add (h1.smul_set) (hb1.smul_of_nonneg ha) (h2.smul_set)
    (hb2.smul_of_nonneg hb)]
  apply csSup_le (h1.smul_set.add h2.smul_set)
  rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
  simpa [smul_eq_mul] using h x hx y hy

end D51a1bfcAux

open DiscreteConvex.CombinatorialC in
theorem solution {V A : Type*} [Fintype A] [Fintype V]
    [DecidableEq V] (src dst : A → V) :
    (∀ c0 : A → ℝ, 0 ≤ c0 → ConvexOn ℝ Set.univ (fun w => FVal src dst w c0)) ∧
      (∀ w0 : A → ℝ, ConcaveOn ℝ {c : A → ℝ | 0 ≤ c} (fun c => FVal src dst w0 c)) := by
  refine ⟨fun c0 hc0 => ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩,
    fun w0 => ⟨?_, fun x hx y hy a b ha hb _ => ?_⟩⟩
  · simp only [smul_eq_mul]
    apply csSup_le (D51a1bfcAux.nonempty src dst _ c0 hc0)
    rintro t ⟨xi, hxi, rfl⟩
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    have h1 := D51a1bfcAux.le_F src dst x c0 xi hxi
    have h2 := D51a1bfcAux.le_F src dst y c0 xi hxi
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  · intro p hp q hq a b ha hb _ e
    have h1 : (0:ℝ) ≤ p e := hp e
    have h2 : (0:ℝ) ≤ q e := hq e
    show (0:ℝ) ≤ a * p e + b * q e
    exact add_nonneg (mul_nonneg ha h1) (mul_nonneg hb h2)
  · simp only [smul_eq_mul]
    apply D51a1bfcAux.aux_sup ha hb (D51a1bfcAux.nonempty src dst w0 x hx) (D51a1bfcAux.nonempty src dst w0 y hy)
      (D51a1bfcAux.bdd src dst w0 x) (D51a1bfcAux.bdd src dst w0 y)
    rintro _ ⟨xi1, h1, rfl⟩ _ ⟨xi2, h2, rfl⟩
    have := D51a1bfcAux.le_F src dst w0 _ _ (D51a1bfcAux.feas_comb src dst a b ha hb x y xi1 xi2 h1 h2)
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
    exact this
