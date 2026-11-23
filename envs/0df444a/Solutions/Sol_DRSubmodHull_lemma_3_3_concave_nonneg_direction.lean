-- Prove2me | solution 1 for DRSubmodHull.lemma_3_3_concave_nonneg_direction
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:38:55.629518+00:00
-- url     : https://prove2.me/submissions/d672359c-44c7-4411-8933-6afd91bcaaf3

import Mathlib
import Definitions.Def_DRSubmodHull_IsDRSubmodularOn

set_option autoImplicit false

open DRSubmodHull

namespace DRSubmodHull.Lemma33Proof

def mask {V : Type*} [DecidableEq V] (S : Finset V) (d : V → ℝ) : V → ℝ :=
  fun j => if j ∈ S then d j else 0

theorem box_mem {V : Type*} [DecidableEq V] {a b z d : V → ℝ}
    (hz : z ∈ Set.Icc a b) (hd : 0 ≤ d) (hzd : z + d ∈ Set.Icc a b)
    (S : Finset V) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    z + s • mask S d ∈ Set.Icc a b := by
  constructor
  · intro j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mask]
    have hzj : a j ≤ z j := hz.1 j
    have hdj : 0 ≤ d j := hd j
    split_ifs <;> nlinarith
  · intro j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mask]
    have hzdj : z j + d j ≤ b j := hzd.2 j
    have hdj : 0 ≤ d j := hd j
    split_ifs <;> nlinarith

theorem update_add_single {V : Type*} [DecidableEq V] (x : V → ℝ) (i : V) (α : ℝ) :
    Function.update x i (x i + α) = x + Pi.single i α := by
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

end DRSubmodHull.Lemma33Proof

open DRSubmodHull.Lemma33Proof in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (a b : V → ℝ) (f : (V → ℝ) → ℝ)
    (hDR : IsDRSubmodularOn (Set.Icc a b) f) (hconc : IsCoordConcaveOn (Set.Icc a b) f)
    (z d : V → ℝ) (hz : z ∈ Set.Icc a b) (hd : 0 ≤ d) (hzd : z + d ∈ Set.Icc a b)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * (f (z + d) - f z) ≤ f (z + t • d) - f z := by
  have hmain : ∀ S : Finset V,
      t * (f (z + mask S d) - f z) ≤ f (z + t • mask S d) - f z := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have hm0 : mask (∅ : Finset V) d = 0 := by ext j; simp [mask]
      simp [hm0]
    | @insert i S hi ih =>
      let x : V → ℝ := z + t • mask S d
      let y : V → ℝ := z + mask S d
      have hx : x ∈ Set.Icc a b := box_mem hz hd hzd S ht0 ht1
      have hy : y ∈ Set.Icc a b := by
        simpa [y] using box_mem hz hd hzd S zero_le_one le_rfl
      have hxy : x ≤ y := by
        intro j
        simp only [x, y, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mask]
        have hdj : 0 ≤ d j := hd j
        split_ifs <;> nlinarith
      have hy_step : z + mask (insert i S) d = y + Pi.single i (d i) := by
        ext j
        by_cases h : j = i
        · subst h; simp [y, mask, hi]
        · simp [y, mask, h]
      have hx_tstep : z + t • mask (insert i S) d = x + Pi.single i (t * d i) := by
        ext j
        by_cases h : j = i
        · subst h; simp [x, mask, hi]
        · simp [x, mask, h]
      have hy_di : y + Pi.single i (d i) ∈ Set.Icc a b := by
        rw [← hy_step]
        simpa using box_mem hz hd hzd (insert i S) zero_le_one le_rfl
      have hx_di : x + Pi.single i (d i) ∈ Set.Icc a b := by
        constructor
        · intro j
          by_cases h : j = i
          · subst h
            simp only [x, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mask, if_neg hi,
              Pi.single_eq_same, mul_zero, add_zero]
            have hzj : a j ≤ z j := hz.1 j
            have hdj : 0 ≤ d j := hd j
            linarith
          · simp only [Pi.add_apply, Pi.single_eq_of_ne h, add_zero]
            exact hx.1 j
        · intro j
          by_cases h : j = i
          · subst h
            simp only [x, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mask, if_neg hi,
              Pi.single_eq_same, mul_zero, add_zero]
            exact hzd.2 j
          · simp only [Pi.add_apply, Pi.single_eq_of_ne h, add_zero]
            exact hx.2 j
      have hdr := hDR i x hx y hy hxy (d i) (hd i) hx_di hy_di
      have hdr_t : t * (f (y + Pi.single i (d i)) - f y) ≤
          t * (f (x + Pi.single i (d i)) - f x) :=
        mul_le_mul_of_nonneg_left hdr ht0
      have hr0 : x i ∈ {r : ℝ | Function.update x i r ∈ Set.Icc a b} := by
        simpa [Function.update_eq_self] using hx
      have hr1 : x i + d i ∈ {r : ℝ | Function.update x i r ∈ Set.Icc a b} := by
        simpa [update_add_single] using hx_di
      have hcc := (hconc x hx i).2 hr0 hr1 (sub_nonneg.mpr ht1) ht0 (sub_add_cancel 1 t)
      simp only [smul_eq_mul, Function.update_eq_self, update_add_single] at hcc
      have hcomb : (1 - t) * x i + t * (x i + d i) = x i + t * d i := by ring
      rw [hcomb, update_add_single] at hcc
      rw [hy_step, hx_tstep]
      change t * (f (y + Pi.single i (d i)) - f z) ≤ f (x + Pi.single i (t * d i)) - f z
      change t * (f y - f z) ≤ f x - f z at ih
      linarith
  have huniv : mask (Finset.univ : Finset V) d = d := by ext j; simp [mask]
  simpa [huniv] using hmain Finset.univ
