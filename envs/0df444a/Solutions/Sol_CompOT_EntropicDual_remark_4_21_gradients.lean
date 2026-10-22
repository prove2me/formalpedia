-- Prove2me | solution 1 for CompOT.EntropicDual.remark_4_21_gradients
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:35:17.77599+00:00
-- url     : https://prove2.me/submissions/8176b0ce-a900-430f-9454-8cc240d723a8

import Mathlib
import Definitions.Def_CompOT_EntropicDual_Defs

set_option autoImplicit false
open CompOT.EntropicDual

theorem solution {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hε : 0 < ε)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (f : Fin n → ℝ) (g : Fin m → ℝ) :
    (∀ i, HasDerivAt
      (fun t : ℝ => dualObjEnt C a b ε (Function.update f i t) g)
      (a i - Real.exp (f i / ε) *
        ∑ j, gibbs C ε i j * Real.exp (g j / ε)) (f i)) ∧
    (∀ j, HasDerivAt
      (fun t : ℝ => dualObjEnt C a b ε f (Function.update g j t))
      (b j - Real.exp (g j / ε) *
        ∑ i, gibbs C ε i j * Real.exp (f i / ε)) (g j)) := by
  have hexp : ∀ (x : ℝ), HasDerivAt (fun t : ℝ => Real.exp (t / ε)) (Real.exp (x / ε) * (1 / ε)) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => t / ε) (1 / ε) x := (hasDerivAt_id x).div_const ε
    exact (Real.hasDerivAt_exp (x / ε)).comp x h1
  constructor
  · intro i
    have hfun : (fun t : ℝ => dualObjEnt C a b ε (Function.update f i t) g) =
        fun t => (t * a i + ∑ i' ∈ Finset.univ.erase i, f i' * a i') + ∑ j, g j * b j
          - ε * (Real.exp (t / ε) * (∑ j, gibbs C ε i j * Real.exp (g j / ε)) +
            ∑ i' ∈ Finset.univ.erase i, ∑ j, Real.exp (f i' / ε) * gibbs C ε i' j * Real.exp (g j / ε)) := by
      funext t
      unfold dualObjEnt
      have e1 : ∑ i', Function.update f i t i' * a i' =
          t * a i + ∑ i' ∈ Finset.univ.erase i, f i' * a i' := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        congr 1
        · simp
        · apply Finset.sum_congr rfl
          intro i' hi'
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi')]
      have e2 : ∑ i', ∑ j, Real.exp (Function.update f i t i' / ε) * gibbs C ε i' j * Real.exp (g j / ε) =
          Real.exp (t / ε) * (∑ j, gibbs C ε i j * Real.exp (g j / ε)) +
            ∑ i' ∈ Finset.univ.erase i, ∑ j, Real.exp (f i' / ε) * gibbs C ε i' j * Real.exp (g j / ε) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        congr 1
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          simp [mul_assoc]
        · apply Finset.sum_congr rfl
          intro i' hi'
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi')]
      rw [e1, e2]
    rw [hfun]
    have h := ((((hasDerivAt_id (f i)).mul_const (a i)).add_const (∑ i' ∈ Finset.univ.erase i, f i' * a i')).add_const
      (∑ j, g j * b j)).sub
      ((((hexp (f i)).mul_const (∑ j, gibbs C ε i j * Real.exp (g j / ε))).add_const
        (∑ i' ∈ Finset.univ.erase i, ∑ j, Real.exp (f i' / ε) * gibbs C ε i' j * Real.exp (g j / ε))).const_mul ε)
    refine h.congr_deriv ?_
    field_simp
  · intro j
    have hfun : (fun t : ℝ => dualObjEnt C a b ε f (Function.update g j t)) =
        fun t => (∑ i, f i * a i) + (t * b j + ∑ j' ∈ Finset.univ.erase j, g j' * b j')
          - ε * (Real.exp (t / ε) * (∑ i, gibbs C ε i j * Real.exp (f i / ε)) +
            ∑ j' ∈ Finset.univ.erase j, ∑ i, Real.exp (f i / ε) * gibbs C ε i j' * Real.exp (g j' / ε)) := by
      funext t
      unfold dualObjEnt
      have e1 : ∑ j', Function.update g j t j' * b j' =
          t * b j + ∑ j' ∈ Finset.univ.erase j, g j' * b j' := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        congr 1
        · simp
        · apply Finset.sum_congr rfl
          intro j' hj'
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hj')]
      have e2 : ∑ i, ∑ j', Real.exp (f i / ε) * gibbs C ε i j' * Real.exp (Function.update g j t j' / ε) =
          Real.exp (t / ε) * (∑ i, gibbs C ε i j * Real.exp (f i / ε)) +
            ∑ j' ∈ Finset.univ.erase j, ∑ i, Real.exp (f i / ε) * gibbs C ε i j' * Real.exp (g j' / ε) := by
        rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        congr 1
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          simp only [Function.update_self]
          ring
        · apply Finset.sum_congr rfl
          intro j' hj'
          apply Finset.sum_congr rfl
          intro i _
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hj')]
      rw [e1, e2]
    rw [hfun]
    have h := (((hasDerivAt_id (g j)).mul_const (b j)).add_const (∑ j' ∈ Finset.univ.erase j, g j' * b j')).const_add
      (∑ i, f i * a i) |>.sub
      ((((hexp (g j)).mul_const (∑ i, gibbs C ε i j * Real.exp (f i / ε))).add_const
        (∑ j' ∈ Finset.univ.erase j, ∑ i, Real.exp (f i / ε) * gibbs C ε i j' * Real.exp (g j' / ε))).const_mul ε)
    refine h.congr_deriv ?_
    field_simp
