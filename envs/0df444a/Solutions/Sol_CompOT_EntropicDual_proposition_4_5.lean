-- Prove2me | solution 1 for CompOT.EntropicDual.proposition_4_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:35:27.142439+00:00
-- url     : https://prove2.me/submissions/c2b91184-575c-4a8e-b00c-9e479e6cc94c

import Mathlib
import Definitions.Def_CompOT_EntropicDual_Defs

set_option autoImplicit false
open CompOT.EntropicDual

theorem grad_aux {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
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


theorem solution {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hε : 0 < ε)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (f : Fin n → ℝ) (g : Fin m → ℝ)
    (hmax : ∀ f' g', dualObjEnt C a b ε f' g' ≤ dualObjEnt C a b ε f g) :
    KantorovichFeasible C f g ∧
      (∑ i, f i * a i) + (∑ j, g j * b j) ≤ unregCost C a b := by
  obtain ⟨hgf, hgg⟩ := grad_aux C a b ε hn hm hε ha hb f g
  have hfa : ∀ i, a i = Real.exp (f i / ε) * ∑ j, gibbs C ε i j * Real.exp (g j / ε) := by
    intro i
    have hloc : IsLocalMax (fun t : ℝ => dualObjEnt C a b ε (Function.update f i t) g) (f i) := by
      refine Filter.Eventually.of_forall (fun t => ?_)
      show dualObjEnt C a b ε (Function.update f i t) g ≤ dualObjEnt C a b ε (Function.update f i (f i)) g
      rw [Function.update_eq_self]; exact hmax _ _
    have := hloc.hasDerivAt_eq_zero (hgf i)
    linarith
  have hgb : ∀ j, b j = Real.exp (g j / ε) * ∑ i, gibbs C ε i j * Real.exp (f i / ε) := by
    intro j
    have hloc : IsLocalMax (fun t : ℝ => dualObjEnt C a b ε f (Function.update g j t)) (g j) := by
      refine Filter.Eventually.of_forall (fun t => ?_)
      show dualObjEnt C a b ε f (Function.update g j t) ≤ dualObjEnt C a b ε f (Function.update g j (g j))
      rw [Function.update_eq_self]; exact hmax _ _
    have := hloc.hasDerivAt_eq_zero (hgg j)
    linarith
  set P : Matrix (Fin n) (Fin m) ℝ :=
    fun i j => Real.exp (f i / ε) * gibbs C ε i j * Real.exp (g j / ε) with hP
  have hPnn : ∀ i j, 0 ≤ P i j := fun i j => by
    simp only [hP, gibbs]; positivity
  have hrow : ∀ i, ∑ j, P i j = a i := by
    intro i
    rw [hfa i, Finset.mul_sum]
    apply Finset.sum_congr rfl; intros; simp only [hP]; ring
  have hcol : ∀ j, ∑ i, P i j = b j := by
    intro j
    rw [hgb j, Finset.mul_sum]
    apply Finset.sum_congr rfl; intros; simp only [hP]; ring
  have hPmem : P ∈ CompOT.Assignment.couplings a b := ⟨hPnn, hrow, hcol⟩
  have ha1 : ∀ i, a i ≤ 1 := by
    intro i
    have := Finset.single_le_sum (f := a) (fun k _ => ha.1 k) (Finset.mem_univ i)
    rw [ha.2] at this; exact this
  have hfeas : KantorovichFeasible C f g := by
    intro i j
    have h1 : P i j ≤ a i := by
      rw [← hrow i]
      exact Finset.single_le_sum (f := fun j => P i j) (fun k _ => hPnn i k) (Finset.mem_univ j)
    have h2 : P i j = Real.exp ((f i + g j - C i j) / ε) := by
      simp only [hP, gibbs]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    have h3 : Real.exp ((f i + g j - C i j) / ε) ≤ 1 := by rw [← h2]; linarith [ha1 i]
    have h4 : (f i + g j - C i j) / ε ≤ 0 := Real.exp_le_one_iff.1 h3
    have h5 : f i + g j - C i j ≤ 0 := by
      by_contra hc
      push_neg at hc
      have : 0 < (f i + g j - C i j) / ε := div_pos hc hε
      linarith
    linarith
  refine ⟨hfeas, ?_⟩
  haveI : Nonempty (CompOT.Assignment.couplings a b) := ⟨⟨P, hPmem⟩⟩
  unfold unregCost
  apply le_ciInf
  intro Q
  obtain ⟨hQnn, hQrow, hQcol⟩ := Q.2
  unfold CompOT.Assignment.frob
  have e1 : ∑ i, f i * a i = ∑ i, ∑ j, f i * Q.1 i j := by
    apply Finset.sum_congr rfl; intro i _
    rw [← hQrow i, Finset.mul_sum]
  have e2 : ∑ j, g j * b j = ∑ i, ∑ j, g j * Q.1 i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [← hQcol j, Finset.mul_sum]
  rw [e1, e2, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro j _
  have := hfeas i j
  nlinarith [hQnn i j]
