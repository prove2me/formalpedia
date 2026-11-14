-- Prove2me | solution 1 for GenCountSampleLLL.insertion_return_probability_unit_interval
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:59:48.821744+00:00
-- url     : https://prove2.me/submissions/6495763e-2574-4056-b0d0-fb4af813828c

import Definitions.Def_GenCountSampleLLL_insertionChain
import Theorems.Thm_GenCountSampleLLL_lemma_6_3_pin_support
noncomputable section
open scoped Classical BigOperators ENNReal
open GenCountSampleLLL

theorem solution (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (z : I.Assign)
    (hT : T ∈ I.twoTrees D a) (hz : z ∈ I.labelsE D a T) :
    0 ≤ I.retProb D a (T,z) ∧ I.retProb D a (T,z) ≤ 1 := by
  have hnonempty (ω : I.ExpSpace) : 0 < (I.Le D a (T,z) ω).card := by
    apply Finset.card_pos.mpr
    exact ⟨(T,z), ((lemma_6_3_pin_support I D a T z hT hz).1 ω).2⟩
  have hsum : ∑ ω : I.ExpSpace, (I.expLaw ω).toReal = 1 := by
    rw [← ENNReal.toReal_sum (by intro ω hω; exact I.expLaw.apply_ne_top ω)]
    have h := I.expLaw.tsum_coe
    rw [tsum_fintype] at h
    rw [h]
    simp
  unfold Inst.retProb
  constructor
  · apply Finset.sum_nonneg
    intro ω hω
    exact div_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)
  · calc
      _ ≤ ∑ ω : I.ExpSpace, (I.expLaw ω).toReal := by
        apply Finset.sum_le_sum
        intro ω hω
        apply div_le_self ENNReal.toReal_nonneg
        exact_mod_cast hnonempty ω
      _ = 1 := hsum

