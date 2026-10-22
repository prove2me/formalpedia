-- Prove2me | solution 1 for CurvatureSubmod.LocalSearch.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:23:50.690246+00:00
-- url     : https://prove2.me/submissions/b915316d-afda-4071-a4f7-94a8efc80f0b

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_CurvatureSubmod_LocalSearch_Setting

set_option autoImplicit false

open CurvatureSubmod.LocalSearch

lemma csls2_subadd {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hsub : NonmonotoneSubmod.Shared.Submodular f) (hempty : f ∅ = 0) (A : Finset X) :
    f A ≤ ∑ j ∈ A, f {j} := by
  induction A using Finset.induction_on with
  | empty => simp [hempty]
  | insert a A ha ih =>
    have h := hsub {a} A
    have e1 : ({a} : Finset X) ∪ A = insert a A := by
      ext x; simp [or_comm]
    have e2 : ({a} : Finset X) ∩ A = ∅ := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      intro hx hxA; exact ha (hx ▸ hxA)
    rw [e1, e2, hempty] at h
    rw [Finset.sum_insert ha]
    linarith

theorem solution {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hmono : MonoInc f) (hsub : NonmonotoneSubmod.Shared.Submodular f)
    (c : ℝ) (hcurv : CurvAtMostInc f c) (hempty : f ∅ = 0) (A : Finset X) :
    (1 - c) * f A ≤ ∑ j ∈ A, marg f (Finset.univ.erase j) j := by
  rcases le_or_gt 0 (1 - c) with hc | hc
  · have h1 := csls2_subadd f hsub hempty A
    calc (1 - c) * f A ≤ (1 - c) * ∑ j ∈ A, f {j} := mul_le_mul_of_nonneg_left h1 hc
      _ = ∑ j ∈ A, (1 - c) * marg f ∅ j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          unfold marg
          simp [hempty]
      _ ≤ _ := Finset.sum_le_sum fun j _ => hcurv j
  · calc (1 - c) * f A ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc.le (hf0 A)
      _ ≤ _ := Finset.sum_nonneg fun j _ => hmono _ j
