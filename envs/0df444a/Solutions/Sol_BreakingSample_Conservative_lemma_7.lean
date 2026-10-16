-- Prove2me | solution 1 for BreakingSample.Conservative.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T06:08:28.610904+00:00
-- url     : https://prove2.me/submissions/0315e3ef-2d36-42c3-b6ac-7caca75bbb88

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_BreakingSample_Conservative_Rule
import Theorems.Thm_FoundationsML_ReinforcementLearning_bellman_equations

open FoundationsML.ReinforcementLearning BreakingSample.Perturbed
open BreakingSample.Conservative

-- Formalization contribution: Alexander Richard Towell (queelius), with Codex assistance.
-- Paper: Gen Li, Yuting Wei, Yuejie Chi and Yuxin Chen, arXiv:2005.12900v8, Lemma 7.
-- Uses Nickrobbins95's accepted proof of the policy Bellman equation.
set_option autoImplicit false

theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [LinearOrder A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsDiscountedMDP P r γ)
    (ξ ς : ℝ) (hς : ς ≤ ξ) (πc : S → A)
    (hc : IsConservative (optQ P r γ) (optValue P r γ) ς πc) (π : S → A) :
    ∀ s, value P r γ π s - value P r γ πc s ≤ ξ / (1 - γ) := by
  classical
  haveI : Nonempty S := hM.2.2.2.2.1
  have hγ0 : 0 ≤ γ := hM.2.2.1.le
  have hγ1 : γ < 1 := hM.2.2.2.1
  have hpol : IsPolicy (detPolicy πc) := by
    intro s
    constructor
    · intro a
      simp only [detPolicy]
      split_ifs <;> norm_num
    · simp [detPolicy]
  have hb (s : S) : value P r γ πc s =
      r s (πc s) + γ * ∑ t, P s (πc s) t * value P r γ πc t := by
    simpa [value, InducedReward, InducedTransition, detPolicy] using
      bellman_equations (detPolicy πc) hpol P hM.1 r γ hγ0 hγ1 s
  let d : S → ℝ := fun s => optValue P r γ s - value P r γ πc s
  obtain ⟨s0, _, hmax⟩ := Finset.exists_max_image Finset.univ d Finset.univ_nonempty
  have hsum : (∑ t, P s0 (πc s0) t * d t) ≤ d s0 := by
    calc
      _ ≤ ∑ t, P s0 (πc s0) t * d s0 :=
        Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left
          (hmax t (Finset.mem_univ t)) ((hM.1 s0 (πc s0)).1 t))
      _ = d s0 := by rw [← Finset.sum_mul, (hM.1 s0 (πc s0)).2, one_mul]
  have hgap : d s0 ≤ ξ + γ * ∑ t, P s0 (πc s0) t * d t := by
    have hcons := (hc s0).1
    have hbell := hb s0
    simp only [optQ] at hcons
    dsimp [d]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    linarith
  have hbound : d s0 ≤ ξ / (1 - γ) := by
    apply (le_div_iff₀ (sub_pos.mpr hγ1)).2
    have hmul := mul_le_mul_of_nonneg_left hsum hγ0
    nlinarith
  intro s
  have hv : value P r γ π s ≤ optValue P r γ s :=
    Finset.le_sup' (fun π' : S → A => value P r γ π' s) (Finset.mem_univ π)
  have hm := hmax s (Finset.mem_univ s)
  dsimp [d] at hm hbound
  linarith
