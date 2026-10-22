-- Prove2me | solution 1 for FrieszDUE.PIE.ess_inf_lower_bound_17
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:35:34.053351+00:00
-- url     : https://prove2.me/submissions/333060ac-0eda-4eed-8be9-d3313b76a97e

import Mathlib
import Definitions.Def_FrieszDUE_PIE_Setting

set_option autoImplicit false
open MeasureTheory FrieszDUE.PIE

lemma fdp_bdd (T : ℝ) (hT : 0 < T) (F : ℝ → ℝ) :
    BddAbove {x : ℝ | ν T {t | F t < x} = 0} := by
  by_contra hb
  have h0 : ∀ n : ℕ, ν T {t | F t < n} = 0 := by
    intro n
    rw [not_bddAbove_iff] at hb
    obtain ⟨x, hx, hnx⟩ := hb n
    exact measure_mono_null (fun t ht => lt_trans ht hnx) hx
  have hU : (Set.univ : Set ℝ) = ⋃ n : ℕ, {t | F t < n} := by
    ext t
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
    exact exists_nat_gt (F t)
  have h1 : ν T Set.univ = 0 := by
    rw [hU]
    exact measure_iUnion_null h0
  rw [Measure.restrict_apply_univ, Real.volume_Icc] at h1
  have := ENNReal.ofReal_eq_zero.mp h1
  linarith

lemma fdp_zero_mem (T : ℝ) (F : ℝ → ℝ) (hF : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ F t) :
    (0 : ℝ) ∈ {x : ℝ | ν T {t | F t < x} = 0} := by
  show ν T {t | F t < 0} = 0
  rw [Measure.restrict_apply' measurableSet_Icc]
  have : {t | F t < 0} ∩ Set.Icc (0 : ℝ) T = ∅ := by
    ext t
    constructor
    · rintro ⟨h, ht⟩
      exact absurd (hF t ht) (not_le.mpr h)
    · intro h
      exact absurd h (by simp)
  rw [this]
  simp

lemma fdp_nonneg (T : ℝ) (hT : 0 < T) (F : ℝ → ℝ) (hF : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ F t) :
    0 ≤ essInfOn T F :=
  le_csSup (fdp_bdd T hT F) (fdp_zero_mem T F hF)

lemma fdp_ae (T : ℝ) (hT : 0 < T) (F : ℝ → ℝ) (hF : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ F t) :
    ∀ᵐ t ∂(ν T), essInfOn T F ≤ F t := by
  have hne : ({x : ℝ | ν T {t | F t < x} = 0}).Nonempty := ⟨0, fdp_zero_mem T F hF⟩
  rw [ae_iff]
  have hset : {t | ¬ essInfOn T F ≤ F t} = ⋃ n : ℕ, {t | F t < essInfOn T F - 1 / ((n : ℝ) + 1)} := by
    ext t
    simp only [not_le, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  rw [hset]
  refine measure_iUnion_null fun n => ?_
  have hlt : essInfOn T F - 1 / ((n : ℝ) + 1) < essInfOn T F := by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  obtain ⟨b, hb, hlb⟩ := exists_lt_of_lt_csSup hne hlt
  exact measure_mono_null (fun t ht => lt_trans ht hlb) hb

theorem solution {P W : Type*}
    (T : ℝ) (hT : 0 < T) (od : P → W) (C : P → ℝ → (P → ℝ → ℝ) → ℝ)
    (h : P → ℝ → ℝ)
    (hC_nonneg : ∀ p, ∀ t ∈ Set.Icc 0 T, 0 ≤ C p t h)
    (hC_meas : ∀ p, AEMeasurable (fun t => C p t h) (ν T)) (p : P) :
    ∀ᵐ t ∂(ν T), muPath T C h p ≤ C p t h ∧ muOD T od C h (od p) ≤ muPath T C h p := by
  have hconst : muOD T od C h (od p) ≤ muPath T C h p := by
    unfold muOD
    refine ciInf_le ?_ (⟨p, rfl⟩ : {q : P // od q = od p})
    refine ⟨0, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact fdp_nonneg T hT _ (hC_nonneg q.1)
  filter_upwards [fdp_ae T hT (fun t => C p t h) (hC_nonneg p)] with t ht
  exact ⟨ht, hconst⟩
