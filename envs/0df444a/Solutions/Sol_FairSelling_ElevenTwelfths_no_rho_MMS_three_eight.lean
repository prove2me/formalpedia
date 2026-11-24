-- Prove2me | solution 1 for FairSelling.ElevenTwelfths.no_rho_MMS_three_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:22:15.723705+00:00
-- url     : https://prove2.me/submissions/4e1cfcca-eb9c-4427-ae93-f9894cdf6351

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_FeigeNorkin
import Definitions.Def_RequestProject_ElevenTwelfths
import Theorems.Thm_FairSelling_ElevenTwelfths_cast_sum_eq
import Theorems.Thm_FairSelling_ElevenTwelfths_MMS_agent_zero
import Theorems.Thm_FairSelling_ElevenTwelfths_MMS_agent_one
import Theorems.Thm_FairSelling_ElevenTwelfths_MMS_agent_two
import Theorems.Thm_FairSelling_FeigeNorkin_feigeNorkin_disjoint
import Theorems.Thm_FairSelling_FeigeNorkin_fnU_total
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ElevenTwelfths
open FeigeNorkin
namespace FairSelling.ElevenTwelfths
theorem _root_.solution {ρ : ℝ} (hρ : 11/12 < ρ) :
    ∀ o : Outcome (Fin 8) 3, o.Valid (instP (min (ρ - 11/12) 1 / 12)) →
      ∃ i, util (instV i) o i
        < ρ * MMS 3 (instV i) (instP (min (ρ - 11/12) 1 / 12)) := by
  classical
  set ε : ℝ := ρ - 11/12 with hε_def
  have hε : 0 < ε := by simp [hε_def]; linarith
  set δ : ℝ := min ε 1 / 12 with hδ_def
  have hδ0 : 0 < δ := by
    have : 0 < min ε 1 := lt_min hε one_pos
    simpa [hδ_def] using by positivity
  have hδ12 : δ ≤ 1/12 := by
    have : min ε 1 ≤ 1 := min_le_right _ _
    simp only [hδ_def]
    linarith
  have hδε : 108 * δ ≤ 9 * ε := by
    have : min ε 1 ≤ ε := min_le_left _ _
    simp only [hδ_def]
    linarith
  intro o hvalid
  by_contra hcon
  push_neg at hcon
  -- the three agents' guarantees
  have h0 := hcon 0
  have h1 := hcon 1
  have h2 := hcon 2
  rw [MMS_agent_zero hδ0.le hδ12] at h0
  rw [MMS_agent_one hδ0.le hδ12] at h1
  rw [MMS_agent_two hδ0.le] at h2
  -- total money available
  have hmoney_sum : ∑ j, o.money j ≤ ∑ g ∈ o.sold, instP δ g := hvalid.2.2.2
  have hmoney_nonneg : ∀ j, 0 ≤ o.money j := hvalid.2.2.1
  have hsoldU : (∑ g ∈ o.sold, instP δ g) = δ * ∑ g ∈ o.sold, (fnU g : ℝ) := by
    rw [Finset.mul_sum]; rfl
  have hsold_le : (∑ g ∈ o.sold, (fnU g : ℝ)) ≤ 108 := by
    have : (∑ g ∈ o.sold, (fnU g : ℝ)) ≤ ∑ g, (fnU g : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun g _ _ => by positivity)
    rw [cast_sum_eq Finset.univ fnU 108 fnU_total] at this
    simpa using this
  have hmoney_le : ∀ j, o.money j ≤ ∑ g ∈ o.sold, instP δ g := by
    intro j
    refine le_trans ?_ hmoney_sum
    exact Finset.single_le_sum (fun k _ => hmoney_nonneg k) (Finset.mem_univ j)
  have hmoney_small : ∀ j, o.money j ≤ 108 * δ := by
    intro j
    refine (hmoney_le j).trans ?_
    rw [hsoldU]
    calc δ * ∑ g ∈ o.sold, (fnU g : ℝ) ≤ δ * 108 := by
          exact mul_le_mul_of_nonneg_left hsold_le hδ0.le
      _ = 108 * δ := by ring
  -- agent 0 keeps goods worth more than 33
  have hR : (33 : ℝ) < ∑ g ∈ o.kept 0, (fnR g : ℝ) := by
    have hu : util (instV 0) o 0 = (∑ g ∈ o.kept 0, (fnR g : ℝ)) + o.money 0 := rfl
    have := hcon 0
    rw [MMS_agent_zero hδ0.le hδ12] at this
    rw [hu] at this
    have hm := hmoney_small 0
    nlinarith [hδε, hε]
  -- agent 1 keeps goods worth more than 33
  have hC : (33 : ℝ) < ∑ g ∈ o.kept 1, (fnC g : ℝ) := by
    have hu : util (instV 1) o 1 = (∑ g ∈ o.kept 1, (fnC g : ℝ)) + o.money 1 := rfl
    have := hcon 1
    rw [MMS_agent_one hδ0.le hδ12] at this
    rw [hu] at this
    have hm := hmoney_small 1
    nlinarith [hδε, hε]
  -- the sold goods are worth more than 33 to agent 2
  have hU : (33 : ℝ) < ∑ g ∈ o.sold, (fnU g : ℝ) := by
    have hu : util (instV 2) o 2 = o.money 2 := by
      simp [util, instV]
    have hmon := hmoney_le 2
    rw [hu] at h2
    rw [hsoldU] at hmon
    have hkey : 33 * δ + 36 * ε * δ ≤ δ * ∑ g ∈ o.sold, (fnU g : ℝ) := by
      nlinarith [h2, hmon]
    have hkey' : δ * (33 + 36 * ε) ≤ δ * ∑ g ∈ o.sold, (fnU g : ℝ) := by nlinarith [hkey]
    have := le_of_mul_le_mul_left hkey' hδ0
    nlinarith [hε]
  -- contradiction with the Feige–Norkin instance
  have hdisj : ∀ i k : Fin 3, i ≠ k →
      Disjoint (![o.kept 0, o.kept 1, o.sold] i) (![o.kept 0, o.kept 1, o.sold] k) := by
    intro i k hik
    have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
    rcases hi3 with rfl | rfl | rfl <;> rcases hk3 with rfl | rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] <;>
      first
        | exact absurd rfl hik
        | exact hvalid.2.1 0 1 (by decide)
        | exact hvalid.2.1 1 0 (by decide)
        | exact (hvalid.1 0).symm
        | exact (hvalid.1 1).symm
        | exact hvalid.1 0
        | exact hvalid.1 1
  obtain ⟨i, hi⟩ := feigeNorkin_disjoint ![o.kept 0, o.kept 1, o.sold] hdisj
  · have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hi3 with rfl | rfl | rfl
    · simp only [fnW, Matrix.cons_val_zero] at hi
      have : (∑ g ∈ o.kept 0, (fnR g : ℝ)) ≤ 33 := by
        rw [← Nat.cast_sum]
        exact_mod_cast hi
      linarith
    · simp only [fnW, Matrix.cons_val_one] at hi
      have : (∑ g ∈ o.kept 1, (fnC g : ℝ)) ≤ 33 := by
        rw [← Nat.cast_sum]
        exact_mod_cast hi
      linarith
    · simp only [fnW, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hi
      have : (∑ g ∈ o.sold, (fnU g : ℝ)) ≤ 33 := by
        rw [← Nat.cast_sum]
        exact_mod_cast hi
      linarith
end FairSelling.ElevenTwelfths
