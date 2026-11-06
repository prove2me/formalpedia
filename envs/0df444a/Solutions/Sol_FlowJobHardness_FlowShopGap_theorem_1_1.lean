-- Prove2me | solution 1 for FlowJobHardness.FlowShopGap.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T16:44:47.033568+00:00
-- url     : https://prove2.me/submissions/427a1f83-0112-47b5-8621-4e4243117daf

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_FlowShopGap_Construction
import Definitions.Def_FlowJobHardness_FlowShopGap_GoodOps
import Theorems.Thm_FlowJobHardness_FlowShopGap_lb_display
import Theorems.Thm_FlowJobHardness_FlowShopGap_lemma_2_3
import Theorems.Thm_FlowJobHardness_FlowShopGap_lemma_2_4

open JobShopLTAS.Core
open FlowJobHardness.FlowShopGap

theorem solution (r d : ℕ) (hr : 8 ≤ r) :
    (∀ q : Fin (size r d), (inst r d).jobLength q = (r : ℝ) ^ (2 * d)) ∧
      (∀ t : Fin (size r d), (inst r d).load t = (r : ℝ) ^ (2 * d)) ∧
      ∀ s : (inst r d).Op → ℝ, (inst r d).IsFeasibleSchedule Finset.univ s →
        (r : ℝ) ^ (2 * d) * min (r : ℝ) ((d : ℝ) / 4) ≤ (inst r d).makespan Finset.univ s := by
  obtain ⟨h1, h2⟩ := lb_display r d
  refine ⟨h1, h2, ?_⟩
  intro s hs
  set M := (inst r d).makespan Finset.univ s with hM
  have hlb : (0 : ℝ) ≤ (r : ℝ) ^ (2 * d) := by positivity
  -- every operation completes by the makespan
  have hle : ∀ o : (inst r d).Op, s o + (inst r d).proc o ≤ M := by
    intro o
    have hb : BddAbove (Set.range fun o : {o : (inst r d).Op // o.1 ∈ Finset.univ} =>
        s o.1 + (inst r d).proc o.1) := Set.finite_range _ |>.bddAbove
    exact le_ciSup hb ⟨o, Finset.mem_univ _⟩
  have hM0 : 0 ≤ M := by
    apply Real.iSup_nonneg
    intro o
    have := hs.start_nonneg o.1 (Finset.mem_univ _)
    have := (inst r d).p_nonneg o.1.1 o.1.2
    unfold Instance.proc
    linarith
  by_cases hbig : (r : ℝ) * (r : ℝ) ^ (2 * d) ≤ M
  · calc (r : ℝ) ^ (2 * d) * min (r : ℝ) ((d : ℝ) / 4) ≤ (r : ℝ) ^ (2 * d) * r :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hlb
      _ = (r : ℝ) * (r : ℝ) ^ (2 * d) := by ring
      _ ≤ M := hbig
  rw [not_le] at hbig
  obtain ⟨g, hg1, hg2, hsum⟩ := lemma_2_4 r d hr s hs hbig
  -- the union sets
  set U : ℕ → Set ℝ := fun f => ⋃₀ T r d s g f with hU
  have hUeq : ∀ f, U f = ⋃ o ∈ goodOpsOn r d s g f, firstHalf r d s o := by
    intro f
    ext x
    simp only [hU, T, Set.mem_sUnion, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨I, ⟨o, ho, rfl⟩, hx⟩
      exact ⟨o, ho, hx⟩
    · rintro ⟨o, ho, hx⟩
      exact ⟨_, ⟨o, ho, rfl⟩, hx⟩
  have hUmeas : ∀ f, MeasurableSet (U f) := by
    intro f
    rw [hUeq f]
    exact Finset.measurableSet_biUnion _ (fun o _ => measurableSet_Ico)
  have hUsub : ∀ f, U f ⊆ Set.Icc 0 M := by
    intro f x hx
    rw [hUeq f] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨o, _, hx⟩ := hx
    simp only [firstHalf, Set.mem_Ico] at hx
    have h0 := hs.start_nonneg o (Finset.mem_univ _)
    have hp : 0 ≤ (inst r d).proc o := (inst r d).p_nonneg o.1 o.2
    have := hle o
    constructor <;> linarith [hx.1, hx.2]
  have hUfin : ∀ f, MeasureTheory.volume (U f) ≠ ⊤ := by
    intro f
    refine ne_top_of_le_ne_top ?_ (MeasureTheory.measure_mono (hUsub f))
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 d) : Set ℕ) U := by
    intro k hk l hl hkl
    simp only [Finset.coe_Icc, Set.mem_Icc] at hk hl
    have key : ∀ k l, 1 ≤ k → k < l → l ≤ d → Disjoint (U k) (U l) := by
      intro k l hk1 hkl hl2
      simp only [hU]
      rw [Set.disjoint_sUnion_left]
      intro I hI
      rw [Set.disjoint_sUnion_right]
      intro J hJ
      exact lemma_2_3 r d (by omega) s hs g hg1 hg2 k l hk1 hkl hl2 I hI J hJ
    rcases lt_or_gt_of_ne hkl with h | h
    · exact key k l hk.1 h hl.2
    · exact (key l k hl.1 h hk.2).symm
  have hvol : MeasureTheory.volume (⋃ f ∈ Finset.Icc 1 d, U f)
      = ∑ f ∈ Finset.Icc 1 d, MeasureTheory.volume (U f) :=
    MeasureTheory.measure_biUnion_finset hdisj (fun f _ => hUmeas f)
  have hsumL : ∑ f ∈ Finset.Icc 1 d, L r d s g f
      = (MeasureTheory.volume (⋃ f ∈ Finset.Icc 1 d, U f)).toReal := by
    rw [hvol, ENNReal.toReal_sum (fun f _ => hUfin f)]
    rfl
  have hunion_sub : (⋃ f ∈ Finset.Icc 1 d, U f) ⊆ Set.Icc 0 M := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨f, _, hx⟩ := hx
    exact hUsub f hx
  have hbound : (MeasureTheory.volume (⋃ f ∈ Finset.Icc 1 d, U f)).toReal ≤ M := by
    have h := MeasureTheory.measure_mono (μ := MeasureTheory.volume) hunion_sub
    rw [Real.volume_Icc] at h
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rw [ENNReal.toReal_ofReal (by linarith)] at this
    linarith
  calc (r : ℝ) ^ (2 * d) * min (r : ℝ) ((d : ℝ) / 4)
      ≤ (r : ℝ) ^ (2 * d) * ((d : ℝ) / 4) := mul_le_mul_of_nonneg_left (min_le_right _ _) hlb
    _ = (r : ℝ) ^ (2 * d) / 4 * (d : ℝ) := by ring
    _ ≤ ∑ f ∈ Finset.Icc 1 d, L r d s g f := hsum
    _ ≤ M := by rw [hsumL]; exact hbound
