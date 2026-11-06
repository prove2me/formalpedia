-- Prove2me | solution 1 for FlowJobHardness.ColoringReduction.lemma_3_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:26:05.222922+00:00
-- url     : https://prove2.me/submissions/41783780-8b3c-4578-96f0-18b02c210782

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_ColoringReduction_Construction
import Definitions.Def_FlowJobHardness_ColoringReduction_Schedule
import Theorems.Thm_FlowJobHardness_ColoringReduction_lemma_3_11
import Theorems.Thm_FlowJobHardness_ColoringReduction_lemma_3_12

open JobShopLTAS.Core

namespace CGAux39
open FlowJobHardness.ColoringReduction MeasureTheory

variable {n d : ℕ} {G : SimpleGraph (Fin n)} (c : G.Coloring (Fin d)) {r : ℕ}

theorem sUnion_T (s : (inst G c r).Op → ℝ) (L : ℝ) (g : ℕ) (v : Fin n) :
    ⋃₀ T G c r s L g v = ⋃ (o : (inst G c r).Op), ⋃ (_ : IsGood G c r s o ∧
      jobCompletion G c r s o.1 ≤ L * (R r d : ℝ) ∧
      FlowJobHardness.FlowShopGap.machGroup n ((inst G c r).mach o).val = g ∧
      machVtx ((inst G c r).mach o) = v), firstHalf G c r s o := by
  ext t
  simp only [Set.mem_sUnion, Set.mem_iUnion, T, Set.mem_setOf_eq]
  constructor
  · rintro ⟨I, ⟨o, h1, h2, h3, h4, rfl⟩, ht⟩; exact ⟨o, ⟨h1, h2, h3, h4⟩, ht⟩
  · rintro ⟨o, ⟨h1, h2, h3, h4⟩, ht⟩; exact ⟨_, ⟨o, h1, h2, h3, h4, rfl⟩, ht⟩

theorem meas_U (s : (inst G c r).Op → ℝ) (L : ℝ) (g : ℕ) (v : Fin n) :
    MeasurableSet (⋃₀ T G c r s L g v) := by
  rw [sUnion_T]
  exact MeasurableSet.iUnion fun o => MeasurableSet.iUnion fun _ => measurableSet_Ico

theorem U_sub (s : (inst G c r).Op → ℝ) (hs : (inst G c r).IsFeasibleSchedule Finset.univ s)
    (L : ℝ) (g : ℕ) (v : Fin n) :
    ⋃₀ T G c r s L g v ⊆ Set.Icc 0 (L * (R r d : ℝ)) := by
  rw [sUnion_T]
  intro t ht
  simp only [Set.mem_iUnion] at ht
  obtain ⟨o, ⟨-, h2, -, -⟩, ht⟩ := ht
  unfold firstHalf at ht
  obtain ⟨t1, t2⟩ := ht
  have h0 := hs.start_nonneg o (Finset.mem_univ _)
  have hp := (inst G c r).p_nonneg o.1 o.2
  have hle : s o + (inst G c r).proc o ≤ jobCompletion G c r s o.1 := by
    unfold jobCompletion
    have := le_ciSup (f := fun i : Fin ((inst G c r).μ o.1) => s ⟨o.1, i⟩ + (inst G c r).p o.1 i)
      (Set.finite_range _).bddAbove o.2
    exact this
  have : (inst G c r).proc o = (inst G c r).p o.1 o.2 := rfl
  constructor <;> linarith

theorem freq_ne {u v : Fin n} (h : G.Adj u v) : freq c u ≠ freq c v := by
  unfold freq
  intro e
  exact c.valid h (Fin.ext (by omega))

theorem lemma_3_9_core (hr : 8 ≤ r) (L : ℝ) (hL0 : 0 < L) (s : (inst G c r).Op → ℝ)
    (hs : (inst G c r).IsFeasibleSchedule Finset.univ s)
    (g : ℕ) (hg1 : 1 ≤ g) (hg2 : g ≤ R r d)
    (hsum : (R r d : ℝ) * n / 8 ≤ ∑ v : Fin n, coveredLength G c r s L g v) :
    ∃ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) ∧
      (n : ℝ) / (8 * L) ≤ (I.card : ℝ) := by
  classical
  by_contra hcon
  push_neg at hcon
  set X : ℝ := (n : ℝ) / (8 * L) with hX
  have hX0 : 0 < X := by
    have := hcon ∅ (by simp)
    simpa using this
  set m : ℕ := ⌈X⌉₊ - 1 with hm
  have hceil1 : 1 ≤ ⌈X⌉₊ := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hmX : (m : ℝ) < X := by
    have := Nat.ceil_lt_add_one hX0.le
    rw [hm, Nat.cast_sub hceil1]; push_cast; linarith
  have hcard : ∀ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) → I.card ≤ m := by
    intro I hI
    have h1 := hcon I hI
    have h2 : I.card < ⌈X⌉₊ := by
      have := lt_of_lt_of_le h1 (Nat.le_ceil X)
      exact_mod_cast this
    omega
  set U : Fin n → Set ℝ := fun v => ⋃₀ T G c r s L g v with hU
  have hr2 : 2 ≤ r := by omega
  -- pointwise independence
  have hind : ∀ t : ℝ, G.IsIndepSet ((Finset.univ.filter (fun v => t ∈ U v) : Finset (Fin n)) : Set (Fin n)) := by
    intro t u hu v hv huv hadj
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, hU,
      Set.mem_sUnion] at hu hv
    obtain ⟨I, hI, htI⟩ := hu
    obtain ⟨J, hJ, htJ⟩ := hv
    rcases lt_or_gt_of_ne (freq_ne c hadj) with h | h
    · have := FlowJobHardness.ColoringReduction.lemma_3_11 G c r hr2 s hs v u hadj.symm h L g hg1 hg2
        J hJ I hI
      exact Set.disjoint_left.1 this htJ htI
    · have := FlowJobHardness.ColoringReduction.lemma_3_11 G c r hr2 s hs u v hadj h L g hg1 hg2
        I hI J hJ
      exact Set.disjoint_left.1 this htI htJ
  set B : ℝ := L * (R r d : ℝ) with hB
  have hR0 : (0 : ℝ) < R r d := by
    unfold R; have : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
    push_cast; positivity
  have hB0 : 0 < B := by positivity
  -- integral bound
  have hlint : ∑ v : Fin n, volume (U v) ≤ (m : ENNReal) * ENNReal.ofReal B := by
    have e1 : ∑ v : Fin n, volume (U v) =
        ∫⁻ t, ∑ v : Fin n, (U v).indicator (fun _ => (1 : ENNReal)) t := by
      rw [lintegral_finset_sum]
      · apply Finset.sum_congr rfl
        intro v _
        exact (lintegral_indicator_one (meas_U c s L g v)).symm
      · intro v _
        exact (measurable_const.indicator (meas_U c s L g v))
    rw [e1]
    calc ∫⁻ t, ∑ v : Fin n, (U v).indicator (fun _ => (1 : ENNReal)) t
        ≤ ∫⁻ t, (Set.Icc 0 B).indicator (fun _ => (m : ENNReal)) t := by
          apply lintegral_mono
          intro t
          by_cases ht : t ∈ Set.Icc 0 B
          · rw [Set.indicator_of_mem ht]
            show (∑ v : Fin n, (U v).indicator (fun _ => (1 : ENNReal)) t) ≤ _
            have : ∑ v : Fin n, (U v).indicator (fun _ => (1 : ENNReal)) t =
                ((Finset.univ.filter (fun v => t ∈ U v)).card : ENNReal) := by
              simp only [Set.indicator_apply]
              rw [Finset.sum_boole]
            rw [this]
            exact_mod_cast hcard _ (hind t)
          · rw [Set.indicator_of_notMem ht]
            show (∑ v : Fin n, (U v).indicator (fun _ => (1 : ENNReal)) t) ≤ _
            apply le_of_eq
            apply Finset.sum_eq_zero
            intro v _
            apply Set.indicator_of_notMem
            intro htv
            exact ht (U_sub c s hs L g v htv)
      _ = (m : ENNReal) * volume (Set.Icc 0 B) := lintegral_indicator_const measurableSet_Icc _
      _ = (m : ENNReal) * ENNReal.ofReal B := by rw [Real.volume_Icc, sub_zero]
  have hfin : ∀ v, volume (U v) ≠ ⊤ := by
    intro v
    apply ne_top_of_le_ne_top (b := volume (Set.Icc 0 B))
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · exact measure_mono (U_sub c s hs L g v)
  have hreal : ∑ v : Fin n, coveredLength G c r s L g v ≤ (m : ℝ) * B := by
    unfold coveredLength
    rw [← ENNReal.toReal_sum (fun v _ => hfin v)]
    have := ENNReal.toReal_mono (by
      apply ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hlint
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB0.le] at this
    simpa using this
  have : (m : ℝ) * B < X * B := mul_lt_mul_of_pos_right hmX hB0
  have e : X * B = (R r d : ℝ) * n / 8 := by
    rw [hX, hB]; field_simp
  linarith

end CGAux39

open FlowJobHardness.ColoringReduction in
theorem solution {n d : ℕ} (G : SimpleGraph (Fin n)) (c : G.Coloring (Fin d)) (r : ℕ)
    (hr : 8 ≤ r) (L : ℝ) (hL0 : 0 < L) (hLr : L ≤ r) (s : (inst G c r).Op → ℝ)
    (hs : (inst G c r).IsFeasibleSchedule Finset.univ s)
    (hhalf : (size r d n : ℝ) ≤ 2 * (finishedCount G c r s L : ℝ)) :
    ∃ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) ∧
      (n : ℝ) / (8 * L) ≤ (I.card : ℝ) := by
  obtain ⟨g, hg1, hg2, hsum⟩ :=
    FlowJobHardness.ColoringReduction.lemma_3_12 G c r hr L hL0 hLr s hs hhalf
  exact CGAux39.lemma_3_9_core c hr L hL0 s hs g hg1 hg2 hsum
