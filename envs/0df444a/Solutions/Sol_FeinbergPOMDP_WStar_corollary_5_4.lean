-- Prove2me | solution 1 for FeinbergPOMDP.WStar.corollary_5_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T17:58:17.720167+00:00
-- url     : https://prove2.me/submissions/193b33b1-f1e4-4ed6-b0a3-48d96c843268
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model
import Theorems.Thm_FeinbergPOMDP_WStar_lemma_5_3

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergPOMDP.WStar

/-- Layer-cake bound: if two probability measures differ by at most `ε` on every measurable set,
then the integrals of a measurable `g : T → [0,1]` differ by at most `ε`. -/
lemma fpw_layer_bound {T : Type*} [MeasurableSpace T] (ν μ : Measure T)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (ε : ℝ)
    (hε : ∀ C : Set T, MeasurableSet C → |ν.real C - μ.real C| ≤ ε)
    (g : T → ℝ) (hg : Measurable g) (hg0 : ∀ t, 0 ≤ g t) (hg1 : ∀ t, g t ≤ 1) :
    |∫ t, g t ∂ν - ∫ t, g t ∂μ| ≤ ε := by
  have hint : ∀ (m : Measure T) [IsProbabilityMeasure m], Integrable g m := fun m _ =>
    Integrable.of_bound hg.aestronglyMeasurable 1
      (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 t)]; exact hg1 t)
  have hlc : ∀ (m : Measure T) [IsProbabilityMeasure m],
      ∫ t, g t ∂m = ∫ s in Set.Ioc (0 : ℝ) 1, m.real {a | s < g a} := by
    intro m _
    rw [(hint m).integral_eq_integral_meas_lt (Eventually.of_forall hg0)]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      Set.Ioc_subset_Ioi_self ?_
    intro s hs
    have hs1 : 1 < s := by
      simp only [Set.mem_diff, Set.mem_Ioi, Set.mem_Ioc, not_and, not_le] at hs
      exact hs.2 hs.1
    have : {a | s < g a} = ∅ := by
      ext a; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      linarith [hg1 a]
    simp [this]
  have hio : ∀ (m : Measure T) [IsProbabilityMeasure m],
      IntegrableOn (fun s => m.real {a | s < g a}) (Set.Ioc (0 : ℝ) 1) := by
    intro m _
    have hanti : AntitoneOn (fun s => m.real {a | s < g a}) (Set.Icc (0 : ℝ) 1) := by
      intro s _ s' _ hss'
      exact measureReal_mono (fun a (ha : s' < g a) => lt_of_le_of_lt hss' ha)
    exact (hanti.integrableOn_isCompact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  rw [hlc ν, hlc μ, ← integral_sub (hio ν) (hio μ)]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc (0 : ℝ) 1)
    (f := fun s => ν.real {a | s < g a} - μ.real {a | s < g a}) (C := ε)
    (by simp) (fun s _ => by
      rw [Real.norm_eq_abs]; exact hε _ (measurableSet_lt measurable_const hg))
  simpa using this

/-- If `μₙ(C) → μ(C)` uniformly in Borel `C`, then `μₙ → μ` in the total variation. -/
lemma fpw_tendstoTV_of_unif {T : Type*} [MeasurableSpace T]
    (μs : ℕ → ProbabilityMeasure T) (μ : ProbabilityMeasure T)
    (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ C : Set T, MeasurableSet C →
      |(μs n : Measure T).real C - (μ : Measure T).real C| ≤ ε) :
    TendstoTV μs μ := by
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn f hf hf1 => ?_⟩
  have hp := fpw_layer_bound (μs n : Measure T) μ (ε / 2) (hN n hn) (fun t => max (f t) 0)
    (hf.max measurable_const) (fun t => le_max_right _ _)
    (fun t => max_le (le_trans (le_abs_self _) (hf1 t)) zero_le_one)
  have hm := fpw_layer_bound (μs n : Measure T) μ (ε / 2) (hN n hn) (fun t => max (-f t) 0)
    (hf.neg.max measurable_const) (fun t => le_max_right _ _)
    (fun t => max_le (le_trans (neg_le_abs _) (hf1 t)) zero_le_one)
  have hdec : ∀ t, f t = max (f t) 0 - max (-f t) 0 := fun t => by
    rcases le_total 0 (f t) with h0 | h0
    · rw [max_eq_left h0, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h0, max_eq_left (by linarith)]; ring
  have hint : ∀ (m : Measure T) [IsProbabilityMeasure m] (g : T → ℝ), Measurable g →
      (∀ t, |g t| ≤ 1) → Integrable g m := fun m _ g hg hg1 =>
    Integrable.of_bound hg.aestronglyMeasurable 1
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hg1 t)
  have hb1 : ∀ t, |max (f t) 0| ≤ 1 := fun t => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_trans (le_abs_self _) (hf1 t)) zero_le_one
  have hb2 : ∀ t, |max (-f t) 0| ≤ 1 := fun t => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_trans (neg_le_abs _) (hf1 t)) zero_le_one
  have hsplit : ∀ (m : Measure T) [IsProbabilityMeasure m],
      ∫ t, f t ∂m = ∫ t, max (f t) 0 ∂m - ∫ t, max (-f t) 0 ∂m := by
    intro m _
    have i1 : Integrable (fun t => max (f t) 0) m := hint m _ (by fun_prop) hb1
    have i2 : Integrable (fun t => max (-f t) 0) m := hint m _ (by fun_prop) hb2
    rw [← integral_sub i1 i2]
    exact integral_congr_ae (Eventually.of_forall hdec)
  rw [hsplit, hsplit]
  calc |(∫ t, max (f t) 0 ∂(μs n : Measure T) - ∫ t, max (-f t) 0 ∂(μs n : Measure T)) -
        (∫ t, max (f t) 0 ∂(μ : Measure T) - ∫ t, max (-f t) 0 ∂(μ : Measure T))|
      = |(∫ t, max (f t) 0 ∂(μs n : Measure T) - ∫ t, max (f t) 0 ∂(μ : Measure T)) -
        (∫ t, max (-f t) 0 ∂(μs n : Measure T) - ∫ t, max (-f t) 0 ∂(μ : Measure T))| := by
          ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hp hm
    _ = ε := by ring

theorem solution {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (hP : IsWeaklyContinuous (kernelPM P)) (hQ : IsTVContinuous (kernelPM Q)) :
    IsTVContinuous (fun p : ProbabilityMeasure X × A => obsLaw P Q p.1 p.2) := by
  have key : ∀ (z : ProbabilityMeasure X) (a : A) (C : Set Y) (hC : MeasurableSet C),
      RFamily P Q (Set.univ \ ∅) ⟨C, hC⟩ (z, a) = (obsLaw P Q z a : Measure Y).real C := by
    intro z a C hC
    simp only [RFamily, obsLaw, Set.diff_empty]
    rw [ProbabilityMeasure.toMeasure_map, measureReal_def, Measure.map_apply measurable_snd hC,
      ← Set.univ_prod]
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_toReal]
  have hR := (lemma_5_3 P Q hP hQ Set.univ ∅ isOpen_univ isOpen_empty).2
  intro s ss hss
  apply fpw_tendstoTV_of_unif
  intro ε hε
  obtain ⟨N, hN⟩ := hR s.1 s.2 (fun n => (ss n).1) (fun n => (ss n).2)
    ((continuous_fst.tendsto _).comp hss) ((continuous_snd.tendsto _).comp hss) ε hε
  refine ⟨N, fun n hn C hC => ?_⟩
  have := hN n hn ⟨C, hC⟩
  rwa [key, key] at this
