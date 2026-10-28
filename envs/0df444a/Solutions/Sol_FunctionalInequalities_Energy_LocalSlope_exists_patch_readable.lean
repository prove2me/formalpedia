-- Prove2me | solution 1 for FunctionalInequalities.Energy.LocalSlope.exists_patch_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:04:57.904388+00:00
-- url     : https://prove2.me/submissions/4f6b9e69-bc7b-4721-b948-54c4a2dc627e

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Density
import Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_exists_partition_readable
import Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_exists_patch_of_isCompact_readable

noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
universe u
section Patch
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
omit [CompleteSpace V] in
/-- `C2`.  The McShane patch: a globally Lipschitz `F` with constant `9 L + 8 α` independent of
`δ`, equal to `f` on a Borel set of co-mass at most `δ`, uniformly within `2 L + 2 α` of `f`, and
whose asymptotic Lipschitz constant on that set is within `2 α` of the local slope of `f`. -/
theorem solution (ν : ProbabilityMeasure V) {f : V → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {α : ℝ≥0} (hα : 0 < α) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ (F : V → ℝ) (K : Set V), LipschitzWith (9 * L + 8 * α) F ∧ MeasurableSet K ∧
      (ν : Measure V) Kᶜ ≤ δ ∧ (∀ x ∈ K, F x = f x) ∧
      (∀ x, |F x - f x| ≤ 2 * (L : ℝ) + 2 * (α : ℝ)) ∧
      ∀ x ∈ K, FunctionalInequalities.Energy.AsymptoticLipschitz.apply F x ≤ FunctionalInequalities.Energy.LocalSlope.apply f x + 2 * (α : ℝ≥0∞) := by
  classical
  obtain ⟨D, c, hDmeas, hDdisj, hDcover, hcle, hDlip, hDslope⟩ := FunctionalInequalities.Energy.LocalSlope.exists_partition_readable hf hα
  set δ' : ℝ≥0∞ := min δ 1 with hδ'def
  have hδ'0 : 0 < δ' := lt_min hδ one_pos
  have hδ'top : δ' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hhalf0 : 0 < δ' / 2 := ENNReal.div_pos hδ'0.ne' (by norm_num)
  set ε : ℕ → ℝ≥0∞ := fun i ↦ δ' / 2 * ((2 : ℝ≥0∞)⁻¹) ^ (i + 1) with hεdef
  have hε0 : ∀ i, ε i ≠ 0 := by
    intro i
    exact mul_ne_zero hhalf0.ne' (pow_ne_zero _ (ENNReal.inv_ne_zero.2 (by norm_num)))
  have hεsum : ∑' i, ε i = δ' / 2 := by
    rw [hεdef, ENNReal.tsum_mul_left]
    have hgeo : ∑' n : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) = 1 := by
      have hfun : (fun n : ℕ ↦ ((2 : ℝ≥0∞)⁻¹) ^ (n + 1))
          = fun n : ℕ ↦ (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞)⁻¹) ^ n := funext fun n ↦ by ring
      rw [hfun, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      norm_num
      exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
    rw [hgeo, mul_one]
  have hexK : ∀ i, ∃ Kc ⊆ D i, IsCompact Kc ∧ (ν : Measure V) (D i \ Kc) < ε i := fun i ↦
    (hDmeas i).exists_isCompact_sdiff_lt (measure_ne_top _ _) (hε0 i)
  choose Kc hKcsub hKccomp hKcmeas using hexK
  have hKcdisj : ∀ i j, i ≠ j → Disjoint (Kc i) (Kc j) := fun i j hij ↦
    Disjoint.mono (hKcsub i) (hKcsub j) (hDdisj hij)
  have hKclip : ∀ i, LipschitzOnWith (c i) f (Kc i) := fun i ↦ (hDlip i).mono (hKcsub i)
  -- a finite family already carries all but `δ` of the mass
  have hDsum : ∑' i, (ν : Measure V) (D i) = 1 := by
    rw [← measure_iUnion hDdisj hDmeas, hDcover, measure_univ]
  have htail : Tendsto (fun N ↦ ∑' k, (ν : Measure V) (D (k + N))) atTop (𝓝 0) :=
    ENNReal.tendsto_sum_nat_add _ (by rw [hDsum]; exact ENNReal.one_ne_top)
  obtain ⟨N, hN⟩ := ((htail.eventually (gt_mem_nhds hhalf0)).exists)
  obtain ⟨F, hFlip, hFclose, hFeq, hFslope⟩ :=
    FunctionalInequalities.Energy.LocalSlope.exists_patch_of_isCompact_readable hf N Kc c hKccomp hKcdisj hKclip hcle
  refine ⟨F, ⋃ i : Fin N, Kc (i : ℕ), hFlip, ?_, ?_, ?_, hFclose, ?_⟩
  · exact (isCompact_iUnion fun i ↦ hKccomp _).isClosed.measurableSet
  · have hsub : (⋃ i : Fin N, Kc (i : ℕ))ᶜ ⊆ (⋃ i, D i \ Kc i) ∪ (⋃ k, D (k + N)) := by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hDcover ▸ Set.mem_univ x : x ∈ ⋃ i, D i)
      by_cases hiN : i < N
      · refine Or.inl (Set.mem_iUnion.2 ⟨i, hi, fun hmem ↦ hx ?_⟩)
        exact Set.mem_iUnion.2 ⟨⟨i, hiN⟩, hmem⟩
      · refine Or.inr (Set.mem_iUnion.2 ⟨i - N, ?_⟩)
        rwa [Nat.sub_add_cancel (by omega)]
    calc (ν : Measure V) (⋃ i : Fin N, Kc (i : ℕ))ᶜ
        ≤ (ν : Measure V) ((⋃ i, D i \ Kc i) ∪ (⋃ k, D (k + N))) := measure_mono hsub
      _ ≤ (ν : Measure V) (⋃ i, D i \ Kc i) + (ν : Measure V) (⋃ k, D (k + N)) :=
          measure_union_le _ _
      _ ≤ (∑' i, (ν : Measure V) (D i \ Kc i)) + ∑' k, (ν : Measure V) (D (k + N)) :=
          add_le_add (measure_iUnion_le _) (measure_iUnion_le _)
      _ ≤ (∑' i, ε i) + δ' / 2 := add_le_add (ENNReal.tsum_le_tsum fun i ↦ (hKcmeas i).le) hN.le
      _ = δ' := by rw [hεsum, ENNReal.add_halves]
      _ ≤ δ := min_le_left _ _
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact hFeq i i.2 x hi
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    refine (hFslope i i.2 x hi).trans ?_
    refine (hDslope i x (hKcsub i hi)).trans ?_
    have h2α : (α : ℝ≥0∞) ≤ 2 * (α : ℝ≥0∞) := by
      calc (α : ℝ≥0∞) = 1 * (α : ℝ≥0∞) := (one_mul _).symm
        _ ≤ 2 * (α : ℝ≥0∞) := by gcongr; norm_num
    exact add_le_add le_rfl h2α
