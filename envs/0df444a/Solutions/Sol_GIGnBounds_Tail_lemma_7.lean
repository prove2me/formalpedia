-- Prove2me | solution 1 for GIGnBounds.Tail.lemma_7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-25T00:36:30.743365+00:00
-- url     : https://prove2.me/submissions/efd0a8a8-dff8-4834-9da2-b5d71cc4dcef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting
import Theorems.Thm_GIGnBounds_Tail_lemma_14
import Theorems.Thm_GIGnBounds_Tail_server_comparison

open MeasureTheory ProbabilityTheory GIGnBounds.Tail Filter Topology

namespace GIGnL7Aux

lemma eqLaw_Iic (μ : Measure ℝ) : eqLaw μ (Set.Iic 0) = 0 := by
  unfold eqLaw
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply measurableSet_Iic]
  have : Set.Iic (0 : ℝ) ∩ Set.Ioi 0 = ∅ := by
    ext a; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi, Set.mem_empty_iff_false,
      iff_false, not_and, not_lt]; intro h; exact h
  rw [this, measure_empty]

lemma eqLaw_isProb (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : IsTimeLaw μ) :
    IsProbabilityMeasure (eqLaw μ) := by
  constructor
  have hrate : 0 < rate μ := inv_pos.mpr hμ.mean_pos
  have hae : ∀ᵐ x ∂μ, 0 ≤ x := by
    have hs : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
    rw [ae_iff, hs]; exact hμ.nonneg
  rw [eqLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h1 : ∀ z, ENNReal.ofReal (rate μ * (μ (Set.Ioi z)).toReal) =
      ENNReal.ofReal (rate μ) * μ (Set.Ioi z) := by
    intro z
    rw [ENNReal.ofReal_mul hrate.le, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hlc := lintegral_eq_lintegral_meas_lt μ hae aemeasurable_id
  try simp only [id_eq, id] at hlc
  have : ∫⁻ t in Set.Ioi 0, μ (Set.Ioi t) = ∫⁻ t in Set.Ioi 0, μ {a : ℝ | t < a} := rfl
  rw [this, ← hlc, ← ofReal_integral_eq_lintegral_ofReal hμ.integrable hae,
    ← ENNReal.ofReal_mul hrate.le]
  have : rate μ * ∫ x, x ∂μ = 1 := by
    rw [rate, mean]; exact inv_mul_cancel₀ hμ.mean_pos.ne'
  rw [this, ENNReal.ofReal_one]

/-- The law of the `i`-th initial residual of `𝒬^{n,n'}_res`. -/
noncomputable def resLaw (n' : ℕ) (μS : Measure ℝ) {n : ℕ} (i : Fin n) : Measure ℝ :=
  if (i : ℕ) < n' then eqLaw μS else Measure.dirac 0

lemma resLaw_isProb (n' : ℕ) (μS : Measure ℝ) [IsProbabilityMeasure μS] (hS : IsTimeLaw μS)
    {n : ℕ} (i : Fin n) : IsProbabilityMeasure (resLaw n' μS i) := by
  unfold resLaw
  split_ifs
  · exact eqLaw_isProb μS hS
  · infer_instance

lemma resLaw_Iio (n' : ℕ) (μS : Measure ℝ) {n : ℕ} (i : Fin n) : resLaw n' μS i (Set.Iio 0) = 0 := by
  unfold resLaw
  split_ifs
  · exact measure_mono_null Set.Iio_subset_Iic_self (eqLaw_Iic μS)
  · simp

end GIGnL7Aux

open GIGnL7Aux in
theorem solution (n : ℕ) (hn : 0 < n) (μA μS : Measure ℝ) [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]
    (hA : IsTimeLaw μA) (hS : IsTimeLaw μS)
    (hstab : rate μA < n * rate μS)
    (π : Measure ℕ) (hπ : IsSteadyStateLaw n μA μS π)
    (n' : ℕ) (hn'₁ : 1 ≤ n') (hn'₂ : n' ≤ n) (x : ℝ) (hx : (n' : ℝ) - n ≤ x)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : RenewalFamily Ω P n' μA μS) :
    π.real {q : ℕ | x ≤ (q : ℝ) - n} ≤
      P.real {ω | ((x + ((n : ℝ) - n') : ℝ) : EReal) ≤ supFrom (fun t => (F.Ae ω t : ℝ) - ∑ i, (F.Ne i ω t : ℝ))} := by
  haveI : IsProbabilityMeasure π := hπ.1
  set z := x + ((n : ℝ) - n') with hz
  have hz0 : 0 ≤ z := by rw [hz]; linarith
  set E := {ω | (z : EReal) ≤ supFrom (fun t => (F.Ae ω t : ℝ) - ∑ i, (F.Ne i ω t : ℝ))} with hE
  rcases hz0.lt_or_eq with hzpos | hzero
  · ---------------------------------------------------------------- the main case `z > 0`
    -- the initial law of `𝒬^{n,n'}_res`
    set ν₀ : Measure (ℝ × (Fin n → ℝ)) :=
      (eqLaw μA).prod (Measure.pi (fun i : Fin n => resLaw n' μS i)) with hν₀
    haveI : IsProbabilityMeasure (eqLaw μA) := eqLaw_isProb μA hA
    haveI : ∀ i : Fin n, IsProbabilityMeasure (resLaw n' μS i) := resLaw_isProb n' μS hS
    have hinit : IsInitLaw n ν₀ := by
      refine ⟨inferInstance, ?_⟩
      rw [ae_iff]
      have hsub : {a : ℝ × (Fin n → ℝ) | ¬ (0 ≤ a.1 ∧ ∀ i, 0 ≤ a.2 i)} ⊆
          (Prod.fst ⁻¹' Set.Iio 0) ∪ ⋃ i : Fin n, (Prod.snd ⁻¹' (Function.eval i ⁻¹' Set.Iio 0)) := by
        intro a ha
        simp only [Set.mem_setOf_eq, not_and_or, not_le, not_forall] at ha
        rcases ha with h | ⟨i, hi⟩
        · exact Or.inl h
        · exact Or.inr (Set.mem_iUnion.mpr ⟨i, hi⟩)
      apply measure_mono_null hsub
      apply measure_union_null
      · rw [hν₀, ← Set.prod_univ, Measure.prod_prod]
        have : eqLaw μA (Set.Iio 0) = 0 :=
          measure_mono_null Set.Iio_subset_Iic_self (eqLaw_Iic μA)
        rw [this, zero_mul]
      · apply measure_iUnion_null
        intro i
        rw [hν₀, ← Set.univ_prod, Measure.prod_prod,
          Measure.pi_eval_preimage_null _ (resLaw_Iio n' μS i), mul_zero]
    have hconv := hπ.2 ν₀ hinit
    -- the comparison chain for every `t > 0`
    have hchain : ∀ t : ℝ, 0 < t →
        (queueMeasure n μA μS ν₀).real {ω | x ≤ (queueLength ω t : ℝ) - n} ≤ P.real E := by
      intro t ht
      have h1 := GIGnBounds.Tail.server_comparison n n' hn'₁ hn'₂ μA μS hA hS t (x + n) ht.le
      have h14 := GIGnBounds.Tail.lemma_14 n' (by omega) μA μS hA hS Ω P F t z ht hzpos
      have e1 : {ω : QueueSpace n | x ≤ (queueLength ω t : ℝ) - n} =
          {ω | x + n ≤ (queueLength ω t : ℝ)} := by
        ext ω; simp only [Set.mem_setOf_eq]; constructor <;> intro h <;> linarith
      have e2 : {ω : QueueSpace n' | x + n ≤ (queueLength ω t : ℝ)} =
          {ω | z ≤ (queueLength ω t : ℝ) - n'} := by
        ext ω; simp only [Set.mem_setOf_eq, hz]; constructor <;> intro h <;> linarith
      have hmono : {ω | (z : EReal) ≤ supUpTo (fun s => (F.Ae ω s : ℝ) - ∑ i, (F.Ne i ω s : ℝ)) t}
          ⊆ E := by
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        refine le_trans hω ?_
        unfold supUpTo supFrom
        apply iSup₂_le
        intro s hs
        exact le_iSup₂ (f := fun s (_ : 0 ≤ s) => (((F.Ae ω s : ℝ) - ∑ i, (F.Ne i ω s : ℝ) : ℝ) : EReal))
          s hs.1
      rw [e1]
      refine h1.trans ?_
      rw [e2]
      exact h14.trans (measureReal_mono hmono)
    -- the limit `t → ∞`
    set K := ⌈x + n⌉₊ with hK
    have hset : ∀ (m : ℕ) (Q : Type) (f : Q → ℕ), {ω | x ≤ (f ω : ℝ) - n} = {ω | K ≤ f ω} := by
      intro m Q f
      ext ω; simp only [Set.mem_setOf_eq]
      rw [hK, Nat.ceil_le]; constructor <;> intro h <;> linarith
    have hπE : π.real {q : ℕ | x ≤ (q : ℝ) - n} = 1 - ∑ q ∈ Finset.range K, π.real {q} := by
      have : {q : ℕ | x ≤ (q : ℝ) - n} = ((Finset.range K : Set ℕ))ᶜ := by
        ext q; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Finset.coe_range, Set.mem_Iio,
          not_lt]
        rw [hK, Nat.ceil_le]; constructor <;> intro h <;> linarith
      rw [this, probReal_compl_eq_one_sub (Finset.measurableSet _), sum_measureReal_singleton]
    have hlow : ∀ t : ℝ, 1 - ∑ q ∈ Finset.range K,
        (queueMeasure n μA μS ν₀).real {ω | queueLength ω t = q} ≤
        (queueMeasure n μA μS ν₀).real {ω | x ≤ (queueLength ω t : ℝ) - n} := by
      intro t
      haveI : IsProbabilityMeasure (queueMeasure n μA μS ν₀) := by
        unfold queueMeasure; infer_instance
      have hcov : (Set.univ : Set (QueueSpace n)) ⊆ {ω | x ≤ (queueLength ω t : ℝ) - n} ∪
          ⋃ q ∈ Finset.range K, {ω | queueLength ω t = q} := by
        intro ω _
        by_cases h : K ≤ queueLength ω t
        · left
          simp only [Set.mem_setOf_eq]
          have : ⌈x + n⌉₊ ≤ queueLength ω t := h
          rw [Nat.ceil_le] at this; linarith
        · right
          simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_range, exists_prop]
          exact ⟨_, by omega, rfl⟩
      have h1 := measureReal_mono hcov (μ := queueMeasure n μA μS ν₀)
      rw [probReal_univ] at h1
      have h2 := measureReal_union_le (μ := queueMeasure n μA μS ν₀)
        {ω | x ≤ (queueLength ω t : ℝ) - n} (⋃ q ∈ Finset.range K, {ω | queueLength ω t = q})
      have h3 := measureReal_biUnion_finset_le (μ := queueMeasure n μA μS ν₀) (Finset.range K)
        (fun q => {ω | queueLength ω t = q})
      linarith
    have htend : Tendsto (fun t => 1 - ∑ q ∈ Finset.range K,
        (queueMeasure n μA μS ν₀).real {ω | queueLength ω t = q}) atTop
        (𝓝 (1 - ∑ q ∈ Finset.range K, π.real {q})) := by
      apply tendsto_const_nhds.sub
      apply tendsto_finset_sum
      intro q _
      have := (ENNReal.tendsto_toReal (measure_ne_top π {q})).comp (hconv q)
      exact this
    rw [hπE]
    apply le_of_tendsto htend
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact (hlow t).trans (hchain t ht)
  · ---------------------------------------------------------------- the trivial case `z = 0`
    rw [← hzero] at hE
    have hae : ∀ᵐ ω ∂P, ∀ i, 0 < F.srv i none ω ∧ ∀ j, 0 ≤ F.srv i (some j) ω := by
      rw [ae_all_iff]
      intro i
      have h1 : ∀ᵐ ω ∂P, 0 < F.srv i none ω := by
        have : P (F.srv i none ⁻¹' Set.Iic 0) = 0 := by
          rw [← Measure.map_apply (F.measurable_srv i none) measurableSet_Iic, F.law_srv_none i,
            eqLaw_Iic]
        rw [ae_iff]; simpa [Set.preimage, not_lt] using this
      have h2 : ∀ᵐ ω ∂P, ∀ j, 0 ≤ F.srv i (some j) ω := by
        rw [ae_all_iff]
        intro j
        have : P (F.srv i (some j) ⁻¹' Set.Iio 0) = 0 := by
          rw [← Measure.map_apply (F.measurable_srv i (some j)) measurableSet_Iio,
            F.law_srv_some i j, hS.nonneg]
        rw [ae_iff]; simpa [Set.preimage, not_le] using this
      filter_upwards [h1, h2] with ω h1 h2 using ⟨h1, h2⟩
    have hsubE : {ω | ∀ i, 0 < F.srv i none ω ∧ ∀ j, 0 ≤ F.srv i (some j) ω} ⊆ E := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      rw [hE]
      simp only [Set.mem_setOf_eq]
      have hNe : ∀ i, F.Ne i ω 0 = 0 := by
        intro i
        simp only [RenewalFamily.Ne, ServiceFamily.Ne, eqCount]
        rw [Nat.card_eq_zero]
        left
        constructor
        intro ⟨k, hk⟩
        have : 0 ≤ ∑ j ∈ Finset.range k, F.srv i (some j) ω :=
          Finset.sum_nonneg (fun j _ => (hω i).2 j)
        linarith [(hω i).1]
      have h0 : (0 : ℝ) ≤ (F.Ae ω 0 : ℝ) - ∑ i, (F.Ne i ω 0 : ℝ) := by
        simp [hNe]
      unfold supFrom
      exact le_trans (EReal.coe_le_coe_iff.mpr h0)
        (le_iSup₂ (f := fun t (_ : 0 ≤ t) => (((F.Ae ω t : ℝ) - ∑ i, (F.Ne i ω t : ℝ) : ℝ) : EReal))
          0 le_rfl)
    have hPE : P.real E = 1 := by
      apply le_antisymm measureReal_le_one
      have hc : P Eᶜ = 0 := by
        apply measure_mono_null _ (ae_iff.mp hae)
        intro ω hω hG
        exact hω (hsubE hG)
      have hcr : P.real Eᶜ = 0 := by rw [measureReal_def, hc]; rfl
      have h1 : P.real (Set.univ : Set Ω) ≤ P.real E + P.real Eᶜ :=
        (measureReal_mono (by intro ω _; by_cases h : ω ∈ E <;> simp [h])).trans
          (measureReal_union_le _ _)
      rw [probReal_univ, hcr] at h1
      linarith
    rw [hPE]
    exact measureReal_le_one
