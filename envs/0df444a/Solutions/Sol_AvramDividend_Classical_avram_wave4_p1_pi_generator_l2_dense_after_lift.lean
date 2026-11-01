-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_pi_generator_l2_dense_after_lift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:59:34.973148+00:00
-- url     : https://prove2.me/submissions/cc3f7ebf-6e73-428b-9a5c-fb6fdced906b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_pi_system_boolean_indicator_span
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_pointwise_indicator_span_l2_lift

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set TopologicalSpace AvramDividend.Classical
open scoped ENNReal NNReal

/-- For a finite marked predictable energy measure, a measurable Pi-system
whose Boolean algebra is measure-dense has a *dense L² linear span of its
bare generator indicators* (plus the universe and empty set). This completes
the Boolean-to-elementary predictable kernel approximation pipeline. -/
theorem solution
    {α : Type*} [mα : MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (G : Set (Set α)) (hPi : IsPiSystem G)
    (hGm : ∀ t : Set α, t ∈ G → MeasurableSet t)
    (hGen : mα = MeasurableSpace.generateFrom G) :
    let GP : Set (Set α) :=
      insert Set.univ (insert (∅ : Set α) G)
    let S : Set (Lp ℝ (2 : ℝ≥0∞) μ) :=
      {v | ∃ (t : Set α) (ht : t ∈ GP)
        (htm : MeasurableSet t) (hμt : μ t ≠ ⊤),
        indicatorConstLp (2 : ℝ≥0∞) htm hμt (1 : ℝ) = v}
    ∀ f : Lp ℝ (2 : ℝ≥0∞) μ,
      f ∈ (Submodule.span ℝ S).topologicalClosure := by
  classical
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let GP : Set (Set α) :=
    insert Set.univ (insert (∅ : Set α) G)
  let S : Set (Lp ℝ (2 : ℝ≥0∞) μ) :=
    {v | ∃ (t : Set α) (ht : t ∈ GP)
      (htm : MeasurableSet t) (hμt : μ t ≠ ⊤),
      indicatorConstLp (2 : ℝ≥0∞) htm hμt (1 : ℝ) = v}
  let M : Submodule ℝ (Lp ℝ (2 : ℝ≥0∞) μ) :=
    (Submodule.span ℝ S).topologicalClosure
  change ∀ f : Lp ℝ (2 : ℝ≥0∞) μ, f ∈ M
  have hGenAlg : mα = MeasurableSpace.generateFrom (generateSetAlgebra G) := by
    simpa only [generateFrom_generateSetAlgebra_eq] using hGen
  have hDense : μ.MeasureDense (generateSetAlgebra G) :=
    Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite μ
      isSetAlgebra_generateSetAlgebra hGenAlg
  have hGPm : ∀ t : Set α, t ∈ GP → MeasurableSet t := by
    intro t ht
    simp only [GP, Set.mem_insert_iff] at ht
    rcases ht with hUniv | hEmpty | htG
    · rw [hUniv]
      exact MeasurableSet.univ
    · rw [hEmpty]
      exact MeasurableSet.empty
    · exact hGm t htG
  have hGPfinite : ∀ t : Set α, t ∈ GP → μ t ≠ ⊤ := by
    intro t _
    exact (measure_lt_top μ t).ne
  have hBoolOne (u : Set α) (hu : u ∈ generateSetAlgebra G)
      (hμu : μ u ≠ ⊤) :
      indicatorConstLp (2 : ℝ≥0∞)
        (hDense.measurable u hu) hμu (1 : ℝ) ∈ M := by
    have hPoint :=
      avram_wave4_p1_pi_system_boolean_indicator_span G hPi u hu
    have hLp :=
      avram_wave4_p1_pointwise_indicator_span_l2_lift
        μ GP hGPm hGPfinite u (hDense.measurable u hu) hμu hPoint
    exact (Submodule.le_topologicalClosure (Submodule.span ℝ S)) hLp
  let SB : Set (Lp ℝ (2 : ℝ≥0∞) μ) :=
    {indicatorConstLp (2 : ℝ≥0∞) (hDense.measurable u hu)
      hμu (1 : ℝ) | (u : Set α) (hu : u ∈ generateSetAlgebra G) (hμu : μ u ≠ ⊤)}
  have hSB : SB ⊆ (M : Set (Lp ℝ (2 : ℝ≥0∞) μ)) := by
    rintro v ⟨u, hu, hμu, rfl⟩
    exact hBoolOne u hu hμu
  have hIndicatorOne (t : Set α) (ht : MeasurableSet t)
      (hμt : μ t ≠ ⊤) :
      indicatorConstLp (2 : ℝ≥0∞) ht hμt (1 : ℝ) ∈ M := by
    have hApprox :
        indicatorConstLp (2 : ℝ≥0∞) ht hμt (1 : ℝ) ∈
        closure SB :=
      hDense.indicatorConstLp_subset_closure (2 : ℝ≥0∞) (1 : ℝ)
        ⟨t, ht, hμt, rfl⟩
    exact (Submodule.isClosed_topologicalClosure (Submodule.span ℝ S)).closure_subset
      ((closure_mono hSB) hApprox)
  have hConst (t : Set α) (ht : MeasurableSet t)
      (hμt : μ t ≠ ⊤) (c : ℝ) :
      indicatorConstLp (2 : ℝ≥0∞) ht hμt c =
        c • indicatorConstLp (2 : ℝ≥0∞) ht hμt (1 : ℝ) := by
    have hEq :
        t.indicator (fun _ => c) =
        c • t.indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : x ∈ t <;>
        simp [hx, Pi.smul_apply, smul_eq_mul]
    have hOneLp : MemLp (t.indicator (fun _ => (1 : ℝ)))
        (2 : ℝ≥0∞) μ :=
      memLp_indicator_const (2 : ℝ≥0∞) ht (1 : ℝ) (Or.inr hμt)
    have hCLp : MemLp (t.indicator (fun _ => c)) (2 : ℝ≥0∞) μ :=
      memLp_indicator_const (2 : ℝ≥0∞) ht c (Or.inr hμt)
    calc
      indicatorConstLp (2 : ℝ≥0∞) ht hμt c =
          (hOneLp.const_smul c).toLp
            (c • t.indicator (fun _ => (1 : ℝ))) := by
        exact MemLp.toLp_congr hCLp (hOneLp.const_smul c)
          (Filter.Eventually.of_forall (fun x => congrFun hEq x))
      _ = c • indicatorConstLp (2 : ℝ≥0∞) ht hμt (1 : ℝ) := by
        exact MemLp.toLp_const_smul c hOneLp
  apply Lp.induction (p := (2 : ℝ≥0∞)) (by norm_num)
    (motive := fun f => f ∈ M)
  · intro c t ht hμt
    have hOne := hIndicatorOne t ht hμt.ne
    rw [Lp.simpleFunc.coe_indicatorConst, hConst t ht hμt.ne c]
    exact M.smul_mem c hOne
  · intro f g hf hg hdisj hfm hgm
    exact M.add_mem hfm hgm
  · exact Submodule.isClosed_topologicalClosure _
