-- Prove2me | solution 1 for AvramDividend.Classical.tauceti_original_levy_stronglyProgressive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T18:58:05.209092+00:00
-- url     : https://prove2.me/submissions/434bbccf-f27f-4964-afd5-68776e409a36

/- Copyright (c) 2026 The Tau Ceti contributors. Apache-2.0.
   Adapted from TauCeti/Probability/Process/Progressive.lean
   MeasureTheory.StronglyAdapted.isStronglyProgressive_of_isRightContinuous.
   Avram-specific specialised statement. -/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set TopologicalSpace AvramDividend.Classical
open scoped NNReal Topology



/-- A source-faithful port of the TauCeti capped right-grid progressivity theorem.
The proof constructs strongly measurable sampled approximations and uses right continuity. -/
private theorem tauCetiStronglyProgressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → ℝ}
    (hu : StronglyAdapted 𝓕 u)
    (hc : ∀ ω (t : ℝ≥0),
      ContinuousWithinAt (fun s => u s ω) (Ici t) t) :
    IsStronglyProgressive 𝓕 u := by
  let rightSample (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
    (⌈(t : ℝ) * (n + 1)⌉₊ : ℝ≥0) / (n + 1)
  have le_rightSample (n : ℕ) (t : ℝ≥0) : t ≤ rightSample n t := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ≥0) < n + 1)).mpr
    exact_mod_cast Nat.le_ceil ((t : ℝ) * (n + 1))
  have tendsto_rightSample (t : ℝ≥0) :
      Tendsto (fun n => rightSample n t) atTop (𝓝 t) := by
    apply NNReal.tendsto_coe.mp
    simpa only [Function.comp_def, rightSample, NNReal.coe_div, NNReal.coe_natCast,
      NNReal.coe_add, NNReal.coe_one, Nat.cast_add, Nat.cast_one] using
      (tendsto_nat_ceil_mul_div_atTop t.coe_nonneg).comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
  intro T
  let : MeasurableSpace Ω := 𝓕 T
  have hm (n : ℕ) : StronglyMeasurable
      (fun p : Iic T × Ω => u (min (rightSample n p.1) T) p.2) := by
    have hs : StronglyMeasurable (Function.uncurry
        (fun k : ℕ => u (min ((k : ℝ≥0) / (n + 1)) T))) := by
      apply Measurable.stronglyMeasurable
      apply measurable_from_prod_countable_right
      intro k
      change Measurable (u (min ((k : ℝ≥0) / (n + 1)) T))
      exact ((hu _).mono (𝓕.mono (min_le_right _ _))).measurable
    have hmap : Measurable (fun p : Iic T × Ω =>
        (⌈((p.1 : ℝ≥0) : ℝ) * (n + 1)⌉₊, p.2)) :=
      ((NNReal.continuous_coe.measurable.comp
        (measurable_subtype_coe.comp measurable_fst)).mul_const
          (n + 1 : ℝ)).nat_ceil.prodMk measurable_snd
    simpa only [Function.uncurry_def, Function.comp_def, rightSample] using
      hs.comp_measurable hmap
  apply stronglyMeasurable_of_tendsto atTop hm
  apply tendsto_pi_nhds.mpr
  intro p
  apply (hc p.2 (p.1 : ℝ≥0)).tendsto.comp
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, .of_forall fun n => ?_⟩
  · have h := (tendsto_rightSample p.1).min (tendsto_const_nhds (x := T))
    rw [min_eq_left (α := ℝ≥0) p.1.property] at h
    exact h
  · exact le_min (le_rightSample n p.1) p.1.property



theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    IsStronglyProgressive 𝓕 X.X := by
  apply tauCetiStronglyProgressive (stronglyAdapted_iff_adapted.mpr X.adapted)
  exact X.rightCont
