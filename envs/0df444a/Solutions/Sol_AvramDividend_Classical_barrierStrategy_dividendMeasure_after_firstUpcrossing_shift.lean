-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_dividendMeasure_after_firstUpcrossing_shift
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T09:52:48.668016+00:00
-- url     : https://prove2.me/submissions/9640db89-b035-46e5-8883-f4556a7e97b2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

open ProbabilityTheory Function

private lemma measurable_top_bool {α : Type*} [MeasurableSpace α] (f : Bool → α) :
    @Measurable Bool α ⊤ _ f := fun _ _ => trivial

private noncomputable def topFiltration :
    Filtration ℝ≥0 (⊤ : MeasurableSpace Bool) where
  seq _ := ⊤
  mono' _ _ _ := le_rfl
  le' _ := le_rfl

private def shiftPath (t : ℝ≥0) (ω : Bool) : ℝ :=
  if ω then max 0 ((t : ℝ) - 1) else 0

private lemma shiftPath_continuous (ω : Bool) :
    Continuous (fun s : ℝ≥0 => shiftPath s ω) := by
  cases ω
  · exact continuous_const
  · change Continuous (fun s : ℝ≥0 => max (0 : ℝ) ((s : ℝ) - 1))
    exact continuous_const.max (NNReal.continuous_coe.sub continuous_const)

private lemma shiftPath_mono_true :
    Monotone (fun s : ℝ≥0 => shiftPath s true) := by
  intro a b hab
  simp only [shiftPath, ↓reduceIte]
  exact max_le_max le_rfl (sub_le_sub_right (NNReal.coe_le_coe.mpr hab) 1)

private lemma shiftPath_nonneg (t : ℝ≥0) (ω : Bool) :
    0 ≤ shiftPath t ω := by
  cases ω <;> simp [shiftPath]

private lemma nhdsWithin_Iio_neBot_of_pos {t : ℝ≥0} (ht : 0 < t) :
    (𝓝[<] t).NeBot := by
  apply mem_closure_iff_nhdsWithin_neBot.mp
  have hne : (Iio t).Nonempty := ⟨0, ht⟩
  rw [closure_Iio' hne]
  exact le_refl t

private noncomputable def shiftLevy :
    SpectrallyNegativeLevy (Measure.dirac false) topFiltration where
  X := shiftPath
  c := 0
  σ := 0
  ν := 0
  isProbability := inferInstance
  σ_nonneg := le_rfl
  ν_Ici := by simp
  ν_integrable := by simp
  X_zero ω := by
    cases ω <;> simp [shiftPath]
  rightCont ω t := (shiftPath_continuous ω).continuousAt.continuousWithinAt
  leftLim ω t _ := ⟨shiftPath t ω, (shiftPath_continuous ω).continuousAt.continuousWithinAt⟩
  noPosJumps ω t l ht hl := by
    have : (𝓝[<] t).NeBot := nhdsWithin_Iio_neBot_of_pos ht
    have hlim : Tendsto (fun s => shiftPath s ω) (𝓝[<] t) (𝓝 (shiftPath t ω)) :=
      (shiftPath_continuous ω).continuousAt.continuousWithinAt
    rw [tendsto_nhds_unique hl hlim]
  adapted _ := measurable_top_bool _
  indepIncrements _ _ _ := by
    rw [ProbabilityTheory.Indep_iff]
    intro t₁ t₂ _ _
    have hm1 : MeasurableSet t₁ := trivial
    have hm2 : MeasurableSet t₂ := trivial
    simp [Measure.dirac_apply' _ hm1, Measure.dirac_apply' _ hm2,
      Measure.dirac_apply' _ (hm1.inter hm2), Set.indicator]
    by_cases h1 : false ∈ t₁ <;> by_cases h2 : false ∈ t₂ <;> simp [h1, h2]
  stationaryIncrements s t _ := by
    refine ⟨(measurable_top_bool _).aemeasurable, (measurable_top_bool _).aemeasurable, ?_⟩
    apply Measure.map_congr
    rw [Filter.EventuallyEq, ae_dirac_iff]
    · simp [shiftPath]
    · trivial
  laplace t θ _ := by
    refine ⟨Integrable.of_finite, ?_⟩
    rw [integral_dirac]
    simp [shiftPath, laplaceExponent]

private lemma shiftPath_csSup_eq (t : ℝ≥0) :
    (⨆ s : Icc (0 : ℝ≥0) t, shiftPath s true) = shiftPath t true := by
  have : Nonempty (Icc (0 : ℝ≥0) t) := ⟨⟨0, left_mem_Icc.mpr bot_le⟩⟩
  apply le_antisymm
  · refine ciSup_le ?_
    rintro ⟨s, hs⟩
    exact shiftPath_mono_true hs.2
  · have hbdd : BddAbove (range (fun s : Icc (0 : ℝ≥0) t => shiftPath s.1 true)) := by
      refine ⟨shiftPath t true, ?_⟩
      rintro _ ⟨⟨s, hs⟩, rfl⟩
      exact shiftPath_mono_true hs.2
    exact le_ciSup hbdd ⟨t, right_mem_Icc.mpr bot_le⟩

private lemma barrier_eq_shiftPath (t : ℝ≥0) :
    barrierStrategy shiftLevy 0 0 t true = shiftPath t true := by
  unfold barrierStrategy shiftLevy
  split_ifs with ht
  · subst ht
    simp [shiftPath]
  · simp only [sub_zero, zero_add]
    rw [shiftPath_csSup_eq]
    exact max_eq_right (shiftPath_nonneg t true)

private lemma runningSup_eq_shiftPath (t : ℝ≥0) :
    runningSup shiftLevy t true = shiftPath t true := by
  unfold runningSup maxZero shiftLevy
  have hEq : (fun s : Icc (0 : ℝ≥0) t => max (shiftPath s.1 true) 0) =
      (fun s : Icc (0 : ℝ≥0) t => shiftPath s.1 true) := by
    ext ⟨s, _⟩
    exact max_eq_left (shiftPath_nonneg s true)
  rw [hEq, shiftPath_csSup_eq]

private def realRamp (t : ℝ) : ℝ :=
  max 0 (t - 1)

private lemma shiftPath_toNNReal_eq_realRamp (t : ℝ) :
    shiftPath t.toNNReal true = realRamp t := by
  simp only [shiftPath, ↓reduceIte, realRamp]
  by_cases ht : 0 ≤ t
  · rw [Real.coe_toNNReal t ht]
  · have ht' : t < 0 := lt_of_not_ge ht
    rw [Real.toNNReal_of_nonpos ht'.le]
    have h1 : (0 : ℝ) - 1 ≤ 0 := by norm_num
    have h2 : t - 1 ≤ 0 := by linarith
    rw [NNReal.coe_zero, max_eq_left h1, max_eq_left h2]

private lemma realRamp_mono : Monotone realRamp := by
  intro a b hab
  exact max_le_max le_rfl (sub_le_sub_right hab 1)

private lemma realRamp_continuous : Continuous realRamp :=
  continuous_const.max (continuous_id.sub continuous_const)

private lemma realRamp_stieltjes_apply (x : ℝ) :
    realRamp_mono.stieltjesFunction x = realRamp x := by
  rw [Monotone.stieltjesFunction_eq]
  exact realRamp_continuous.continuousWithinAt.rightLim_eq

private lemma barrier_toNNReal_eq :
    (fun t : ℝ => barrierStrategy shiftLevy 0 0 t.toNNReal true) = realRamp := by
  ext t
  rw [barrier_eq_shiftPath, shiftPath_toNNReal_eq_realRamp]

private lemma runningSup_toNNReal_eq :
    (fun t : ℝ => runningSup shiftLevy t.toNNReal true) = realRamp := by
  ext t
  rw [runningSup_eq_shiftPath, shiftPath_toNNReal_eq_realRamp]

private lemma dividendMeasure_barrier_eq :
    dividendMeasure (barrierStrategy shiftLevy 0 0) true =
      realRamp_mono.stieltjesFunction.measure := by
  unfold dividendMeasure
  simp only [barrier_toNNReal_eq, realRamp_mono, ↓reduceDIte]

private lemma dividendMeasure_runningSup_eq :
    dividendMeasure (runningSup shiftLevy) true =
      realRamp_mono.stieltjesFunction.measure := by
  unfold dividendMeasure
  simp only [runningSup_toNNReal_eq, realRamp_mono, ↓reduceDIte]

private lemma shiftLevy_upcrossing_eq_one :
    ((1 : ℝ≥0) : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : (0 : ℝ) - 0 < shiftLevy.X t true), (t : ℝ≥0∞)) := by
  symm
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add ?_
    intro ε hε _
    have hlt : (0 : ℝ) - 0 < shiftLevy.X (1 + ε) true := by
      change (0 : ℝ) - 0 < max 0 (((1 + ε : ℝ≥0) : ℝ) - 1)
      have hpos : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
      have hsub : ((1 + ε : ℝ≥0) : ℝ) - 1 = (ε : ℝ) := by
        push_cast
        ring
      rw [hsub, max_eq_right hpos.le]
      linarith
    have hle : (⨅ (t : ℝ≥0) (_ : (0 : ℝ) - 0 < shiftLevy.X t true), (t : ℝ≥0∞)) ≤
        ((1 + ε : ℝ≥0) : ℝ≥0∞) :=
      le_trans (iInf_le _ (1 + ε)) (iInf_le _ hlt)
    simpa [ENNReal.coe_add] using hle
  · refine le_iInf₂ ?_
    intro t ht
    change (0 : ℝ) - 0 < max 0 ((t : ℝ) - 1) at ht
    by_contra hlt
    have hle : (t : ℝ≥0∞) ≤ (1 : ℝ≥0) := (lt_of_not_ge hlt).le
    have ht1 : (t : ℝ) ≤ 1 := by exact_mod_cast hle
    have hmax : max (0 : ℝ) ((t : ℝ) - 1) = 0 := max_eq_left (by linarith)
    linarith

theorem solution :
    ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
      {𝓕 : Filtration ℝ≥0 mΩ}
      (X : SpectrallyNegativeLevy P 𝓕)
      (x a : ℝ) (_hxa : x ≤ a) (ω : Ω) (u : ℝ≥0)
      (_hu : (u : ℝ≥0∞) =
        (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))
      (_hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u)),
      ∀ (t : ℝ≥0),
        (dividendMeasure (barrierStrategy X x a) ω) (Ioc u (u + t)) =
          (dividendMeasure (runningSup X) ω) (Ioc 0 t)) := by
  intro hAll
  have hbdd : BddAbove ((fun r : ℝ≥0 => shiftLevy.X r true) '' Set.Icc 0 1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    change max (0 : ℝ) ((r : ℝ) - 1) ≤ 0
    have hr1 : (r : ℝ) ≤ 1 := by exact_mod_cast hr.2
    linarith [max_eq_left (show (r : ℝ) - 1 ≤ 0 by linarith)]
  have hEq := hAll shiftLevy 0 0 le_rfl true 1 shiftLevy_upcrossing_eq_one hbdd 1
  rw [dividendMeasure_barrier_eq, dividendMeasure_runningSup_eq] at hEq
  have hLHS :
      realRamp_mono.stieltjesFunction.measure
        (Ioc ((1 : ℝ≥0) : ℝ) (((1 : ℝ≥0) : ℝ) + ((1 : ℝ≥0) : ℝ))) = 1 := by
    rw [StieltjesFunction.measure_Ioc, realRamp_stieltjes_apply, realRamp_stieltjes_apply]
    unfold realRamp
    norm_num
  have hRHS :
      realRamp_mono.stieltjesFunction.measure (Ioc (0 : ℝ) ((1 : ℝ≥0) : ℝ)) = 0 := by
    rw [StieltjesFunction.measure_Ioc, realRamp_stieltjes_apply, realRamp_stieltjes_apply]
    unfold realRamp
    norm_num
  have hEq' :
      realRamp_mono.stieltjesFunction.measure
        (Ioc ((1 : ℝ≥0) : ℝ) (((1 : ℝ≥0) : ℝ) + ((1 : ℝ≥0) : ℝ))) =
      realRamp_mono.stieltjesFunction.measure (Ioc (0 : ℝ) ((1 : ℝ≥0) : ℝ)) := by
    simpa [NNReal.coe_add] using hEq
  rw [hLHS, hRHS] at hEq'
  exact one_ne_zero hEq'
