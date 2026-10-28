-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_paymentTimes_after_firstUpcrossing_eq_shifted
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:03:19.676049+00:00
-- url     : https://prove2.me/submissions/b6f52cae-b0f0-4d94-92a6-8eb5ffa4372e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

lemma S107PT.sup_Icc (t : ℝ≥0) : (⨆ s : Icc (0 : ℝ≥0) t, ((s : ℝ≥0) : ℝ)) = t := by
  haveI : Nonempty (Icc (0 : ℝ≥0) t) := ⟨⟨0, le_rfl, bot_le⟩⟩
  have hb : BddAbove (Set.range fun s : Icc (0 : ℝ≥0) t => ((s : ℝ≥0) : ℝ)) :=
    ⟨t, by rintro _ ⟨s, rfl⟩; exact_mod_cast s.2.2⟩
  refine le_antisymm (ciSup_le fun s => by exact_mod_cast s.2.2) ?_
  exact le_ciSup_of_le hb ⟨t, bot_le, le_rfl⟩ le_rfl

theorem solution : ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u))
    (hdraw : ∀ t : ℝ≥0,
      riskProcess X x (barrierStrategy X x a) (u + t) ω < 0 ↔
        a < runningSup X (u + t) ω - X.X (u + t) ω),
    {t : ℝ≥0 | u < t ∧
        (t : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω} =
      {t : ℝ≥0 | u < t ∧
        (t : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω ∧
        a < runningSup X t ω - X.X t ω}) := by
  intro H
  let P : Measure PUnit.{1} := Measure.dirac PUnit.unit
  let 𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace PUnit.{1}) :=
    { seq := fun _ => ⊥, mono' := fun _ _ _ => le_rfl, le' := fun _ => bot_le }
  -- the pure unit drift X_t = t
  let X : SpectrallyNegativeLevy P 𝓕 :=
    { X := fun t _ => (t : ℝ)
      c := 1
      σ := 0
      ν := 0
      isProbability := by infer_instance
      σ_nonneg := le_rfl
      ν_Ici := by simp
      ν_integrable := by simp
      X_zero := fun _ => rfl
      rightCont := fun _ _ => NNReal.continuous_coe.continuousWithinAt
      leftLim := fun _ t _ => ⟨t, (NNReal.continuous_coe.tendsto t).mono_left nhdsWithin_le_nhds⟩
      noPosJumps := by
        intro ω t l ht h
        haveI : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
        exact (tendsto_nhds_unique ((NNReal.continuous_coe.tendsto t).mono_left
          nhdsWithin_le_nhds) h).le
      adapted := fun _ => measurable_const
      indepIncrements := fun _ _ _ => ProbabilityTheory.indep_bot_right _
      stationaryIncrements := by
        intro s t hst
        have : (fun _ : PUnit.{1} => ((t : ℝ≥0) : ℝ) - (s : ℝ)) = fun _ => (((t - s : ℝ≥0)) : ℝ) := by
          funext _; rw [NNReal.coe_sub hst]
        show ProbabilityTheory.IdentDistrib (fun _ : PUnit.{1} => ((t : ℝ≥0) : ℝ) - (s : ℝ))
          (fun _ => (((t - s : ℝ≥0)) : ℝ)) P P
        rw [this]
        exact ProbabilityTheory.IdentDistrib.refl aemeasurable_const
      laplace := by
        intro t θ _
        refine ⟨integrable_const _, ?_⟩
        simp [laplaceExponent, P, mul_comm] }
  have hXX : ∀ t ω, X.X t ω = (t : ℝ) := fun _ _ => rfl
  have hS : ∀ t ω, runningSup X t ω = t := by
    intro t ω
    unfold runningSup
    simp only [hXX, maxZero, max_eq_left (NNReal.coe_nonneg _)]
    exact S107PT.sup_Icc t
  have hD : ∀ t ω, barrierStrategy X 0 0 t ω = t := by
    intro t ω
    unfold barrierStrategy
    split_ifs with h
    · rw [h]; rfl
    · simp only [hXX, sub_self, zero_add, S107PT.sup_Icc]
      exact max_eq_right (NNReal.coe_nonneg _)
  have hR : ∀ t ω, riskProcess X 0 (barrierStrategy X 0 0) t ω = 0 := by
    intro t ω; simp only [riskProcess, hD, hXX]; ring
  have hruin : ruinTime X 0 (barrierStrategy X 0 0) PUnit.unit = ⊤ := by
    unfold ruinTime
    refine iInf_eq_top.2 fun t => iInf_eq_top.2 fun h => ?_
    rw [hR] at h; exact absurd h (lt_irrefl 0)
  have hu : ((0 : ℝ≥0) : ℝ≥0∞) = ⨅ (t : ℝ≥0) (_ : (0 : ℝ) - 0 < X.X t PUnit.unit), (t : ℝ≥0∞) := by
    rw [ENNReal.coe_zero]
    symm
    by_contra hne
    have hpos : 0 < ⨅ (t : ℝ≥0) (_ : (0 : ℝ) - 0 < X.X t PUnit.unit), (t : ℝ≥0∞) :=
      pos_iff_ne_zero.2 hne
    obtain ⟨r, _, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hpos
    have hr0 : 0 < r := ENNReal.ofReal_pos.1 hr1
    have := iInf₂_le (f := fun (t : ℝ≥0) (_ : (0 : ℝ) - 0 < X.X t PUnit.unit) => (t : ℝ≥0∞))
      r.toNNReal (by rw [hXX, sub_self, Real.coe_toNNReal _ hr0.le]; exact hr0)
    exact absurd (this.trans_lt hr2) (lt_irrefl _)
  have hb : BddAbove ((fun r : ℝ≥0 => X.X r PUnit.unit) '' Set.Icc 0 0) :=
    (isCompact_Icc.image NNReal.continuous_coe).bddAbove
  have hdraw : ∀ t : ℝ≥0,
      riskProcess X 0 (barrierStrategy X 0 0) (0 + t) PUnit.unit < 0 ↔
        (0 : ℝ) < runningSup X (0 + t) PUnit.unit - X.X (0 + t) PUnit.unit := by
    intro t
    rw [hR, hS, hXX, sub_self]
  have key := H X 0 0 le_rfl PUnit.unit 0 hu hb hdraw
  have h1 : (1 : ℝ≥0) ∈ {t : ℝ≥0 | 0 < t ∧
      (t : ℝ≥0∞) < ruinTime X 0 (barrierStrategy X 0 0) PUnit.unit} := by
    refine ⟨one_pos, ?_⟩
    rw [hruin]; exact ENNReal.coe_lt_top
  rw [key] at h1
  have := h1.2.2
  rw [hS, hXX, sub_self] at this
  exact lt_irrefl _ this
