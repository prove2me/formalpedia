-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_separated_countable_jump_drop_budget
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T06:13:45.975611+00:00
-- url     : https://prove2.me/submissions/f3b6d82c-7591-422d-abf8-482a28447718

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace LVDis

def F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Unit) :=
  ⟨fun _ => inferInstance, monotone_const, fun _ => le_rfl⟩

noncomputable def L : SpectrallyNegativeLevy (Measure.dirac ()) F where
  X := fun _ _ => 0
  c := 0
  σ := 0
  ν := 0
  isProbability := inferInstance
  σ_nonneg := le_rfl
  ν_Ici := by simp
  ν_integrable := by simp
  X_zero := fun _ => rfl
  rightCont := fun _ _ => continuousWithinAt_const
  leftLim := fun _ _ _ => ⟨0, tendsto_const_nhds⟩
  noPosJumps := by
    intro ω t l ht h
    have : (𝓝[<] t).NeBot := nhdsWithin_Iio_self_neBot' ⟨0, ht⟩
    exact le_of_eq (tendsto_nhds_unique tendsto_const_nhds h)
  adapted := fun _ => measurable_const
  indepIncrements := by
    intro s t _
    simp only [sub_self]
    rw [MeasurableSpace.comap_const]
    exact indep_bot_left _
  stationaryIncrements := by
    intro s t _
    simp only [sub_self]
    exact IdentDistrib.refl aemeasurable_const
  laplace := by
    intro t θ _
    simp [laplaceExponent]

noncomputable def D : ℝ≥0 → Unit → ℝ := fun t _ => if t = 0 then 0 else 1 / 2

lemma rightLimit_D (t : ℝ≥0) : rightLimit D t () = 1 / 2 := by
  unfold rightLimit
  have : ∀ s : Ioi t, D s () = 1 / 2 := by
    intro s
    have hs : (s : ℝ≥0) ≠ 0 := ne_of_gt (lt_of_le_of_lt (by positivity : (0:ℝ≥0) ≤ t) s.2)
    simp [D, hs]
  simp only [this]
  have : Nonempty (Ioi t) := ⟨⟨t + 1, by simp⟩⟩
  exact ciInf_const

lemma adm : IsAdmissibleLe L 1 ⊤ D := by
  refine ⟨⟨⟨fun _ => by simp [D], ?_, ?_, fun _ => measurable_const⟩, ?_⟩, fun _ _ _ => le_top⟩
  · intro ω a b hab
    simp only [D]
    by_cases hb : b = 0
    · subst hb; have : a = 0 := le_antisymm hab bot_le; simp [this]
    · by_cases ha : a = 0 <;> simp [ha, hb]
  · intro ω t
    by_cases ht : t = 0
    · subst ht
      have : Iic (0 : ℝ≥0) = {0} := by ext s; simp
      rw [this]; exact continuousWithinAt_singleton
    · refine ContinuousWithinAt.congr_of_eventuallyEq (f := fun _ => (1 / 2 : ℝ)) continuousWithinAt_const ?_ ?_
      · have : ∀ᶠ s in 𝓝[Iic t] t, s ≠ 0 :=
          nhdsWithin_le_nhds (isOpen_ne.mem_nhds ht)
        filter_upwards [this] with s hs
        simp [D, hs]
      · simp [D, ht]
  · intro ω t _
    cases ω
    rw [rightLimit_D]
    simp only [riskProcess, L, D]
    split_ifs <;> norm_num

end LVDis

open LVDis in
theorem solution : ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxC : ENNReal.ofReal x ≤ C)
    (ω : Ω) (S : Set ℝ) (hCountable : S.Countable)
    (hNonneg : ∀ s ∈ S, 0 ≤ s)
    (hActive : ∀ s ∈ S,
      s.toNNReal = 0 ∨ (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω),
    (∑' s : S, ENNReal.ofReal (Real.exp (-(q * (s : ℝ))) *
      (w (riskProcess X x D (s : ℝ).toNNReal ω) -
       w (riskProcess X x D (s : ℝ).toNNReal ω -
         (rightLimit D (s : ℝ).toNNReal ω - D (s : ℝ).toNNReal ω))))) ≤
      ENNReal.ofReal (w x)) := by
  intro h
  have hw : ContDiff ℝ 2 (fun y : ℝ => y - 10) := contDiff_id.sub contDiff_const
  have key := h (Ω := Unit) (P := Measure.dirac ()) (𝓕 := F) L 1 0 (fun y => y - 10) ⊤
    (continuous_id.sub continuous_const).continuousOn
    ⟨fun _ => hw.contDiffOn, fun _ => (hw.of_le (by norm_num)).contDiffOn⟩
    (by
      intro y _ _
      refine ⟨?_, ?_⟩
      · simp only [SpectrallyNegativeLevy.GeneratorIntegrable, L]
        rw [IntegrableOn, Measure.restrict_zero]; exact integrable_zero_measure
      · simp [SpectrallyNegativeLevy.generator, L])
    (by
      intro y _ _
      simp)
    LVDis.D adm le_top () {0} (countable_singleton 0) (by simp) (by simp)
  have k2 := (ENNReal.le_tsum (⟨0, rfl⟩ : ({0} : Set ℝ))).trans key
  simp only [Real.toNNReal_zero, rightLimit_D] at k2
  norm_num [LVDis.D] at k2
  rw [ENNReal.ofReal_of_nonpos (by norm_num : (-9 : ℝ) ≤ 0), nonpos_iff_eq_zero,
    ENNReal.ofReal_eq_zero] at k2
  norm_num at k2
