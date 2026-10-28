-- Prove2me | solution 1 for AvramDividend.Classical.chat03_two_sided_grid_stopped_scale_identity
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:10:41.268058+00:00
-- url     : https://prove2.me/submissions/9d08d25f-0a87-4cef-ae72-b8f159f06fc1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace S107ZP

/-- The zero process is a spectrally negative Lévy process (triplet `(0,0,0)`) on any probability
space and any filtration. -/
noncomputable def zeroLevy {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) : AvramDividend.Classical.SpectrallyNegativeLevy P 𝓕 where
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
    haveI : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
    exact (tendsto_nhds_unique h tendsto_const_nhds).symm.le
  adapted := fun _ => measurable_const
  indepIncrements := by
    intro s t _
    have : MeasurableSpace.comap (fun _ : Ω => (0 : ℝ) - 0) (inferInstance : MeasurableSpace ℝ) = ⊥ :=
      MeasurableSpace.comap_const _
    rw [this]
    exact ProbabilityTheory.indep_bot_left _
  stationaryIncrements := by
    intro s t _
    simp only [sub_self]
    exact ProbabilityTheory.IdentDistrib.refl aemeasurable_const
  laplace := by
    intro t θ _
    refine ⟨integrable_const _, ?_⟩
    simp [AvramDividend.Classical.laplaceExponent]

lemma X_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (t : ℝ≥0) (ω : Ω) : (zeroLevy P 𝓕).X t ω = 0 := rfl

lemma psi_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (θ : ℝ) : (zeroLevy P 𝓕).ψ θ = 0 := by
  simp [AvramDividend.Classical.SpectrallyNegativeLevy.ψ, AvramDividend.Classical.laplaceExponent,
    zeroLevy]

/-- For the zero process and `q > 0` the Laplace condition is vacuous. -/
lemma isScale {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (q : ℝ) (hq : 0 < q) :
    AvramDividend.Classical.IsScaleFunction (zeroLevy P 𝓕) q (fun y => max y 0) := by
  refine ⟨fun y hy => max_eq_right hy.le, fun y _ => le_max_right _ _,
    (continuous_id.max continuous_const).continuousOn,
    fun a _ b _ hab => max_le_max hab le_rfl, fun θ _ hθ => ?_⟩
  rw [psi_eq] at hθ; exact absurd hθ (not_lt.2 hq.le)

lemma generator_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (f : ℝ → ℝ) (x : ℝ) : (zeroLevy P 𝓕).generator f x = 0 := by
  simp [AvramDividend.Classical.SpectrallyNegativeLevy.generator, zeroLevy]

end S107ZP
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution : ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω),
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂P) * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x)) := by
  intro H
  let P : Measure PUnit.{1} := Measure.dirac PUnit.unit
  let 𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace PUnit.{1}) :=
    { seq := fun _ => ⊥, mono' := fun _ _ _ => le_rfl, le' := fun _ => bot_le }
  haveI : IsProbabilityMeasure P := by infer_instance

  let X := S107ZP.zeroLevy P 𝓕
  let H0 : Filtration ℕ (inferInstance : MeasurableSpace PUnit.{1}) :=
    { seq := fun _ => ⊥, mono' := fun _ _ _ => le_rfl, le' := fun _ => bot_le }
  have h := H X 1 one_pos (fun y => max y 0) (S107ZP.isScale P 𝓕 1 one_pos) (by simp) 1 (1 / 2) one_pos
    (by norm_num) (by norm_num) (fun _ => 0) (fun _ _ _ => le_rfl) rfl H0 (fun _ => rfl) 1 0 0 _ (fun _ => rfl)
  have hup : ∀ ω, twoSidedExitUpTime X (1 - 1 / 2) ω = ⊤ := by
    intro ω; unfold twoSidedExitUpTime
    refine iInf_eq_top.2 fun t => iInf_eq_top.2 fun ht => ?_
    simp only [X, S107ZP.X_eq] at ht; norm_num at ht
  simp only [hup, lt_self_iff_false, if_false, lintegral_zero, zero_mul] at h
  norm_num at h
