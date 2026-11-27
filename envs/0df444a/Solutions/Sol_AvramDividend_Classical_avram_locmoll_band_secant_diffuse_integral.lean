-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_secant_diffuse_integral
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:22:03.85047+00:00
-- url     : https://prove2.me/submissions/79159e27-7c94-4c6c-9a0f-9c513158b9f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_zero_drop_measurable
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_eligible_zero_drop_atomless
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_measurableSet
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_all_source_pathwise_atomless_prejump_for_path_dependent_measure
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_controlled_left_prestate_explicit_source_eq
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (H : ℝ≥0)
    (g : ℝ → ℝ) :
    let S : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Iic (H : ℝ)
    let U : Set ℝ := {t : ℝ | rightLimit D t.toNNReal ω = D t.toNNReal ω}
    let μ := (dividendMeasure D ω).restrict S
    let Q : ℝ → ℝ → ℝ := fun a b => if a = b then deriv g a else (g a - g b) / (a - b)
    let F : ℝ → ℝ := fun t => Real.exp (-(q * t)) *
      (1 - Q (riskProcess X x D t.toNNReal ω)
        (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω))
    (∫ t in U, F t ∂μ) =
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioc (0 : ℝ) (H : ℝ),
        Real.exp (-(q * t)) *
          (1 - deriv g (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t.toNNReal))
        ∂((dividendMeasure D ω).restrict U) := by 
  dsimp only
  let S : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Iic (H : ℝ)
  let U : Set ℝ := {t : ℝ | rightLimit D t.toNNReal ω = D t.toNNReal ω}
  let ν := ((dividendMeasure D ω).restrict S).restrict U
  have hS : MeasurableSet S := (avram_p4_d_dividend_original_paymentTimes_measurableSet _).inter measurableSet_Iic
  have hU : MeasurableSet U := avram_locmoll_band_zero_drop_measurable D hD ω
  haveI : NullSingletonClass ν := avram_locmoll_band_eligible_zero_drop_atomless X x q D hD ω H
  have hsu : ν = (dividendMeasure D ω).restrict (U ∩ S) := Measure.restrict_restrict hU
  have hSae : ∀ᵐ t ∂ν, t ∈ S := by
    rw [hsu]
    exact (ae_restrict_mem (hU.inter hS)).mono (fun _ ht => ht.2)
  have hUae : ∀ᵐ t ∂ν, t ∈ U := ae_restrict_mem hU
  have hn : ∀ᵐ t : ℝ ∂ν, t ≠ 0 := by
    rw [ae_iff]
    simpa using (measure_singleton (μ := ν) (0 : ℝ))
  have hp : ∀ᵐ t ∂ν, 0 < t := by
    filter_upwards [hSae, hn] with t ht hne
    exact lt_of_le_of_ne ht.1.1 (Ne.symm hne)
  have he := avram_wave4_04b_all_source_pathwise_atomless_prejump_for_path_dependent_measure X x D hD ω ν
  let L : ℝ → ℝ := fun t => Real.exp (-(q * t)) *
    (1 - deriv g (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t.toNNReal))
  calc
    _ = ∫ t, L t ∂ν := by
      apply integral_congr_ae
      filter_upwards [hUae, hp, he] with t hu ht he
      have hd : rightLimit D t.toNNReal ω = D t.toNNReal ω := hu
      obtain ⟨l, hl⟩ := X.leftLim ω t.toNNReal (Real.toNNReal_pos.mpr ht)
      letI : (𝓝[<] t.toNNReal).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, Real.toNNReal_pos.mpr ht⟩
      have hll := leftLim_eq_of_tendsto hl
      have hY := avram_p3_2_original_controlled_left_prestate_explicit_source_eq X x D hD ω
        t.toNNReal (Real.toNNReal_pos.mpr ht) l hl
      have hpre := he ht
      rw [hll, hd] at hpre
      have hpost : riskProcess X x D t.toNNReal ω =
          x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω := by simp only [riskProcess, hd]
      change Real.exp _ * (1 - (if _ then _ else _)) = L t
      rw [if_pos hpost]
      dsimp only [L]
      rw [hY, ← hpre]
    _ = _ := by
      have hν : ν.restrict (Ioi (0 : ℝ)) = ν := Measure.restrict_eq_self_of_ae_mem hp
      have hW : MeasurableSet (paymentTimes (ruinTime X x D ω) ∩ Ioc (0 : ℝ) (H : ℝ)) :=
        (avram_p4_d_dividend_original_paymentTimes_measurableSet _).inter measurableSet_Ioc
      rw [← hν, hsu, Measure.restrict_restrict measurableSet_Ioi, Measure.restrict_restrict hW]
      have hs : Ioi (0 : ℝ) ∩ (U ∩ S) =
          (paymentTimes (ruinTime X x D ω) ∩ Ioc (0 : ℝ) (H : ℝ)) ∩ U := by
        ext t
        simp only [S, mem_inter_iff, mem_Ioi, mem_Iic, mem_Ioc]
        tauto
      rw [hs]
