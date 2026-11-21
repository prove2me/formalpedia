-- Prove2me | solution 1 for FoundationsRL.PosteriorSampling.kl_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T03:34:06.102194+00:00
-- url     : https://prove2.me/submissions/91d275cb-4682-46d4-ac93-4514a05e66ff

import Mathlib

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

set_option maxHeartbeats 4000000

private lemma rnDeriv_compProd_same {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsFiniteMeasure μ] (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (h : ∀ᵐ x ∂μ, κ x ≪ η x) :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η] fun p => κ.rnDeriv η p.1 p.2 := by
  set f : α → β → ℝ≥0∞ := fun x y => ((κ.rnDeriv η x y).toNNReal : ℝ≥0∞) with hf
  have hrn_meas : Measurable fun p : α × β => κ.rnDeriv η p.1 p.2 := Kernel.measurable_rnDeriv κ η
  have hf_meas : Measurable (Function.uncurry f) :=
    hrn_meas.ennreal_toNNReal.coe_nnreal_ennreal
  have hf_ne : ∀ x y, f x y ≠ ∞ := fun x y => ENNReal.coe_ne_top
  haveI : IsSFiniteKernel (η.withDensity f) :=
    ProbabilityTheory.Kernel.IsSFiniteKernel.withDensity η hf_ne
  have hfibKer : ∀ᵐ x ∂μ, f x =ᵐ[η x] fun y => κ.rnDeriv η x y := by
    filter_upwards [h] with x hx
    filter_upwards [Kernel.rnDeriv_ne_top κ η (a := x)] with y hy
    simp only [hf]
    rw [ENNReal.coe_toNNReal hy]
  have hfibMeas : ∀ᵐ x ∂μ, f x =ᵐ[η x] (κ x).rnDeriv (η x) := by
    filter_upwards [hfibKer] with x h1
    exact h1.trans (Kernel.rnDeriv_eq_rnDeriv_measure (a := x))
  have hκ : η.withDensity f =ᵐ[μ] κ := by
    filter_upwards [h, hfibMeas] with x hx hfx
    rw [Kernel.withDensity_apply _ hf_meas]
    rw [withDensity_congr_ae hfx]
    exact Measure.withDensity_rnDeriv_eq (κ x) (η x) hx
  have h1 : μ ⊗ₘ (η.withDensity f) = μ ⊗ₘ κ := Measure.compProd_congr hκ
  have h2 : μ ⊗ₘ (η.withDensity f) = (μ ⊗ₘ η).withDensity (fun p => f p.1 p.2) :=
    Measure.compProd_withDensity hf_meas
  have h3 : (μ ⊗ₘ η).withDensity (fun p => f p.1 p.2) = μ ⊗ₘ κ := by
    rw [← h2, h1]
  have h4 := Measure.rnDeriv_withDensity (μ ⊗ₘ η) (f := fun p => f p.1 p.2) hf_meas
  rw [h3] at h4
  have h5 : ∀ᵐ p ∂(μ ⊗ₘ η), f p.1 p.2 = κ.rnDeriv η p.1 p.2 := by
    refine Measure.ae_compProd_of_ae_ae ?_ hfibKer
    exact measurableSet_eq_fun hf_meas hrn_meas
  filter_upwards [h4, h5] with p hp hp5
  rw [hp, hp5]

private lemma klDiv_compProd_same {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsFiniteMeasure μ] (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ x, klDiv (κ x) (η x) ∂μ := by
  haveI : IsFiniteMeasure (μ ⊗ₘ κ) := ⟨by rw [Measure.compProd_apply_univ]; exact measure_lt_top _ _⟩
  haveI : IsFiniteMeasure (μ ⊗ₘ η) := ⟨by rw [Measure.compProd_apply_univ]; exact measure_lt_top _ _⟩
  have hmeas : Measurable fun p : α × β =>
      ENNReal.ofReal (klFun ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p).toReal) :=
    (ENNReal.measurable_ofReal.comp
      (measurable_klFun.comp (Measure.measurable_rnDeriv _ _).ennreal_toReal))
  by_cases h : ∀ᵐ x ∂μ, κ x ≪ η x
  · have h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η := Measure.absolutelyContinuous_compProd_right_iff.mpr h
    rw [klDiv_eq_lintegral_klFun_of_ac h_ac]
    rw [Measure.lintegral_compProd hmeas]
    have hR : ∫⁻ x, klDiv (κ x) (η x) ∂μ
        = ∫⁻ x, (∫⁻ y, ENNReal.ofReal (klFun ((κ x).rnDeriv (η x) y).toReal) ∂(η x)) ∂μ :=
      lintegral_congr_ae (h.mono fun x hx => klDiv_eq_lintegral_klFun_of_ac hx)
    rw [hR]
    have hfib := Measure.ae_ae_of_ae_compProd (rnDeriv_compProd_same μ κ η h)
    refine lintegral_congr_ae ?_
    filter_upwards [hfib, h] with x hx hxac
    refine lintegral_congr_ae ?_
    filter_upwards [hx, Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := x)] with y hy hy2
    rw [hy, hy2]
  · have h_ac : ¬ (μ ⊗ₘ κ ≪ μ ⊗ₘ η) :=
      fun hc => h (Measure.absolutelyContinuous_compProd_right_iff.mp hc)
    rw [klDiv_of_not_ac h_ac]
    have hset : MeasurableSet {x | ¬ κ x ≪ η x} :=
      (Kernel.measurableSet_absolutelyContinuous κ η).compl
    have hne : μ {x | ¬ κ x ≪ η x} ≠ 0 := fun h0 => h (ae_iff.mpr h0)
    have h1 : ∫⁻ x in {x | ¬ κ x ≪ η x}, klDiv (κ x) (η x) ∂μ = ∞ := by
      rw [setLIntegral_congr_fun hset (fun x hx => klDiv_of_not_ac hx)]
      rw [setLIntegral_const]
      exact ENNReal.top_mul hne
    have h2 : ∫⁻ x in {x | ¬ κ x ≪ η x}, klDiv (κ x) (η x) ∂μ
        ≤ ∫⁻ x, klDiv (κ x) (η x) ∂μ := by
      simpa using lintegral_mono_set (μ := μ)
        (f := fun x => klDiv (κ x) (η x)) (Set.subset_univ {x : α | ¬ κ x ≪ η x})
    symm
    rw [eq_top_iff, ← h1]
    exact h2

theorem solution {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
    (ρ : Measure (X × Y)) [IsProbabilityMeasure ρ] :
    ∫⁻ x, klDiv (ρ.condKernel x) ρ.snd ∂ρ.fst =
      ∫⁻ y, klDiv ((ρ.map Prod.swap).condKernel y) ρ.fst ∂ρ.snd := by
  have hss : (Prod.swap ∘ Prod.swap : X × Y → X × Y) = id := by
    funext p; exact Prod.swap_swap p
  have hswap_kl : klDiv (ρ.map Prod.swap)
      ((ρ.fst.prod ρ.snd).map Prod.swap) = klDiv ρ (ρ.fst.prod ρ.snd) := by
    refine le_antisymm (klDiv_map_le _ _ measurable_swap) ?_
    have h := klDiv_map_le (μ := ρ.map Prod.swap) (ν := (ρ.fst.prod ρ.snd).map Prod.swap)
      (g := Prod.swap) measurable_swap
    have h1 : Measure.map Prod.swap (Measure.map Prod.swap ρ) = ρ := by
      rw [Measure.map_map measurable_swap measurable_swap, hss, Measure.map_id]
    have h2 : Measure.map Prod.swap (Measure.map Prod.swap (ρ.fst.prod ρ.snd))
        = ρ.fst.prod ρ.snd := by
      rw [Measure.map_map measurable_swap measurable_swap, hss, Measure.map_id]
    rw [h1, h2] at h
    exact h
  have hL : ∫⁻ x, klDiv (ρ.condKernel x) ρ.snd ∂ρ.fst = klDiv ρ (ρ.fst.prod ρ.snd) := by
    have hstep : ∫⁻ x, klDiv (ρ.condKernel x) ρ.snd ∂ρ.fst
        = ∫⁻ x, klDiv (ρ.condKernel x) ((Kernel.const X ρ.snd) x) ∂ρ.fst := by
      simp [Kernel.const_apply]
    rw [hstep, ← klDiv_compProd_same (μ := ρ.fst) (κ := ρ.condKernel)
      (η := Kernel.const X ρ.snd)]
    rw [Measure.IsCondKernel.disintegrate, Measure.compProd_const]
  have hR : ∫⁻ y, klDiv ((ρ.map Prod.swap).condKernel y) ρ.fst ∂ρ.snd
      = klDiv ρ (ρ.fst.prod ρ.snd) := by
    have hstep : ∫⁻ y, klDiv ((ρ.map Prod.swap).condKernel y) ρ.fst ∂ρ.snd
        = ∫⁻ y, klDiv ((ρ.map Prod.swap).condKernel y) ((Kernel.const Y ρ.fst) y) ∂ρ.snd := by
      simp [Kernel.const_apply]
    rw [hstep, ← klDiv_compProd_same (μ := ρ.snd) (κ := (ρ.map Prod.swap).condKernel)
      (η := Kernel.const Y ρ.fst)]
    have e1 : ρ.snd ⊗ₘ (ρ.map Prod.swap).condKernel = ρ.map Prod.swap := by
      rw [← Measure.fst_map_swap (ρ := ρ)]
      exact Measure.IsCondKernel.disintegrate (ρ := ρ.map Prod.swap)
    have e2 : ρ.snd ⊗ₘ Kernel.const Y ρ.fst = ρ.snd.prod ρ.fst := Measure.compProd_const
    rw [e1, e2, ← Measure.prod_swap (μ := ρ.fst) (ν := ρ.snd)]
    exact hswap_kl
  rw [hL, hR]
