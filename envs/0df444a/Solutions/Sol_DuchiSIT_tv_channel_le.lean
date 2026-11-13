-- Prove2me | solution 1 for DuchiSIT.tv_channel_le
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T18:23:51.743409+00:00
-- url     : https://prove2.me/submissions/2cdf6280-066f-457e-ad69-b676751e56ea

import Theorems.Thm_DuchiSIT_tv_probability_bounds
import Theorems.Thm_MarkovChainCLT_abs_integral_sub_le_tvDist_of_bounded
import Mathlib.Tactic.Positivity
import Definitions.Def_DuchiSIT_DobrushinCoefficient
set_option autoImplicit false
open MeasureTheory ProbabilityTheory

open DuchiSIT


theorem solution {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (K : Kernel X Y) [IsMarkovKernel K]
    (μ ν : ProbabilityMeasure X) :
    MarkovChainCLT.tvDist (channel K μ : Measure Y) (channel K ν : Measure Y) ≤
      dobrushin K * MarkovChainCLT.tvDist (μ : Measure X) (ν : Measure X) := by
  classical
  letI : Nonempty X := μ.nonempty
  have hb (x y : X) := DuchiSIT.tv_probability_bounds (K x) (K y)
  have hd0 : 0 ≤ dobrushin K := by
    apply Real.sSup_nonneg
    rintro r ⟨x, y, rfl⟩
    exact (hb x y).2.1
  have hdb : BddAbove {r : ℝ | ∃ x y : X, r = MarkovChainCLT.tvDist (K x) (K y)} := by
    refine ⟨1, ?_⟩
    rintro r ⟨x, y, rfl⟩
    exact (hb x y).2.2.1
  have hrow (x y : X) : MarkovChainCLT.tvDist (K x) (K y) ≤ dobrushin K :=
    le_csSup hdb ⟨x, y, rfl⟩
  have htv0 := (DuchiSIT.tv_probability_bounds (μ : Measure X) (ν : Measure X)).2.1
  apply Real.sSup_le _ (mul_nonneg hd0 htv0)
  rintro r ⟨A, hA, rfl⟩
  let g : X → ℝ := fun x => ((K x) A).toReal
  have hgm : Measurable g := (Kernel.measurable_coe K hA).ennreal_toReal
  have hg0 (x : X) : 0 ≤ g x := ENNReal.toReal_nonneg
  have hg1 (x : X) : g x ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one (μ := K x) (s := A))
  have hpair (x y : X) : |g x - g y| ≤ dobrushin K :=
    ((hb x y).1 A hA).trans (hrow x y)
  let c : ℝ := sInf (Set.range g)
  have hcB : BddBelow (Set.range g) := ⟨0, by rintro _ ⟨x, rfl⟩; exact hg0 x⟩
  have hcl (x : X) : c ≤ g x := csInf_le hcB ⟨x, rfl⟩
  have hcu (x : X) : g x - dobrushin K ≤ c := by
    apply le_csInf (Set.range_nonempty g)
    rintro _ ⟨y, rfl⟩
    linarith [(abs_le.mp (hpair x y)).2]
  let a : ℝ := c + dobrushin K / 2
  have hbound (x : X) : |g x - a| ≤ dobrushin K / 2 := by
    rw [abs_le]
    dsimp [a]
    constructor <;> linarith [hcl x, hcu x]
  have hint (ρ : Measure X) [IsProbabilityMeasure ρ] : Integrable g ρ := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const (1 : ℝ)).mono ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one, abs_of_nonneg (hg0 x)]
    exact hg1 x
  have hshift (ρ : Measure X) [IsProbabilityMeasure ρ] :
      (∫ x, (g x - a) ∂ρ) = (∫ x, g x ∂ρ) - a := by
    rw [integral_sub (hint ρ) (integrable_const a), integral_const]
    simp [Measure.real]
  have hkey := MarkovChainCLT.abs_integral_sub_le_tvDist_of_bounded
    (μ : Measure X) (ν : Measure X) (fun x => g x - a) (hgm.sub_const a)
    (dobrushin K / 2) (by positivity) hbound
  rw [hshift, hshift] at hkey
  have hval (ρ : Measure X) [IsProbabilityMeasure ρ] :
      ((K ∘ₘ ρ) A).toReal = ∫ x, g x ∂ρ := by
    rw [Measure.bind_apply hA (Kernel.aemeasurable _)]
    refine (integral_toReal (Kernel.measurable_coe K hA).aemeasurable ?_).symm
    filter_upwards with x
    exact measure_lt_top _ _
  change |((K ∘ₘ (μ : Measure X)) A).toReal - ((K ∘ₘ (ν : Measure X)) A).toReal| ≤ _
  rw [hval, hval]
  have heq : (∫ x, g x ∂(μ : Measure X)) - a - ((∫ x, g x ∂(ν : Measure X)) - a) =
      (∫ x, g x ∂(μ : Measure X)) - (∫ x, g x ∂(ν : Measure X)) := by ring
  rw [heq] at hkey
  convert hkey using 1 <;> ring
