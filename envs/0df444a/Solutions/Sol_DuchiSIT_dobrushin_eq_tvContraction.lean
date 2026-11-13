-- Prove2me | solution 1 for DuchiSIT.dobrushin_eq_tvContraction
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T18:28:15.725548+00:00
-- url     : https://prove2.me/submissions/37c68792-1fe0-40ff-aebf-8ba9925498b8

import Theorems.Thm_DuchiSIT_tv_probability_bounds
import Theorems.Thm_DuchiSIT_tv_channel_le
import Theorems.Thm_DuchiSIT_dobrushin_le_tvContraction
import Definitions.Def_DuchiSIT_TVContractionCoefficient
set_option autoImplicit false
open MeasureTheory ProbabilityTheory

open DuchiSIT


theorem solution {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (K : Kernel X Y) [IsMarkovKernel K] :
    dobrushin K = tvContraction K := by
  classical
  apply le_antisymm (dobrushin_le_tvContraction K)
  have hd0 : 0 ≤ dobrushin K := by
    apply Real.sSup_nonneg
    rintro r ⟨x, y, rfl⟩
    exact (DuchiSIT.tv_probability_bounds (K x) (K y)).2.1
  apply Real.sSup_le _ hd0
  rintro r ⟨μ, ν, hne, rfl⟩
  have hdp : 0 < MarkovChainCLT.tvDist (μ : Measure X) (ν : Measure X) := by
    apply lt_of_le_of_ne (DuchiSIT.tv_probability_bounds (μ : Measure X) (ν : Measure X)).2.1
    intro hz
    apply hne
    apply ProbabilityMeasure.toMeasure_injective
    exact (DuchiSIT.tv_probability_bounds (μ : Measure X) (ν : Measure X)).2.2.2.mp hz.symm
  exact (div_le_iff₀ hdp).mpr (tv_channel_le K μ ν)
