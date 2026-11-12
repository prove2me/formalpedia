-- Prove2me | solution 1 for CondDRO.proposition_2_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T01:57:43.019264+00:00
-- url     : https://prove2.me/submissions/626e6868-6d26-4561-b664-47dae47fc10a

import Definitions.Def_CondDRO_FinitePartition
import Definitions.Def_CondDRO_condDRF
import Definitions.Def_CondDRO_condRM
import Definitions.Def_CondDRO_mixture
import Theorems.Thm_CondDRO_mixture_isProbability_and_cell
import Theorems.Thm_CondDRO_inducedSets_mixture
import Theorems.Thm_CondDRO_condRM_inducedSets_eq_condDRF

open MeasureTheory

open CondDRO in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {I : Type*} [Fintype I]
    (ϖ : FinitePartition Ω I) (A : I → Set (Measure Ω))
    (hA_ne : ∀ i, (A i).Nonempty)
    (hA_prob : ∀ i, ∀ Q ∈ A i, IsProbabilityMeasure Q)
    (hA_supp : ∀ i, ∀ Q ∈ A i, Q (ϖ.cell i)ᶜ = 0)
    (ν : I → ℝ) (hν_pos : ∀ i, 0 < ν i) (hν_sum : ∑ i, ν i = 1)
    (Z : Ω → ℝ) (hZ_meas : Measurable Z) (hZ_int : ∀ i, ∀ Q ∈ A i, Integrable Z Q) :
    condRM A Z = condDRF (mixture A ν) ϖ Z := by
  classical
  have hmix := mixture_isProbability_and_cell ϖ A hA_prob hA_supp ν hν_pos hν_sum
  have hind := inducedSets_mixture ϖ A hA_ne hA_prob hA_supp ν hν_pos hν_sum
  have hA_eq : A = inducedSets (mixture A ν) ϖ := funext fun i => (hind i).symm
  have hM_prob : ∀ Q ∈ mixture A ν, IsProbabilityMeasure Q := fun Q hQ => (hmix Q hQ).1
  have hM_assum : ∀ i, ∃ Q ∈ mixture A ν, Q (ϖ.cell i) ≠ 0 := by
    choose q₀ hq₀ using hA_ne
    let Q₀ : Measure Ω := ∑ j, ENNReal.ofReal (ν j) • q₀ j
    have hQ₀_mem : Q₀ ∈ mixture A ν := ⟨q₀, hq₀, rfl⟩
    intro i
    refine ⟨Q₀, hQ₀_mem, ?_⟩
    rw [(hmix Q₀ hQ₀_mem).2 i]
    exact (ENNReal.ofReal_pos.mpr (hν_pos i)).ne'
  have hZ_mix_int : ∀ Q ∈ mixture A ν, Integrable Z Q := by
    rintro Q ⟨q, hq, rfl⟩
    refine integrable_finsetSum_measure.mpr ?_
    intro j _
    exact (hZ_int j (q j) (hq j)).smul_measure ENNReal.ofReal_ne_top
  exact (congrArg (fun B => condRM B Z) hA_eq).trans
    (condRM_inducedSets_eq_condDRF ϖ (mixture A ν) hM_prob hM_assum Z hZ_meas hZ_mix_int)
