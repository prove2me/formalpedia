-- Prove2me | solution 1 for DistCov.Indep.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T22:29:56.475964+00:00
-- url     : https://prove2.me/submissions/3b5d398a-d247-447a-a324-27811bbf6e37

import Theorems.Thm_DistCov_Indep_eq_3_4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open DistCov.Indep
namespace DistCovBaryInj

lemma negType_of_embedding {X H : Type*} [MetricSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ϕ : X → H) (hϕ : IsNegTypeEmbedding ϕ) : NegType X := by
  intro n x α hα
  have he := inner_sum_smul_sum_smul_of_sum_eq_zero
    (fun i => ϕ (x i)) hα (fun i => ϕ (x i)) hα
  have hd (i j : Fin n) := hϕ (x i) (x j)
  simp_rw [← sq, ← hd] at he
  have hp : 0 ≤ inner ℝ (∑ i, α i • ϕ (x i)) (∑ i, α i • ϕ (x i)) := real_inner_self_nonneg
  linarith

lemma energy_zero_iff_bary_eq {X H : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (ϕ : X → H) (hϕ : IsNegTypeEmbedding ϕ)
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : FiniteFirstMoment μ) (hν : FiniteFirstMoment ν)
    (hmass : μ Set.univ = ν Set.univ) :
    Ddiff μ ν = 0 ↔ bary ϕ μ = bary ϕ ν := by
  rw [eq_3_4 ϕ hϕ μ ν hμ hν hmass]
  constructor
  · intro h
    have hn : ‖bary ϕ μ - bary ϕ ν‖^2 = 0 := by linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
  · intro h
    simp only [h, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]

end DistCovBaryInj

theorem solution {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (ϕ : X → H) (hϕ : IsNegTypeEmbedding ϕ) :
    StrongNegType X ↔ BaryInjProb ϕ := by
  constructor
  · intro h
    intro μ ν hμ hν hm hn hb
    letI := hμ
    letI := hν
    exact h.2 μ ν hμ hν hm hn
      ((DistCovBaryInj.energy_zero_iff_bary_eq ϕ hϕ μ ν hm hn (by simp)).mpr hb)
  · intro h
    refine ⟨DistCovBaryInj.negType_of_embedding ϕ hϕ, ?_⟩
    intro μ ν hμ hν hm hn hD
    letI := hμ
    letI := hν
    exact h μ ν hμ hν hm hn
      ((DistCovBaryInj.energy_zero_iff_bary_eq ϕ hϕ μ ν hm hn (by simp)).mp hD)

#print axioms solution
