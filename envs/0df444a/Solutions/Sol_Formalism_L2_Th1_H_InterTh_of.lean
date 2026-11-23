-- Prove2me | solution 1 for Formalism.L2.Th1.H.InterTh_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:05.255314+00:00
-- url     : https://prove2.me/submissions/c588dd09-477c-4fac-9a31-e1b0cad68e01

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Theorems.Thm_Formalism_L2_Th1_H_cosetRepsExist
import Theorems.Thm_Formalism_L2_Th1_H_InterReps_of
import Theorems.Thm_Formalism_L2_Th1_H_InterFixed_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution (h : SemiHom) (ha : OpUAnalytic) : InterTh := by
  intro V _ _ _ H hH Λ₁ Λ₂ α hα hne F hF
  classical
  have hF' : AnalyticOnNhd ℂ F Set.univ ∧ F ∈ fixedBy H α Λ₁ := hF
  obtain ⟨S, hS⟩ := (cosetRepsExist V Λ₁ Λ₂ hne).1
  have hsum : ∀ T : Finset V,
      AnalyticOnNhd ℂ (fun v => ∑ x ∈ T, α x * opU H x F v) Set.univ := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · intro w _
      simp only [Finset.sum_empty]
      exact analyticAt_const
    · intro a T haT ih w hw
      simp only [Finset.sum_insert haT]
      exact (analyticAt_const.mul (ha V H a F hF'.1 w hw)).add (ih w hw)
  have hrep := InterReps_of h V H hH Λ₁ Λ₂ α hα F hF'.2
  have hG : inter H α Λ₁ Λ₂ F
      = fun v => ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹ * sumU H α S F v :=
    funext (hrep S hS)
  show AnalyticOnNhd ℂ (inter H α Λ₁ Λ₂ F) Set.univ ∧
    inter H α Λ₁ Λ₂ F ∈ fixedBy H α Λ₂
  refine ⟨?_, InterFixed_of h V H hH Λ₁ Λ₂ α hα hne F hF'.2⟩
  rw [hG]
  intro w hw
  exact analyticAt_const.mul (hsum S w hw)
end Formalism.L2.Th1.H
