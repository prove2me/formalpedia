-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.ortho
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:12.272275+00:00
-- url     : https://prove2.me/submissions/5a3d31ed-a016-4f44-b21b-ceae418297dc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinA
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_trace_sum
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_tr_ed_eb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
open NumberField Module FractionalIdeal
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]
open scoped Classical
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
theorem _root_.solution (σ τ : E →+* ℂ) :
    ∑ i, σ (ed E i) * τ (integralBasis E i) = if σ = τ then 1 else 0 := by
  classical
  let P : Matrix (E →+* ℂ) (Free.ChooseBasisIndex ℤ (𝓞 E)) ℂ := Matrix.of fun ρ i => ρ (integralBasis E i)
  let Q : Matrix (Free.ChooseBasisIndex ℤ (𝓞 E)) (E →+* ℂ) ℂ := Matrix.of fun i ρ => ρ (ed E i)
  have hQP : Q * P = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Q, P, Matrix.of_apply, Matrix.one_apply]
    simp_rw [← map_mul]
    rw [← trace_sum, tr_ed_eb]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card (E →+* ℂ) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, NumberField.Embeddings.card]
  have hPQ : P * Q = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).mp hQP
  have h := congrFun (congrFun hPQ τ) σ
  simp only [Matrix.mul_apply, P, Q, Matrix.of_apply, Matrix.one_apply] at h
  convert h using 1
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · exact if_congr eq_comm rfl rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
