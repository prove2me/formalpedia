-- Prove2me | solution 1 for DerivativeChainContinuation.sixth9_prefix_actual_root_family
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:02:58.131097+00:00
-- url     : https://prove2.me/submissions/ac4d086b-281c-4959-901a-065757e8a722

import Mathlib
import Definitions.Def_DerivativeChainContinuation_Sixth9InversePolynomial
import Definitions.Def_DerivativeChainContinuation_Sixth9PData
import Definitions.Def_DerivativeChainContinuation_SixthPhysicalNormalization
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_sixth9_actual_root_family
import Theorems.Thm_DerivativeChainContinuation_sixth_actual_rows_rescale
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate





theorem sixth_prefix_radius_positive : 0<sixthPrefixRadius := by
  unfold sixthPrefixRadius
  positivity























end DerivativeChainContinuation

theorem solution :
    ∃ W : ℂ → ℂ,
      DifferentiableOn ℂ W (Metric.ball 0 2) ∧
      (∀ t : ℂ,‖t‖≤2 → ‖W t-sixth9P t‖≤1/100000000 ∧ sixth9G t (W t)=0) ∧
      (∀ x : ℝ,|x|≤2 → (W (x:ℂ)).im=0) ∧
      ∀ z : ℂ,z≠0 → ‖z⁻¹‖^2≤2 →
        let β:=((sixthPrefixRadius:ℂ)^3/136)*(z^3*W ((z⁻¹)^2))
        (derivative^[9] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval
          ((sixthPrefixRadius:ℂ)*z)=0 := by
  obtain ⟨W,hhol,hW,hreal,hroot⟩:=sixth9_actual_root_family
  refine ⟨W,hhol,hW,hreal,?_⟩
  intro z hz hdom
  dsimp only
  apply (sixth_actual_rows_rescale _ z 9).mpr
  have hr : (sixthPrefixRadius:ℂ)≠0 := by exact_mod_cast sixth_prefix_radius_positive.ne'
  have hβ : sixthPhysicalParameter (((sixthPrefixRadius:ℂ)^3/136)*(z^3*W ((z⁻¹)^2)))=
      z^3*W ((z⁻¹)^2) := by
    unfold sixthPhysicalParameter
    field_simp
  rw [hβ]
  exact hroot z hz hdom
