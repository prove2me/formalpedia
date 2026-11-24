-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.euler_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:56.875815+00:00
-- url     : https://prove2.me/submissions/abf1c188-9c24-4d5b-b0d3-68d2b23ad988

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Mx1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.M.EulerCoord := by
  intro r v w z
  have hc : ∀ (v : Var r) (h : Fn r) (γ : Expo r), (euler v h).coeff γ = ((ofLex γ v : ℤ) : ℂ) * h.coeff γ :=
    fun _ _ _ => rfl
  constructor
  · ext γ
    rw [hc]
    by_cases hvw : v = w
    · subst hvw
      rw [if_pos rfl]
      simp only [coord, HahnSeries.coeff_single]
      split_ifs with hγ
      · subst hγ
        simp
      · simp
    · rw [if_neg hvw]
      simp only [coord, HahnSeries.coeff_single, HahnSeries.coeff_zero]
      split_ifs with hγ
      · subst hγ
        simp [Pi.single_apply, hvw]
      · simp
  · ext γ
    rw [hc]
    simp only [HahnSeries.algebraMap_apply, HahnSeries.C_apply, HahnSeries.coeff_single,
      HahnSeries.coeff_zero, Algebra.algebraMap_self, RingHom.id_apply]
    split_ifs with hγ
    · subst hγ
      simp
      left
      rfl
    · simp
end Formalism.FourierDecayAlt.P
