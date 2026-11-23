-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.euler_leibniz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:36.080214+00:00
-- url     : https://prove2.me/submissions/1e01ce2d-909d-44a5-bf0a-1df4696cd5db

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx1_euler_support

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
theorem _root_.solution : Formalism.FourierDecayAlt.M.EulerLeibniz := by
  intro r v f g
  have hc : ∀ (v : Var r) (h : Fn r) (γ : Expo r), (euler v h).coeff γ = ((ofLex γ v : ℤ) : ℂ) * h.coeff γ :=
    fun _ _ _ => rfl
  ext γ
  rw [hc, HahnSeries.coeff_add, HahnSeries.coeff_mul_left' f.isPWO_support (Mx1.euler_support v f),
    HahnSeries.coeff_mul_right' g.isPWO_support (Mx1.euler_support v g), HahnSeries.coeff_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  obtain ⟨-, -, hsum⟩ := Finset.mem_addAntidiagonal.1 hij
  rw [hc, hc, ← hsum, ofLex_add, Pi.add_apply]
  push_cast
  ring
end Formalism.FourierDecayAlt.P
