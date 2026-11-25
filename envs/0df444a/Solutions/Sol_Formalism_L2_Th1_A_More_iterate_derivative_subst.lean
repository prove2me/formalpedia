-- Prove2me | solution 1 for Formalism.L2.Th1.A.More.iterate_derivative_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:28:59.441174+00:00
-- url     : https://prove2.me/submissions/1078e6d8-f1fc-465e-9e13-fea0de5b5a0a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementM
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ChainRuleFormalGroupVar
import Theorems.Thm_Formalism_L2_Th1_A_chainZ_of
import Theorems.Thm_Formalism_L2_Th1_A_composition_inverse_spec
import Theorems.Thm_Formalism_L2_Th1_A_integration_spec
import Theorems.Thm_Formalism_L2_Th1_A_invariant_differential_units


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open More
open Formalism.L2.Th1.A.More
namespace Formalism.L2.Th1.A.More
theorem _root_.solution {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)
    (n : ℕ) (f : K⟦X⟧) :
    (derivative K)^[n] (f.subst (expSer W)) = ((D W)^[n] f).subst (expSer W) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    first
    | exact chainZ_of integration_spec composition_inverse_spec invariant_differential_units K W _
    | exact chainZ_of integration_spec.{u} composition_inverse_spec.{u} invariant_differential_units.{u} K W _
end Formalism.L2.Th1.A.More
