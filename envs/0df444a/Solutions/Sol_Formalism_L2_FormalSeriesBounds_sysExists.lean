-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.sysExists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:57:05.494818+00:00
-- url     : https://prove2.me/submissions/cf448d44-f644-4edc-aec9-652a4592f881

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (X : Cart V d I J) : SysExists X := by
  intro u hu hty hdet
  have hc : ∀ c, ∃ x, X.IsCurve (X.ty (Sum.inl c)) (u c) x := fun c => by
    obtain ⟨x, hx, h0, hp⟩ := X.t4 (X.ty (Sum.inl c)) (u c) (hu c) (fun k hk => hty c k hk)
    exact ⟨x, hx, h0, hp⟩
  choose cur hcur using hc
  exact ⟨⟨u, cur, hcur, hdet⟩, rfl⟩
end Formalism.L2.FormalSeriesBounds
