-- Prove2me | solution 1 for Formalism.L2.Th1.A.chainZ_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:08:30.683638+00:00
-- url     : https://prove2.me/submissions/2d1ebf80-79ac-4419-98bb-ddee2d441e5e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementZ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Theorems.Thm_Formalism_L2_Th1_A_expSpec_of
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open PowerSeries
universe u
noncomputable section
namespace Formalism.L2.Th1.A
section SlopeTestRemainingChoices
variable {R : Type u} [CommRing R]
private theorem hasSubst_lemma {a : R⟦X⟧} (h : constantCoeff a = 0) : HasSubst a := by
  first
  | exact HasSubst.of_constantCoeff_zero' h
  | exact HasSubst.of_constantCoeff_zero h
  | exact PowerSeries.HasSubst.of_constantCoeff_zero' h
private theorem powerSeries_subst_mul_of_hasSubst {a : R⟦X⟧} (ha : HasSubst a) (f g : R⟦X⟧) :
    (f * g).subst a = f.subst a * g.subst a := by
  first
  | exact PowerSeries.subst_mul ha f g
  | (rw [← PowerSeries.coe_substAlgHom ha]; exact map_mul _ f g)
end SlopeTestRemainingChoices
end Formalism.L2.Th1.A
end
end

set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
namespace Formalism.L2.Th1.A
theorem _root_.solution (hI : IntegSpec.{u}) (hC : CompInvSpec.{u}) (hU : UnitSpec.{u}) :
    ChainZ.{u} := by
  intro K _ _ W f
  obtain ⟨hE0, -, -, -, hEd⟩ := expSpec_of hI hC hU K W
  have hs : HasSubst (expSer W) := hasSubst_lemma hE0
  rw [derivative_subst hs, hEd]
  simp only [D, Derivation.smul_apply, smul_eq_mul]
  rw [powerSeries_subst_mul_of_hasSubst hs, mul_comm]
end Formalism.L2.Th1.A
