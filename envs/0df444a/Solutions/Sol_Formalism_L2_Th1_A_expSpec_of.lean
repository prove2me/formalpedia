-- Prove2me | solution 1 for Formalism.L2.Th1.A.expSpec_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:00:51.394937+00:00
-- url     : https://prove2.me/submissions/cb1830e1-78d6-4994-accb-dae144976a34

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementZ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Theorems.Thm_P2M_Formalism_L2_Th1_A_subst_one__7b65fa7ad290
import Theorems.Thm_Formalism_L2_Th1_A_logSpec_of
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
    ExpSpec.{u} := by
  intro K _ _ W
  obtain ⟨hL0, hL1, hLd, -⟩ := logSpec_of hI hU K W
  obtain ⟨-, hfo, -⟩ := hU K W
  obtain ⟨hE0, hLE, hEL, hcoef, -⟩ := hC K (logSer W) hL0 (by rw [hL1]; exact isUnit_one)
  have hE0' : constantCoeff (expSer W) = 0 := hE0
  have hLE' : (logSer W).subst (expSer W) = X := hLE
  have hs : HasSubst (expSer W) := hasSubst_lemma hE0'
  refine ⟨hE0, ?_, hLE, hEL, ?_⟩
  · have h : coeff 1 (expSer W) * coeff 1 (logSer W) = 1 := hcoef
    rwa [hL1, mul_one] at h
  · have h1 := congrArg (derivative K) hLE'
    rw [derivative_subst hs, hLd, derivative_X] at h1
    have h2 : (fw W).subst (expSer W) * (om W).subst (expSer W) = 1 := by
      rw [← powerSeries_subst_mul_of_hasSubst hs, hfo, subst_one' hs]
    calc derivative K (expSer W)
        = ((fw W).subst (expSer W) * (om W).subst (expSer W)) * derivative K (expSer W) := by
          rw [h2, one_mul]
      _ = (fw W).subst (expSer W) := by rw [mul_assoc, h1, mul_one]
end Formalism.L2.Th1.A
