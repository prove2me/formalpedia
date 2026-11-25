-- Prove2me | solution 1 for Formalism.L2.Th1.A.logNeg_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:08:32.947871+00:00
-- url     : https://prove2.me/submissions/457fc326-f3a0-4b33-9e21-7fb7053cc5cc

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementZ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Theorems.Thm_P2M_Formalism_L2_Th1_A_subst_neg__662fad9e4892
import Theorems.Thm_Formalism_L2_Th1_A_subst_injective_of_leftInverse
import Theorems.Thm_Formalism_L2_Th1_A_logSpec_of
import Theorems.Thm_Formalism_L2_Th1_A_expSpec_of
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb

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
private theorem constantCoeff_powerSeries_subst_eq_zero {a f : R⟦X⟧} (ha0 : constantCoeff a = 0) (hf : constantCoeff f = 0) :
    constantCoeff (f.subst a) = 0 := by
  obtain ⟨h, rfl⟩ := (PowerSeries.X_dvd_iff).mpr hf
  rw [powerSeries_subst_mul_of_hasSubst (hasSubst_lemma ha0), PowerSeries.subst_X (hasSubst_lemma ha0), map_mul, ha0, zero_mul]
private theorem powerSeries_subst_subst_eq_subst_subst {a b f : R⟦X⟧} (ha : HasSubst a) (hb : HasSubst b) :
    PowerSeries.subst b (PowerSeries.subst a f : R⟦X⟧)
      = PowerSeries.subst (PowerSeries.subst b a : R⟦X⟧) f := by
  first
  | exact PowerSeries.subst_comp_subst_apply ha hb f
  | exact (PowerSeries.subst_comp_subst_apply ha hb f).symm
  | rw [PowerSeries.subst_comp_subst_apply ha hb]
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
theorem _root_.solution (hI : IntegSpec.{u}) (hC : CompInvSpec.{u}) (hU : UnitSpec.{u})
    (hS : ISerSpec.{u}) : LogNeg.{u} := by
  intro K _ _ W
  obtain ⟨hL0, -, hLd, -⟩ := logSpec_of hI hU K W
  obtain ⟨hE0, -, hLE, hEL, -⟩ := expSpec_of hI hC hU K W
  obtain ⟨hi0, -, -, -, -, -, -, hiom⟩ := hS K W
  have hsi : HasSubst (iSer W) := hasSubst_lemma hi0
  have hsE : HasSubst (expSer W) := hasSubst_lemma hE0
  have hL' : (logSer W).subst (iSer W) = -logSer W := by
    obtain ⟨-, -, huniq⟩ := hI K (-om W)
    have e1 := huniq ((logSer W).subst (iSer W)) (constantCoeff_powerSeries_subst_eq_zero hi0 hL0)
      (by rw [derivative_subst hsi, hLd, hiom])
    have e2 := huniq (-logSer W) (by rw [map_neg, hL0, neg_zero]) (by rw [map_neg, hLd])
    rw [e1, e2]
  refine ⟨hL', ?_⟩
  have hnX0 : constantCoeff (-X : K⟦X⟧) = 0 := by simp
  have hsn : HasSubst (-X : K⟦X⟧) := hasSubst_lemma hnX0
  apply subst_injective_of_leftInverse (l := logSer W) (e := expSer W) (hasSubst_lemma hL0)
    (hasSubst_lemma (constantCoeff_powerSeries_subst_eq_zero hnX0 hE0)) (hasSubst_lemma (constantCoeff_powerSeries_subst_eq_zero hE0 hi0)) hEL
  rw [← powerSeries_subst_subst_eq_subst_subst hsE hsn, hLE, PowerSeries.subst_X hsn, ← powerSeries_subst_subst_eq_subst_subst hsi hsE, hL',
    subst_neg' hsE, hLE]
end Formalism.L2.Th1.A
