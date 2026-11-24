-- Prove2me | solution 1 for Formalism.LT.PadicP.isHom_of_subst_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:33:47.707632+00:00
-- url     : https://prove2.me/submissions/a2276cca-5282-487a-bd77-7dccb81416b3

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_IsHomOfSubstEqSmul
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_substInjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.LT Formalism.LT.PadicP
open Formalism.G
namespace Formalism.LT.PadicP
theorem _root_.solution {R : Type} [CommRing R] (F : FormalGroup R) (f e : PowerSeries R)
    (c : R) (hlog : IsLog F f) (he0 : constantCoeff e = 0) (hfe : f.subst e = c • f) :
    IsHom F F e := by
  obtain ⟨h0, h1, hF⟩ := hlog
  refine ⟨he0, ?_⟩
  have hFS : PowerSeries.HasSubst F.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have heS : PowerSeries.HasSubst e := PowerSeries.HasSubst.of_constantCoeff_zero' he0
  have hcc : ∀ t : Fin 2, MvPowerSeries.constantCoeff
      (e.subst (MvPowerSeries.X t : MvPowerSeries (Fin 2) R)) = 0 := fun t =>
    PowerSeries.constantCoeff_subst_eq_zero (by simp) e he0
  have hv : MvPowerSeries.HasSubst ![atX e, atY e] := LogP.hs2 (hcc 0) (hcc 1)
  have hat : ∀ t : Fin 2, f.subst (e.subst (MvPowerSeries.X t : MvPowerSeries (Fin 2) R)) =
      c • f.subst (MvPowerSeries.X t : MvPowerSeries (Fin 2) R) := by
    intro t
    rw [← PowerSeries.subst_comp_subst_apply heS (PowerSeries.HasSubst.X t), hfe,
      PowerSeries.subst_smul (PowerSeries.HasSubst.X t)]
  apply substInjective R (Fin 2) f _ _ h0 h1
  · exact PowerSeries.constantCoeff_subst_eq_zero F.zero_constantCoeff e he0
  · rw [LogP.constantCoeff_subst_of_zero F.toPowerSeries (fun i => by fin_cases i <;> simp [hcc]),
      F.zero_constantCoeff]
  · rw [← PowerSeries.subst_comp_subst_apply heS hFS, hfe, PowerSeries.subst_smul hFS, hF,
      ← LogP.psubst_subst f F.zero_constantCoeff hv, hF, MvPowerSeries.subst_add hv]
    rw [LogP.psubst_subst f (by simp) hv, LogP.psubst_subst f (by simp) hv,
      MvPowerSeries.subst_X hv, MvPowerSeries.subst_X hv]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, atX, atY]
    rw [hat 0, hat 1, smul_add]
end Formalism.LT.PadicP
