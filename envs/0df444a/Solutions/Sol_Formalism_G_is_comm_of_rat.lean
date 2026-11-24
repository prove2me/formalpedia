-- Prove2me | solution 1 for Formalism.G.is_comm_of_rat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:49.873152+00:00
-- url     : https://prove2.me/submissions/7383b7e7-074a-4baa-a301-e7b6cfc308cf

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
import Theorems.Thm_Formalism_G_LogP_hX0
import Theorems.Thm_Formalism_G_LogP_hX1
import Theorems.Thm_Formalism_G_LogP_logF_isLog
import Theorems.Thm_Formalism_G_LogP_psubst_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
namespace Formalism.G
theorem _root_.solution : Formalism.G.IsCommOfRat := by
  intro R _ _ F
  refine ⟨?_⟩
  have hf := Formalism.G.LogP.logF_isLog F
  set f := Formalism.G.LogP.logF F
  have hFc : constantCoeff F.toPowerSeries = 0 := F.zero_constantCoeff
  have hc : MvPowerSeries.HasSubst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0] :=
    Formalism.G.LogP.hs2 (by simp) (by simp)
  have hFs : constantCoeff (F.toPowerSeries.subst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0]) = 0 := by
    rw [Formalism.G.LogP.constantCoeff_subst_of_zero _ (fun i => by fin_cases i <;> simp), hFc]
  have h1 : f.subst (F.toPowerSeries.subst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0]) =
      f.subst F.toPowerSeries := by
    rw [← Formalism.G.LogP.psubst_subst f hFc hc, hf.2.2, subst_add hc, Formalism.G.atX, Formalism.G.atY,
      Formalism.G.LogP.psubst_subst f Formalism.G.LogP.hX0 hc, Formalism.G.LogP.psubst_subst f Formalism.G.LogP.hX1 hc,
      subst_X hc, subst_X hc]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [add_comm]
  exact (Formalism.G.LogP.psubst_injective hf.1 hf.2.1 hFs hFc h1).symm
end Formalism.G
