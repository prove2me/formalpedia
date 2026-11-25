-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.valCIrr_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:27:10.730964+00:00
-- url     : https://prove2.me/submissions/18860bfb-5655-41fa-adcd-3a98cab699e0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ColDictValC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf Matrix MvPolynomial
open scoped ComplexOrder
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution (hT : Transfer) (hD : DivClosed) (hH : HiEx) (hU : Uniq) (hG : Gen) : ValCIrr := by
  unfold ValCIrr
  intro ι _ n G hGd lam W hW hne hst
  classical
  obtain ⟨M, hMle, hMne, hMst, hMW⟩ := hT ι n G hGd lam W hW hne hst
  have hdiv := hD ι n G hGd M hMst
  obtain ⟨Q, hQM, hQ0, hQk⟩ := hH ι n M hdiv hMne
  obtain ⟨c, hc⟩ := hU ι n lam Q (hMle hQM) hQk
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hQ0 (by simpa using hc)
  have htM : tenHW lam ∈ M := by
    have hcQ : c⁻¹ • Q ∈ M := M.smul_mem _ hQM
    rwa [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at hcQ
  exact hMW (hG ι n lam M hdiv htM)
end Formalism.L2.SG.Pf.ColDictValCPf
