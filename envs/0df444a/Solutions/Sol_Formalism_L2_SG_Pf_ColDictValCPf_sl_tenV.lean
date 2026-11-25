-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.sl_tenV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:57:25.34069+00:00
-- url     : https://prove2.me/submissions/f895cdb9-e5b4-4c04-a568-3dab76b8e0bc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWLine
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylLeDual
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighestWeightVectorUnique
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_sl_rename_self
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_sl_rename_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution (τ₀ : ι) (x : ι × Fin n × Fin n → ℂ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    sl τ₀ x (tenV f) = C (∏ σ ∈ Finset.univ.erase τ₀, eval (fun q => x (σ, q)) (f σ)) * f τ₀ := by
  rw [tenV, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ₀), sl_rename_self, mul_comm,
    map_prod]
  congr 1
  refine Finset.prod_congr rfl fun σ hσ => ?_
  exact sl_rename_ne τ₀ σ (Finset.ne_of_mem_erase hσ) x (f σ)
end Formalism.L2.SG.Pf.ColDictValCPf
