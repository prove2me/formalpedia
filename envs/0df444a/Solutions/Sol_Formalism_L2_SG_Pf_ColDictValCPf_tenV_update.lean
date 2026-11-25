-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.tenV_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:54:34.394717+00:00
-- url     : https://prove2.me/submissions/8e90a284-0b2d-460a-856a-31fd3dd64d9f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWLine
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylLeDual
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighestWeightVectorUnique

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
theorem _root_.solution (f : ι → MvPolynomial (Fin n × Fin n) ℂ) (τ : ι)
    (p : MvPolynomial (Fin n × Fin n) ℂ) :
    tenV (Function.update f τ p) =
      rename (Prod.mk τ) p * ∏ σ ∈ Finset.univ.erase τ, rename (Prod.mk σ) (f σ) := by
  rw [tenV, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun σ hσ => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hσ)]
end Formalism.L2.SG.Pf.ColDictValCPf
