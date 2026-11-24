-- Prove2me | solution 1 for FockRL.fi_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:07.9898+00:00
-- url     : https://prove2.me/submissions/fa92f2f8-d208-4299-9b40-aad1ce45f9d9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
import Theorems.Thm_FockRL_fi_zero_right
import Theorems.Thm_FockRL_fi_add_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open FockRL
variable {p q r s : ℕ}
variable {σ : Type}
namespace FockRL
theorem _root_.solution {ι : Type} (hR : FockLinR) (t : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (P : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (∑ i ∈ t, f i) = ∑ i ∈ t, FockH1Action.fockInner P (f i) := by
  classical
  induction t using Finset.induction_on
  · simp only [Finset.sum_empty, fi_zero_right]
  · rename_i a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fi_add_right hR, ih]
end FockRL
