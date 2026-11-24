-- Prove2me | solution 1 for FockRL.fi_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:40:58.951911+00:00
-- url     : https://prove2.me/submissions/f7ccb41e-6756-4857-a266-260fd2c211b2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
import Theorems.Thm_FockRL_fi_zero_left
import Theorems.Thm_FockRL_fi_add_left

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
theorem _root_.solution {ι : Type} (hL : FockLinL) (t : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (∑ i ∈ t, f i) Q = ∑ i ∈ t, FockH1Action.fockInner (f i) Q := by
  classical
  induction t using Finset.induction_on
  · simp only [Finset.sum_empty, fi_zero_left]
  · rename_i a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fi_add_left hL, ih]
end FockRL
