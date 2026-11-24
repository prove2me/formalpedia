-- Prove2me | solution 1 for Formalism.GM.TM.support_zpsmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:17.864646+00:00
-- url     : https://prove2.me/submissions/b21f8ccb-6b09-4ad5-b23f-3494beef6657

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.GM.TM
theorem _root_.solution (a : ℤ_[p]) (ha : a ≠ 0) (x : MvPolynomial σ ℚ_[p]) : (a • x).support = x.support := by
  have hne : (algebraMap ℤ_[p] ℚ_[p]) a ≠ 0 := by
    intro h; apply ha; exact PadicInt.coe_eq_zero.mp h
  ext m
  rw [mem_support_iff, mem_support_iff, MvPolynomial.coeff_smul, Algebra.smul_def]
  constructor
  · intro h h0; apply h; rw [h0, mul_zero]
  · intro h; exact mul_ne_zero hne h
end Formalism.GM.TM
