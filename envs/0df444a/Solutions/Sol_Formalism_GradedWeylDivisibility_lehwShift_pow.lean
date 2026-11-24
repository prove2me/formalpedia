-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lehwShift_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:22.999378+00:00
-- url     : https://prove2.me/submissions/0d380ffa-bd96-40e6-951a-3ad6502b1b50

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehwShift_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehwShift_one
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} {w : Fin r × Fin n → ℤ}
    {P : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ δ : ℤ}
    (hP : LehwShift w P μ δ) (e : ℕ) : LehwShift w (P ^ e) (e • μ) δ := by
  induction e with
  | zero => simpa using lehwShift_one (R := R) w δ
  | succ e ih =>
    rw [pow_succ, succ_nsmul]
    exact lehwShift_mul ih hP
end Formalism.GradedWeylDivisibility
