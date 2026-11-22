-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_sig
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:38:26.214271+00:00
-- url     : https://prove2.me/submissions/ab653acd-0877-427a-b12f-9873792de9da

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
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
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R')
    (P : MvPolynomial (Fin n × Fin n) ℚ) :
    evGLR (R := ℚ) x (qd_sig n P) = aeval (fun v : Fin n × Fin n => x.val v.2 v.1) P := by
  have h : (evGLR (R := ℚ) x).comp (qd_sig n).toRingHom
      = (aeval (R := ℚ) (fun v : Fin n × Fin n => x.val v.2 v.1)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro v
      simp [qd_sig, evGLR, IsLocalization.Away.lift_eq]
  exact congrArg (fun φ => φ P) h
end Formalism.InvariantFactorPaths.ColumnFamilies
