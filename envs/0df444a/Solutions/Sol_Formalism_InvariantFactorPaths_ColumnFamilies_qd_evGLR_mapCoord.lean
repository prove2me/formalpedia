-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_evGLR_mapCoord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:30:10.303227+00:00
-- url     : https://prove2.me/submissions/3f943db6-94bc-4610-9c42-048507bf821e

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
theorem _root_.solution {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R') (z : GLCoord ℤ n) :
    evGLR (R := ℚ) x (mapCoord ℚ z) = evGL x z := by
  have h : (evGLR (R := ℚ) x).comp (mapCoord ℚ) = evGL x := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (genMat ℤ n).det)
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro v
      simp [evGLR, mapCoord, evGL, IsLocalization.Away.lift_eq]
  exact congrArg (fun φ => φ z) h
end Formalism.InvariantFactorPaths.ColumnFamilies
