-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.contr_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:33.716675+00:00
-- url     : https://prove2.me/submissions/aec15860-8233-45a0-b189-2a15a9a366fa

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_LeadAt_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_hom_intCast0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
variable {R M : Type*} [CommRing R] [AddCommMonoid M] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
theorem _root_.solution (w : ℕ × Fin n → M) (K : Form (MvPolynomial (ℕ × Fin n) R) n)
    (hK : ∀ J, IsWeightedHomogeneous w (K J) 0) (j : ℕ) (I : Finset (Fin n)) (m : Fin n) :
    IsWeightedHomogeneous w (((sg I m : ℤ) : MvPolynomial (ℕ × Fin n) R) * XR R n j m * K (insert m I))
      (w (j, m)) := by
  have hX : IsWeightedHomogeneous w (X (j, m) : MvPolynomial (ℕ × Fin n) R) (w (j, m)) := by
    apply isWeightedHomogeneous_X
  have := ((hom_intCast0 (R := R) w (Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg I m)).mul hX).mul (hK (insert m I))
  simpa only [zero_add, add_zero] using this
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
