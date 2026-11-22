-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_hom_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:37:46.450238+00:00
-- url     : https://prove2.me/submissions/4507c449-00bd-4c58-9d47-d714e3decc0e

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} {R : Type} [CommRing R] (f g : GLCoord ℤ n →+* R)
    (h : ∀ a b, f (algebraMap (MvPolynomial (Fin n × Fin n) ℤ) _ (X (a, b))) =
      g (algebraMap (MvPolynomial (Fin n × Fin n) ℤ) _ (X (a, b)))) : f = g := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (genMat ℤ n).det) ?_
  apply MvPolynomial.ringHom_ext
  · intro r; simp
  · rintro ⟨a, b⟩; exact h a b
end Formalism.InvariantFactorPaths.ColumnFamilies
