-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_phi_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:23.148+00:00
-- url     : https://prove2.me/submissions/2cee0ab5-6048-4d06-8785-9f3a9621d95b

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhMemDualWeyl
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_phi_mono1

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
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (d : Fin n × Fin n →₀ ℕ) (r : R) :
    qhPhi R n (monomial d r) = monomial (Finsupp.mapDomain Prod.snd d) (monomial d r) := by
  have e : monomial d r = r • monomial d (1 : R) := by rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, qh_phi_mono1, smul_monomial]
end Formalism.InvariantFactorPaths.ColumnFamilies
