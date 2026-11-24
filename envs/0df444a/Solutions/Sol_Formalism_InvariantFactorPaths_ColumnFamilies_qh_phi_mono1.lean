-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_phi_mono1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:22.617991+00:00
-- url     : https://prove2.me/submissions/7983d3c0-2667-4adc-8edc-12bcd9c07326

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhMemDualWeyl
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
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (d : Fin n × Fin n →₀ ℕ) :
    qhPhi R n (monomial d 1) = monomial (Finsupp.mapDomain Prod.snd d) (monomial d 1) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d1 d2 h1 h2 =>
    have e : (monomial (d1 + d2) (1 : R)) = monomial d1 1 * monomial d2 1 := by
      rw [monomial_mul, one_mul]
    rw [e, map_mul, h1, h2, monomial_mul, Finsupp.mapDomain_add]
  | single v e =>
    rw [← X_pow_eq_monomial, map_pow, qhPhi, aeval_X, mul_pow, Finsupp.mapDomain_single, ← map_pow,
      X_pow_eq_monomial, mul_comm, C_mul_monomial, mul_one]
end Formalism.InvariantFactorPaths.ColumnFamilies
