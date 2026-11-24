-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_sig_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:32:44.947802+00:00
-- url     : https://prove2.me/submissions/8e2dc2d1-525b-4a18-9dab-1aefbbd995ae

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_genDet_ne
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


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
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) : Function.Injective (qd_sig n) := by
  have h1 : Function.Injective (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n)) :=
    IsLocalization.injective (GLCoord ℚ n)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (qd_genDet_ne n))
  have h2 : Function.Injective (rename (R := ℚ) (Prod.swap : Fin n × Fin n → Fin n × Fin n)) :=
    rename_injective _ Prod.swap_injective
  intro p q hpq
  exact h2 (h1 hpq)
end Formalism.InvariantFactorPaths.ColumnFamilies
