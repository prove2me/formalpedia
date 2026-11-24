-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:24:20.672745+00:00
-- url     : https://prove2.me/submissions/f3dd0edf-feb3-4b1e-86be-22245f131556

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_prod_castLE
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_mem_iff

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
theorem _root_.solution {mu mu' : Fin n → ℤ} {f f' : GLCoord R n} (hf : f ∈ inducedSections R mu) (hf' : f' ∈ inducedSections R mu') :
    f * f' ∈ inducedSections R (mu + mu') := by
  rw [qh_mem_iff] at hf hf' ⊢
  intro R' _ _ b g u hb hu
  rw [map_mul, map_mul, hf R' b g u hb hu, hf' R' b g u hb hu]
  simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib, Units.val_mul]
  ring
end Formalism.InvariantFactorPaths.ColumnFamilies
