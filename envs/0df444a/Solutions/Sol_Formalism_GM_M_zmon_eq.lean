-- Prove2me | solution 1 for Formalism.GM.M.zmon_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:26.809803+00:00
-- url     : https://prove2.me/submissions/090929e5-d1da-4473-8296-279ac828b24f

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M
open MvPolynomial Finset SSD
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero r] (D : BlockData N)
namespace Formalism.GM.M
theorem _root_.solution : ((∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) *
    X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus : MvPolynomial (BVar N r D.T.t) ℚ_[p]) =
      monomial (zmS D) 1 := by
  simp only [X_pow_eq_monomial]
  rw [zmS, ← monomial_sum_one, monomial_mul, mul_one]
end Formalism.GM.M
