-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldiag_prod_rowDeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:13.239916+00:00
-- url     : https://prove2.me/submissions/4673bef4-c875-49ff-a065-3a9f3b363df0

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DomPow
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockDiagBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
open Formalism.REAL (fockF)
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r n : ℕ} (t : Fin r → ℂ) (u : Fin r × Fin n →₀ ℕ) :
    (u.prod fun v k => t v.1 ^ k) = ∏ a : Fin r, t a ^ rowDeg u a := by
  have h1 : (u.prod fun v k => t v.1 ^ k) = ∏ v : Fin r × Fin n, t v.1 ^ u v := by
    exact Finsupp.prod_fintype _ _ (fun _ => pow_zero _)
  rw [h1]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  try dsimp only
  rw [Finset.prod_pow_eq_pow_sum, rowDeg]
end Formalism.GradedWeylDivisibility
