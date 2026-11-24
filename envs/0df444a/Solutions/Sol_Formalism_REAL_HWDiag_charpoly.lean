-- Prove2me | solution 1 for Formalism.REAL.HWDiag_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:34:04.996897+00:00
-- url     : https://prove2.me/submissions/2ea5587c-61db-4b59-8c76-73850c319af1

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HWDiag
import Theorems.Thm_Formalism_REAL_HWDiag_Amat_upper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (l : Fin n → ℂ) :
    (Amat l).charpoly = ∏ s : Fin n, (Polynomial.X - Polynomial.C (l s)) := by
  have hU := HWDiag_Amat_upper l
  first
  | (rw [Matrix.charpoly_of_upperTriangular _ hU]
     simp [Amat])
  | (rw [Matrix.charpoly, Matrix.det_of_upperTriangular]
     · refine Finset.prod_congr rfl fun s _ => ?_
       simp [Matrix.charmatrix_apply_eq, Amat]
     · intro i j hij
       have h : j < i := hij
       first
       | simp [Matrix.charmatrix_apply_ne _ _ _ h.ne', Amat, h.ne', not_lt.mpr h.le]
       | simp [Matrix.charmatrix_apply, Amat, h.ne', not_lt.mpr h.le])
end Formalism.REAL
