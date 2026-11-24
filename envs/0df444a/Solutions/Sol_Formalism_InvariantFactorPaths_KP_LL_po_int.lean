-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.po_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:45.734412+00:00
-- url     : https://prove2.me/submissions/bd75c83e-ea20-45a8-9ec6-d4778ac2871e

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PlusOp
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_contr_divDeriv
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_intPol_iff_bnd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M Formalism.GM.M.PhiIntegrality
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution {σ : Type} (v : σ) (k : ℕ) {y : MvPolynomial σ ℚ_[p]} (hy : y ∈ IntPol p σ) :
    ((k.factorial : ℚ_[p])⁻¹ • (po_d v ^ k) y) ∈ IntPol p σ := by
  rw [intPol_iff_bnd] at hy ⊢
  have h := contr_divDeriv (p := p) v k 1 zero_le_one y hy
  intro m
  simpa using h m
end Formalism.InvariantFactorPaths.KP.LL
