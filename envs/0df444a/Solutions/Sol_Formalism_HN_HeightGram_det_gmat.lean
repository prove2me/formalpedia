-- Prove2me | solution 1 for Formalism.HN.HeightGram.det_gmat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:04.307369+00:00
-- url     : https://prove2.me/submissions/d086fea5-f3f5-418e-b43c-e63e2172e8cf

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Theorems.Thm_Formalism_HN_HeightGram_det_bmat
import Theorems.Thm_Formalism_HN_HeightGram_gmat_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.HeightGram
variable {P S : Type} [Fintype P] [DecidableEq P] [Fintype S] [DecidableEq S] {j : ℕ}
namespace Formalism.HN.HeightGram
theorem _root_.solution (lam : P → S → ℂ) (G : P → Matrix (Fin j) (Fin j) ℂ) (eS : S ≃ P × Fin 2) :
    (gmat lam G).det = (amat lam eS).det ^ (2 * j) * ∏ v, Complex.normSq (G v).det := by
  have h := congrArg Matrix.det (gmat_eq lam G eS)
  simp only [Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one, det_bmat, Fintype.card_fin] at h
  rw [h]
  ring
end Formalism.HN.HeightGram
