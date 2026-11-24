-- Prove2me | solution 1 for Formalism.G0.DetDividesP.conj_diagonal_last_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:22.549981+00:00
-- url     : https://prove2.me/submissions/70cf57c7-1ed8-4663-87f6-e82f36da4344

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
import Theorems.Thm_Formalism_G0_DetDividesP_diagonal_last_zero_eq
import Theorems.Thm_Formalism_G0_DetDividesP_rank_one_conj_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
variable {L : Type} [Field L]
namespace Formalism.G0.DetDividesP
theorem _root_.solution (hr : 0 < r) (φ : Fin r → L) (hφ : φ (lst hr) = 1) :
    (gU (lst hr) φ hφ).1 * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then (0 : L) else 1) *
      (gU (lst hr) φ hφ)⁻¹.1 = 1 - Matrix.vecMulVec (Pi.single (lst hr) (1 : L)) φ := by
  rw [diagonal_last_zero_eq hr]
  exact rank_one_conj_eq (lst hr) φ hφ
end Formalism.G0.DetDividesP
