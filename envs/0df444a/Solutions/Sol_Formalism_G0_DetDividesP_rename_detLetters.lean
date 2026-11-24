-- Prove2me | solution 1 for Formalism.G0.DetDividesP.rename_detLetters
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:24.620801+00:00
-- url     : https://prove2.me/submissions/c617749e-8acf-4c32-ba84-62b828055a46

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides

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
namespace Formalism.G0.DetDividesP
theorem _root_.solution (A : Fin r → ι) :
    rename Sum.inl (detLetters (K := K) A) = (Tm K A : Matrix (Fin r) (Fin r) (MvPolynomial ((ι × Fin r) ⊕ ι) K)).det := by
  unfold detLetters; rw [AlgHom.map_det]; congr 1; ext l a; simp [Tm]
end Formalism.G0.DetDividesP
