-- Prove2me | solution 1 for Formalism.G0.DetDividesP.evPerm_Tm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:21.224852+00:00
-- url     : https://prove2.me/submissions/44072053-f818-4c67-957c-7f783736b7d1

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
theorem _root_.solution (A : Fin r → ι) (hA : Function.Injective A) (τ : Equiv.Perm (Fin r)) :
    (evPerm (K := K) A τ).mapMatrix (Tm K A) = τ.permMatrix K := by
  ext l b
  have h : ∃ l', A l' = A l := ⟨l, rfl⟩
  have hc : Classical.choose h = l := hA (Classical.choose_spec h)
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Tm, Matrix.of_apply, evPerm, aeval_X,
    Sum.elim_inl, dif_pos h, hc]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, eq_comm]
end Formalism.G0.DetDividesP
