-- Prove2me | solution 1 for Formalism.G0.DetDividesP.adj_Tm_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:04.979064+00:00
-- url     : https://prove2.me/submissions/1dd9a7db-30f4-46c8-9600-7b6cc592016f

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
import Theorems.Thm_Formalism_G0_DetDividesP_evPerm_Tm
import Theorems.Thm_Formalism_G0_DetDividesP_sign_cast_ne_zero

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
theorem _root_.solution (A : Fin r → ι) (hA : Function.Injective A) (lst l : Fin r) :
    (Tm K A).adjugate lst l ≠ 0 := by
  classical
  intro h
  rw [Matrix.adjugate_apply] at h
  have := congrArg (evPerm (K := K) A (Equiv.swap l lst)) h
  have hm : (evPerm (K := K) A (Equiv.swap l lst)).mapMatrix ((Tm K A).updateRow l (Pi.single lst 1)) =
      (Equiv.swap l lst).permMatrix K := by
    ext i j
    have hT := congrFun (congrFun (evPerm_Tm (K := K) A hA (Equiv.swap l lst)) i) j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply] at hT
    by_cases hi : i = l
    · subst hi
      simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_self]
      simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Equiv.swap_apply_left,
        Option.mem_def, Option.some.injEq]
      by_cases hj : j = lst
      · subst hj; simp
      · simp [hj, Ne.symm hj]
    · simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_ne hi]
      exact hT
  rw [AlgHom.map_det, hm, Matrix.det_permutation, map_zero] at this
  exact sign_cast_ne_zero (K := K) _ this
end Formalism.G0.DetDividesP
