-- Prove2me | solution 1 for Formalism.GM.FockB.tvA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:06.668825+00:00
-- url     : https://prove2.me/submissions/625acf65-54f3-40fb-975a-04f2d90b2363

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_finPos_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset Formalism.GM.M
variable {N r : ℕ} {D : BlockData N}
namespace Formalism.GM.FockB
theorem _root_.solution (hB : D.BlockOK) (a : Option (Fin D.T.t)) :
    M.TieVars (wA (r := r) D a) (eA D a) (zA D a) (sA D a) := by
  have h2 := hB.2.2.2
  rcases a with _ | i
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro c d h; simpa [wA] using h
    · intro c d h; simpa [eA, xiVar] using h
    · intro c d h
      simp only [wA, eA, xiVar, Option.elim, Sum.inl.injEq, Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc,
        Fin.val_last] at h
      omega
    · intro c; simp [wA, eA, zA, sA, xiVar, scalZ, scalS]
    · simp [zA, sA, scalZ, scalS]
  · have h1 := hB.2.1 i
    have hv0 : (finPos N (D.T.pos i) : ℕ) = D.T.pos i := finPos_val (by omega)
    have hv1 : (finPos N (D.T.pos i + 1) : ℕ) = D.T.pos i + 1 := finPos_val (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro c d h; simpa [wA] using h
    · intro c d h; simpa [eA] using h
    · intro c d h
      simp only [wA, eA, Option.elim, Sum.inl.injEq, Prod.mk.injEq, Fin.ext_iff] at h
      omega
    · intro c; simp [wA, eA, zA, sA, scalZ, scalS]
    · simp [zA, sA, scalZ, scalS]
end Formalism.GM.FockB
