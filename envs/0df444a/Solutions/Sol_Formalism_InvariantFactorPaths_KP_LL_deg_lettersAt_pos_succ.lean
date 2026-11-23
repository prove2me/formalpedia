-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.deg_lettersAt_pos_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:11.284033+00:00
-- url     : https://prove2.me/submissions/5fb7b7dd-6a4a-4ced-b4ec-593ee6d40083

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_SmulMemOfNorm
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LetterAtSuccVal
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_letterAt_succ_val
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_pos_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_pos_ne_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_pos_lt_u

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
open MvPolynomial Finset Formalism.GM.M
variable {N r : ℕ} (D : BlockData N)
variable {D}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) :
    (D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)) = D.LL.deg (D.letterAt (D.T.pos i + 1)) - j i := by
  simp only [BlockData.lettersAt]
  have hs : (∑ i', if ((D.letterAt (D.T.pos i + 1) : Fin N) : ℕ) = D.T.pos i' ∨
      ((D.letterAt (D.T.pos i + 1) : Fin N) : ℕ) = D.T.pos i' + 1 then j i' else 0) = j i := by
    rw [Finset.sum_eq_single i]
    · simp [letterAt_succ_val hB]
    · intro b _ hb
      rw [if_neg]
      rw [letterAt_succ_val hB]
      rintro (h | h)
      · exact pos_ne_succ hB b i h.symm
      · exact hb (pos_inj hB (by omega)).symm
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hu : D.letterAt (D.T.pos i + 1) ≠ D.uPos := by
    intro h
    have h1 := congrArg Fin.val h
    rw [letterAt_succ_val hB] at h1
    have := pos_lt_u hB i
    omega
  rw [hs, if_neg hu, Nat.sub_zero]
end Formalism.InvariantFactorPaths.KP.LL
