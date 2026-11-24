-- Prove2me | solution 1 for Formalism.NG.ColumnGeneratorDecomposition.colGenJ_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:09:32.821796+00:00
-- url     : https://prove2.me/submissions/72171648-9dfa-412e-b4ae-e77f68e35cd2

import Definitions.Def_Formalism_CharacterColumnKernels_StatementColKer
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKer

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
open Formalism Formalism.NG
open Formalism.NG.ColumnGeneratorDecomposition
variable {A T' G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Group G]
  {r : G →* A} {χ : G →* T'ˣ} {E : A} {ι : Type*} [DecidableEq ι] {j : ι → ℕ}
namespace Formalism.NG.ColumnGeneratorDecomposition
theorem _root_.solution (y : Ymod r χ E) (l : ι) (c : A) (s : Fin (j l) → A) (c₀ : A) :
    colGenJ y l c s c₀ = ((y, 0) : ColFreeJ A r χ E ι j) + c • fNu l +
      ∑ a, s a • fSig l a + c₀ • fSig0 l := by
  refine Prod.ext ?_ ?_
  · simp [colGenJ, Prod.fst_sum]
  · funext l'
    by_cases h : l' = l
    · subst h
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp [colGenJ, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply]
      · funext b
        simp [colGenJ, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [colGenJ, Prod.snd_sum, Finset.sum_apply]
    · simp [colGenJ, Prod.snd_sum, Finset.sum_apply, Pi.single_eq_of_ne h]
end Formalism.NG.ColumnGeneratorDecomposition
