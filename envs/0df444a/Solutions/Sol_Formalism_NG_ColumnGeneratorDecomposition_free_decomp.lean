-- Prove2me | solution 1 for Formalism.NG.ColumnGeneratorDecomposition.free_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:09:34.183335+00:00
-- url     : https://prove2.me/submissions/fbf426f1-cf47-485a-9d55-44aee148c500

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
theorem _root_.solution [Fintype ι] (z : ColFreeJ A r χ E ι j) :
    z = ((z.1, 0) : ColFreeJ A r χ E ι j) +
      ∑ l, colGenJ 0 l (z.2 l).1 (z.2 l).2.1 (z.2 l).2.2 := by
  refine Prod.ext ?_ ?_
  · simp [colGenJ, Prod.fst_sum]
  · simp only [colGenJ, Prod.snd_add, Prod.snd_sum, zero_add, Prod.mk.eta]
    exact (Finset.univ_sum_single z.2).symm
end Formalism.NG.ColumnGeneratorDecomposition
