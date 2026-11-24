-- Prove2me | solution 1 for Formalism.NG.ColumnGeneratorDecomposition.map_colGenJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:08.78922+00:00
-- url     : https://prove2.me/submissions/58700b07-1b0b-4b57-af7c-3a5e2c9ca64c

import Definitions.Def_Formalism_CharacterColumnKernels_StatementColKer
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKer
import Theorems.Thm_Formalism_NG_ColumnGeneratorDecomposition_colGenJ_decomp

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
variable {M : Type*} [AddCommGroup M] [Module A M]
namespace Formalism.NG.ColumnGeneratorDecomposition
theorem _root_.solution (ψ : ColFreeJ A r χ E ι j →ₗ[A] M) (y : Ymod r χ E) (l : ι) (c : A)
    (s : Fin (j l) → A) (c₀ : A) :
    ψ (colGenJ y l c s c₀) = ψ (y, 0) + c • ψ (fNu l) + ∑ a, s a • ψ (fSig l a) +
      c₀ • ψ (fSig0 l) := by
  rw [colGenJ_decomp]
  simp only [map_add, map_sum, map_smul]
end Formalism.NG.ColumnGeneratorDecomposition
