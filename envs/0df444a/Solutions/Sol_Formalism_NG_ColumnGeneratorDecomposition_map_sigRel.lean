-- Prove2me | solution 1 for Formalism.NG.ColumnGeneratorDecomposition.map_sigRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:30:49.151363+00:00
-- url     : https://prove2.me/submissions/51202469-fa20-450f-99c2-beb2185e6a90

import Definitions.Def_Formalism_CharacterColumnKernels_StatementColKer
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKer
import Theorems.Thm_Formalism_NG_ColumnGeneratorDecomposition_map_colGenJ

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
theorem _root_.solution (ψ : ColFreeJ A r χ E ι j →ₗ[A] M) (l : ι) (a : Fin (j l)) (t : A) :
    ψ (colGenJ 0 l 0 (Pi.single a t) 0) = t • ψ (fSig l a) := by
  have h0 : ψ ((0 : Ymod r χ E), 0) = 0 := map_zero ψ
  rw [map_colGenJ]
  simp [Pi.single_apply, h0]
end Formalism.NG.ColumnGeneratorDecomposition
