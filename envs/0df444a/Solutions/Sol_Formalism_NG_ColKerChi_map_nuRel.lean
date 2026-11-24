-- Prove2me | solution 1 for Formalism.NG.ColKerChi.map_nuRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:33:23.099905+00:00
-- url     : https://prove2.me/submissions/230b15a6-7182-4a44-805f-fe1eec683528

import Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelEqualityForm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKer
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKerChiOne
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
open Formalism.NG.ColKerChi
open ColumnGeneratorDecomposition
variable {A T' G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Group G]
  {r : G →* A} {χ : G →* T'ˣ} {E : A} {ι : Type*} [DecidableEq ι] {j : ι → ℕ}
  {M : Type*} [AddCommGroup M] [Module A M]
namespace Formalism.NG.ColKerChi
theorem _root_.solution (ψ : ColFreeJ A r χ E ι j →ₗ[A] M) (l : ι) (t : A) :
    ψ (colGenJ 0 l t 0 0) = t • ψ (fNu l) := by
  have h0 : ψ ((0 : Ymod r χ E), 0) = 0 := map_zero ψ
  rw [map_colGenJ]
  simp [h0]
end Formalism.NG.ColKerChi
