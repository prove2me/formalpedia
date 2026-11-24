-- Prove2me | solution 1 for Formalism.REAL.exp_injective_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:43:13.845394+00:00
-- url     : https://prove2.me/submissions/5b4fd944-70d9-4ae1-8c86-f790e590f4d3

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Theorems.Thm_Formalism_REAL_isSelfAdjoint_of_conjTranspose_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open Formalism Formalism.REAL
variable {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution {A B : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ = A) (hB : Bᴴ = B)
    (h : NormedSpace.exp A = NormedSpace.exp B) : A = B := by
  have h1 := congrArg CFC.log h
  first
  | rwa [CFC.log_exp A (isSelfAdjoint_of_conjTranspose_eq hA), CFC.log_exp B (isSelfAdjoint_of_conjTranspose_eq hB)] at h1
  | rwa [CFC.log_exp A, CFC.log_exp B] at h1
end Formalism.REAL
