-- Prove2me | solution 1 for Formalism.ResultantValuation.LaplaceProof.prod_finPairsLT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:36:46.199193+00:00
-- url     : https://prove2.me/submissions/fed015e5-0db2-42a5-ac00-7c7d599907ab

import Definitions.Def_Formalism_ResultantValuation_ResultantConjugate
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Laplace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Equiv
noncomputable section
open Formalism Formalism.ResultantValuation
open Formalism.ResultantValuation.LaplaceProof
namespace Formalism.ResultantValuation.LaplaceProof
theorem _root_.solution {n : ℕ} (f : (Σ _ : Fin n, Fin n) → ℤˣ) :
    ∏ p ∈ Perm.finPairsLT n, f p = ∏ x : Fin n, ∏ y : Fin n, if y < x then f ⟨x, y⟩ else 1 := by
  have hs : Perm.finPairsLT n = univ.sigma (fun x : Fin n => univ.filter (· < x)) := by
    ext ⟨x, y⟩
    simp [Perm.mem_finPairsLT]
  rw [hs, Finset.prod_sigma]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Finset.prod_filter]
end Formalism.ResultantValuation.LaplaceProof
