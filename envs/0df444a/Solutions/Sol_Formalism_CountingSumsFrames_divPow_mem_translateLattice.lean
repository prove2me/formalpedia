-- Prove2me | solution 1 for Formalism.CountingSumsFrames.divPow_mem_translateLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:06:07.309704+00:00
-- url     : https://prove2.me/submissions/81990172-21ff-43ca-a54c-4e2e76bfbc93

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_pairingDivPow_linearSubst
import Theorems.Thm_Formalism_CountingSumsFrames_laplacianDivPow_linearSubst

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
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (L : Set (PolXY K k))
    (hL : ∀ (l : ℕ) (f : PolXY K k), f ∈ L → hDiv K k l f ∈ L ∧ ctrDiv K k l f ∈ L)
    (g : GL (Fin k) K) (l : ℕ) (f : PolXY K k) (hf : f ∈ latOf g L) :
    hDiv K k l f ∈ latOf g L ∧ ctrDiv K k l f ∈ latOf g L := by
  obtain ⟨f0, hf0, rfl⟩ := hf
  exact ⟨⟨_, (hL l f0 hf0).1, (pairingDivPow_linearSubst g l f0).symm⟩, ⟨_, (hL l f0 hf0).2, (laplacianDivPow_linearSubst g l f0).symm⟩⟩
end Formalism.CountingSumsFrames
