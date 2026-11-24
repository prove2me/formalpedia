-- Prove2me | solution 1 for Formalism.MainNotions.FormalGroupSystem.Pf.Gen.fac_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:39:07.239803+00:00
-- url     : https://prove2.me/submissions/6094c85f-4dc9-4fd4-be41-bb367e369415

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf Formalism.MainNotions.FormalGroupSystem.Pf.Gen
open Finset
variable {K Pl : Type} [CommRing K] {ι : Pl → Type}
variable [Fintype Pl]
variable [DecidableEq Pl]
namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen
theorem _root_.solution [∀ v, Fintype (ι v)] (n : (Σ v, ι v) →₀ ℕ) : fac n = ∏ v, fac (eqv n v) := by
  classical
  have h1 : ∀ {τ : Type} [Fintype τ] (m : τ →₀ ℕ), fac m = ∏ x, (m x).factorial := by
    intro τ _ m
    unfold fac
    refine Finset.prod_subset (Finset.subset_univ _) ?_
    intro x _ hx
    have h0 : m x = 0 := by simpa using hx
    rw [h0, Nat.factorial_zero]
  rw [h1, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [h1]
  exact Finset.prod_congr rfl fun i _ => by rw [Finsupp.sigmaFinsuppAddEquivPiFinsupp_apply]
end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
