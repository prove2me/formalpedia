-- Prove2me | solution 1 for Formalism.CountingSumsFrames.fock_mult_val_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:45.354933+00:00
-- url     : https://prove2.me/submissions/68eb00b7-617f-4250-a08d-5dd0648536bd

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_fock_mult_fact_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution {α : Type*} (p : ℕ) [hp : Fact p.Prime] (f : α → ℕ) (s : Finset α) :
    padicValNat p (Nat.multinomial s f) ≤ s.card * Nat.log p (∑ i ∈ s, f i) := by
  rw [← Nat.factorization_def _ hp.out]
  exact fock_mult_fact_le p f s
end Formalism.CountingSumsFrames
