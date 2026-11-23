-- Prove2me | solution 1 for Bl.FirstBlockLemmaC.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:50.569811+00:00
-- url     : https://prove2.me/submissions/a864c1b6-6642-4192-bdd4-3ef46d5dc705

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaC_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.FirstBlockLemmaC
namespace Bl.FirstBlockLemmaC
theorem _root_.solution :
  ∀ {p : Nat} [inst : Fact (Nat.Prime p)] {m : Nat},
  Ne.{1} m 0 → ∀ {ζ : PadicAlgCl p}, Eq.{1} (HPow.hPow.{0, 0, 0} ζ m) 1 → Eq.{1} (Norm.norm.{0} ζ) 1 := by
  intro p _ m hm ζ h
  have h1 : ‖ζ‖ ^ m = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm).mp h1
end Bl.FirstBlockLemmaC
