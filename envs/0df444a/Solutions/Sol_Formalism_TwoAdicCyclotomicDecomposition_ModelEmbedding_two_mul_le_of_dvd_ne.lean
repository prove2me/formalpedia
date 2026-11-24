-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.two_mul_le_of_dvd_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:37:25.60437+00:00
-- url     : https://prove2.me/submissions/107a31a1-ce71-434b-9bb2-7de907e0468a

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Subgroup
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open ModelEmbedding
open Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
namespace Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
theorem _root_.solution {a b : ℕ} (hb : 0 < b) (hd : a ∣ b) (hne : b ≠ a) : 2 * a ≤ b := by
  obtain ⟨c, rfl⟩ := hd
  rcases c with _ | _ | c
  · simp at hb
  · simp at hne
  · nlinarith
end Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
