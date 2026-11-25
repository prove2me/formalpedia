-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LSmall.node_sizes_of_windows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:31.615558+00:00
-- url     : https://prove2.me/submissions/9b13dbfd-a35e-444c-8b68-a630a101641a

import Definitions.Def_Formalism_SizeWindowBrackets_SSmall
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PSmall

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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LSmall
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.LSmall
theorem _root_.solution : NodeSizesOfWindows (H := H) := by
  intro m TT T2 x b b' η κ w'' off bt w ⟨hb, hb', hη, hκ, hx, hoff0, hoff, hw0, hw'', hbt, hsum⟩ ⟨hthick, htop, hthin⟩
  have hκb : 0 ≤ κ * b' := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro u0 j ρ hρ
    by_cases h1 : IsThickAt T2 u0 ρ
    · linarith [(hthick u0 j ρ h1).1]
    by_cases h2 : ∀ t ∈ TT, ρ ≠ topPl t
    · linarith [(hthin u0 j ρ hρ h1 h2).1]
    push Not at h2
    obtain ⟨t, ht, rfl⟩ := h2
    linarith [(htop u0 j t ht).1, (hbt t ht).1]
  · intro u0 j ρ h1
    have := hthick u0 j ρ h1
    exact ⟨this.1, by linarith [this.2]⟩
  · intro u0 j ρ hρ h1
    by_cases h2 : ∀ t ∈ TT, ρ ≠ topPl t
    · linarith [(hthin u0 j ρ hρ h1 h2).2]
    push Not at h2
    obtain ⟨t, ht, rfl⟩ := h2
    linarith [(htop u0 j t ht).2, (hbt t ht).2]
end Formalism.LFunctionChainParameters.LSmall
