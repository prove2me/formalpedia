-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmA_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:27.424881+00:00
-- url     : https://prove2.me/submissions/7aa2fc98-ae50-4004-b33e-c8f32bd943dc

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementA
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmA_top_gen
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmA_dTop_odd

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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (l d : ℕ) [NeZero d] (hl : 2 ≤ l) (TT : Finset (ZMod d))
    (nu1 nu2 : ZMod d → ℕ) (s : ZMod d) (R : Finset ℕ) (hR : ∀ j ∈ R, Odd j) :
    ∃ ε : ℝ, 0 ≤ ε ∧ (∀ e : ℕ, dTop d TT s = e → ((l : ℝ) ^ e)⁻¹ ≤ ε) ∧
      topTerm l d TT nu1 nu2 s + ((nu1 s : ℝ) * ε +
        ∑ j ∈ R, (capL d TT nu1 nu2 (s + (j : ZMod d)) : ℝ) * max (1 - (l : ℝ) ^ j * ε) 0) ≤
        (nu1 s : ℝ) * gam l := by
  obtain ⟨ε, h0, h1, h2⟩ := asmA_top_gen l hl (nu1 s : ℝ) (Nat.cast_nonneg _)
    (fun e => (capL d TT nu1 nu2 (s + (e : ZMod d)) : ℝ)) (fun _ => Nat.cast_nonneg _)
    (dTop d TT s) (fun e he => asmA_dTop_odd TT s e he) R hR
  exact ⟨ε, h0, h1, h2⟩
end Formalism.DworkPowerSeriesWeights
