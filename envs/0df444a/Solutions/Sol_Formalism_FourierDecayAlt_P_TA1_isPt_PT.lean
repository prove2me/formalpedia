-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TA1.isPt_PT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:56.263861+00:00
-- url     : https://prove2.me/submissions/32603ecf-7156-41c7-b7ed-d477aaa81c90

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagonalTopBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TA1_mem_PT_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TA1
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate
namespace Formalism.FourierDecayAlt.P.TA1
theorem _root_.solution {E : Type} [Field E] [DecidableEq E] (Sg : ℕ → ℕ → Finset E) (hNZ : NZSg Sg) :
    ∀ n p, p ∈ PT Sg n → IsPt n p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hp
    cases n with
    | zero =>
      simp [PT] at hp; subst hp; exact ⟨by simp [lvl], by simp⟩
    | succ n =>
      obtain ⟨m, hm, h, hh, t, ht, rfl⟩ := (mem_PT_succ Sg n p).1 hp
      have h0 := ih m (by omega) h hh
      refine ⟨?_, ?_⟩
      · have := h0.1
        simp only [lvl] at this
        simp [lvl, Formalism.FourierDecayAlt.TA.ext, this]; omega
      · intro b hb
        simp only [Formalism.FourierDecayAlt.TA.ext, List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact h0.2 b hb
        · exact ⟨by simp; omega, hNZ _ _ t ht⟩
end Formalism.FourierDecayAlt.P.TA1
