-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.tele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:29:05.175087+00:00
-- url     : https://prove2.me/submissions/aee8b59c-138b-47be-8fc1-77d4e04e97dc

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
theorem _root_.solution (w : ℕ → ℝ) (U : ℕ) : ∀ V, U ≤ V →
    ∑ n ∈ Ioc U V, (w n - w (n + 1)) = w (U + 1) - w (V + 1) := by
  intro V hV
  induction V, hV using Nat.le_induction with
  | base => simp
  | succ V hUV ih => rw [Finset.sum_Ioc_succ_top hUV, ih]; ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
