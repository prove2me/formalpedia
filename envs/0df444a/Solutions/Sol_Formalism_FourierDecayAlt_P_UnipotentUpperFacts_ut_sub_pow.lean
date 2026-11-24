-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentUpperFacts.ut_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:36:06.841767+00:00
-- url     : https://prove2.me/submissions/24072bc8-97d5-44d3-92d2-e1ad48c9ccc1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedPointsGramVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_strict_pow_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentUpperFacts
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector
namespace Formalism.FourierDecayAlt.P.UnipotentUpperFacts
theorem _root_.solution {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : (u - 1) ^ m = 0 := by
  apply strict_pow_eq_zero
  intro i j hji
  rw [Matrix.sub_apply, Matrix.one_apply]
  rcases lt_or_eq_of_le hji with h | h
  · rw [hu.1 i j h, if_neg (fun e => by subst e; exact lt_irrefl _ h), sub_zero]
  · subst h; rw [hu.2, if_pos rfl, sub_self]
end Formalism.FourierDecayAlt.P.UnipotentUpperFacts
