-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumSplittings.polyClass_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:51:53.139628+00:00
-- url     : https://prove2.me/submissions/d190e4ad-373f-4e3d-833a-3b4068d96466

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_polyClass_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumSplittings
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic Formalism.FourierDecayAlt.P.ListSumInequalities
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumSplittings
theorem _root_.solution {D : ℕ} {P : Mat k r → ℂ} (hP : PolyClass D P) :
    ∀ n : ℕ, PolyClass (n * D) (fun g => P g ^ n) := by
  intro n
  induction n with
  | zero => simpa using polyClass_const (k := k) (r := r) 1
  | succ n ih =>
    have := polyClass_mul ih hP
    have e : (fun g => P g ^ (n + 1)) = fun g => P g ^ n * P g := by funext g; rw [pow_succ]
    rw [e, Nat.succ_mul]
    exact this
end Formalism.FourierDecayAlt.P.ListSumSplittings
