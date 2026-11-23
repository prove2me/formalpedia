-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BlockStartPoints.phi_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:57.587433+00:00
-- url     : https://prove2.me/submissions/994d3bce-4f20-4f1c-a2d2-00f7aacb0377

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockStartPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BlockStartPoints
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
open Classical
noncomputable section
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.BlockStartPoints
theorem _root_.solution {τ J : Type} (S : Finset τ) (Js : Finset J) (m : τ → τ → ℝ) (g : J → τ → τ → ℝ) :
    ∑ t ∈ S, ∑ t' ∈ S, m t t' * ∑ j ∈ Js, g j t t' =
      ∑ j ∈ Js, ∑ t ∈ S, ∑ t' ∈ S, m t t' * g j t t' := by
  simp_rw [Finset.mul_sum]
  calc ∑ t ∈ S, ∑ t' ∈ S, ∑ j ∈ Js, m t t' * g j t t'
      = ∑ t ∈ S, ∑ j ∈ Js, ∑ t' ∈ S, m t t' * g j t t' :=
        Finset.sum_congr rfl fun t _ => Finset.sum_comm
    _ = ∑ j ∈ Js, ∑ t ∈ S, ∑ t' ∈ S, m t t' * g j t t' := Finset.sum_comm
end Formalism.FourierDecayAlt.P.BlockStartPoints
