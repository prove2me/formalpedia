-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep.sum_eq_geoS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:44.933079+00:00
-- url     : https://prove2.me/submissions/94c86eca-57f3-4e08-b972-12d5d2e38032

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7
namespace Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
theorem _root_.solution {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (t : ℂ) :
    ∑ j ∈ Finset.range n, (ρ ⬝ᵥ ((-X) ^ j *ᵥ B)) * t ^ (n - 1 - j) = ρ ⬝ᵥ (geoS X t *ᵥ B) := by
  unfold geoS
  have key : ∀ m : ℕ, ∑ j ∈ Finset.range m, (ρ ⬝ᵥ ((-X) ^ j *ᵥ B)) * t ^ (n - 1 - j) =
      ρ ⬝ᵥ ((∑ j ∈ Finset.range m, t ^ (n - 1 - j) • (-X) ^ j) *ᵥ B) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, Matrix.add_mulVec, dotProduct_add,
        Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, mul_comm (t ^ (n - 1 - k))]
  exact key n
end Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
