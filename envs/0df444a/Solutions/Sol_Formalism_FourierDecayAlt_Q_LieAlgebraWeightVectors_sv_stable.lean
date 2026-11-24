-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:12:43.427808+00:00
-- url     : https://prove2.me/submissions/c48bfa45-9ad1-432b-a0f3-99d0c4aa8ba6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SmoothVec
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_exp_uw
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_lie_conj
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_exp_conj
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
  {π : Mx k r → (Wp →L[ℂ] Wp)}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution (hrep : IsCRepOn (UWset k r z) π) {h₀ : Mx k r} (hh₀ : h₀ ∈ UWset k r z) {x : Wp}
    (hx : x ∈ SmVec k r z π) : π h₀ x ∈ SmVec k r z π := by
  intro h hh X hX
  have e : (fun t : ℝ => π (h * NormedSpace.exp ((t : ℂ) • X)) (π h₀ x)) =
      fun t : ℝ => π (h * h₀ * NormedSpace.exp ((t : ℂ) • (h₀⁻¹ * X * h₀))) x := by
    funext t
    rw [← sv_exp_conj hh₀ t, hrep.2 _ (WeylGroupFacts.uw_mul hh (sv_exp_uw hX t)) _ hh₀]
    rfl
  rw [e]
  exact hx (h * h₀) (WeylGroupFacts.uw_mul hh hh₀) _ (sv_lie_conj hX hh₀)
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
