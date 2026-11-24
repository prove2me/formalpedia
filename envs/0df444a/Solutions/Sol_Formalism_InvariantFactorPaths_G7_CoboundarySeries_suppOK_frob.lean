-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoboundarySeries.suppOK_frob
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:35.215679+00:00
-- url     : https://prove2.me/submissions/710189a5-9111-455f-85fa-dba3b806bcf8

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_frobVar_ne_zero


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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.CoboundarySeries
open MvPowerSeries
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.CoboundarySeries
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (σ : K →+* K) {G : MvPowerSeries (Fin 2) K}
    (hG : SuppOK p G) : SuppOK p (frobVar p (map σ G)) := by
  intro n hn
  obtain ⟨m, rfl, hm⟩ := coeff_frobVar_ne_zero (by omega) hn
  rw [MvPowerSeries.coeff_map] at hm
  have hm' : MvPowerSeries.coeff m G ≠ 0 := fun h => hm (by rw [h, map_zero])
  obtain ⟨h0, h1, h2⟩ := hG m hm'
  simp only [Finsupp.smul_apply, smul_eq_mul]
  exact ⟨Nat.mul_pos (by omega) h0, Nat.mul_pos (by omega) h1, h2.mul_left p⟩
end Formalism.InvariantFactorPaths.G7.CoboundarySeries
