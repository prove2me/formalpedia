-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.iN_le_min
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:13.898807+00:00
-- url     : https://prove2.me/submissions/22e4919c-592f-4619-8629-cc2168f1e777

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GrowthSums_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryATwoAndB
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_iN_mul_le
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ParitySumsOverFilteredPairs_iN_le_cap

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
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
variable {ν r0 r1 E : ℕ}
namespace Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
theorem _root_.solution (hC : HitsCapPos) {K : Type} [Field K] [NeZero ν] {C : ℕ} {p : ℕ} (hp : 0 < p)
    (ξ : ZMod (2 * ν) → Fin r0 → K) (α : PhiI ν r0 r1 E → ℕ) (β : KapI ν r1 E →₀ ℕ)
    (e : TpV ν r1 → ℕ) (l : Fin C → ℕ)
    (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1)
    (h3 : ∀ τ, ∑ φ, α φ * dAof p φ τ + ∑ k, β k * dBof p k τ ≤ e τ)
    (h4 : hasseDir (bBof p ξ) β (lowOp l sf T I) ≠ 0) (s : ZMod (2 * ν)) (e' : ℕ) :
    (iN β s e' : ℝ) ≤ min ((alN e s : ℝ) / (p : ℝ) ^ (2 * e' + 1))
      (capN sf (s + ((2 * e' + 1 : ℕ) : ZMod (2 * ν))) : ℝ) := by
  refine le_min ?_ ?_
  · rw [le_div_iff₀ (pow_pos (Nat.cast_pos.2 hp) _)]
    exact_mod_cast iN_mul_le α β e h3 s e'
  · exact_mod_cast iN_le_cap hC p ξ β l sf T I h4 s e'
end Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
