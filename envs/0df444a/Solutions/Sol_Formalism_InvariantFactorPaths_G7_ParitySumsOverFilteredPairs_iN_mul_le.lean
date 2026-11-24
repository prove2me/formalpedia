-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs.iN_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:33.363837+00:00
-- url     : https://prove2.me/submissions/f47fdb7a-41b0-451d-b790-0cd54045852c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GrowthSums_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryATwoAndB

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
theorem _root_.solution [NeZero ν] {p : ℕ} (α : PhiI ν r0 r1 E → ℕ) (β : KapI ν r1 E →₀ ℕ)
    (e : TpV ν r1 → ℕ)
    (h3 : ∀ τ, ∑ φ, α φ * dAof p φ τ + ∑ k, β k * dBof p k τ ≤ e τ) (s : ZMod (2 * ν)) (e' : ℕ) :
    iN β s e' * p ^ (2 * e' + 1) ≤ alN e s := by
  unfold iN alN
  split_ifs with h
  · rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun b _ => ?_)
    have h1 := h3 (s, b)
    have h2 : β (s, ⟨e', h⟩, b) * dBof p (s, ⟨e', h⟩, b) (s, b) ≤ ∑ k, β k * dBof p k (s, b) :=
      Finset.single_le_sum (f := fun k => β k * dBof p k (s, b)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ _)
    have h4 : dBof p (s, ⟨e', h⟩, b) (s, b) = p ^ (2 * e' + 1) := by
      simp [dBof]
    rw [h4] at h2
    exact le_trans h2 (le_trans (Nat.le_add_left _ _) h1)
  · simp
end Formalism.InvariantFactorPaths.G7.ParitySumsOverFilteredPairs
