-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ValuationParity.sum_charge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:45:35.272415+00:00
-- url     : https://prove2.me/submissions/92edf722-57bf-4a4f-af39-086a271530c3

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryAOneParity

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
open Formalism.InvariantFactorPaths.G7.ValuationParity
namespace Formalism.InvariantFactorPaths.G7.ValuationParity
theorem _root_.solution {Φ S : Type} [Fintype Φ] [DecidableEq S] (TT : Finset S) (R : Finset ℕ)
    (c : Φ → S × ℕ) (w : Φ → ℕ) (h : ∀ φ, w φ ≠ 0 → (c φ).1 ∈ TT ∧ (c φ).2 ∈ R) :
    ∑ s ∈ TT, ∑ e ∈ R, ∑ φ, (if c φ = (s, e) then w φ else 0) = ∑ φ, w φ := by
  calc ∑ s ∈ TT, ∑ e ∈ R, ∑ φ, (if c φ = (s, e) then w φ else 0)
      = ∑ s ∈ TT, ∑ φ, ∑ e ∈ R, (if c φ = (s, e) then w φ else 0) :=
        Finset.sum_congr rfl fun s _ => Finset.sum_comm
    _ = ∑ φ, ∑ s ∈ TT, ∑ e ∈ R, (if c φ = (s, e) then w φ else 0) := Finset.sum_comm
    _ = ∑ φ, w φ := by
      refine Finset.sum_congr rfl fun φ _ => ?_
      by_cases hw : w φ = 0
      · simp [hw]
      obtain ⟨h1, h2⟩ := h φ hw
      rw [Finset.sum_eq_single (c φ).1]
      · rw [Finset.sum_eq_single (c φ).2]
        · simp
        · intro e _ he
          rw [if_neg]
          intro hc
          apply he
          rw [hc]
        · intro h'
          exact absurd h2 h'
      · intro s _ hs
        refine Finset.sum_eq_zero fun e _ => ?_
        rw [if_neg]
        intro hc
        apply hs
        rw [hc]
      · intro h'
        exact absurd h1 h'
end Formalism.InvariantFactorPaths.G7.ValuationParity
