-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.coeff_AA_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:23.158076+00:00
-- url     : https://prove2.me/submissions/afd4e4b9-4bba-4679-9ab4-e538aba5b501

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_powq_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ppowq_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_lt_powq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_lt_ppowq

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
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (K : Type) [Field K] {p : ℕ} (hp : 2 ≤ p) {x y : Fin 2} {n : Fin 2 →₀ ℕ}
    {i j : ℕ} (hij : i ≤ j) (hx : n x = (p ^ 2) ^ i) (hy : n y = p * (p ^ 2) ^ j) :
    MvPowerSeries.coeff n (AA K p x y) = ((p : K) ^ (i + j + 1))⁻¹ := by
  change AA K p x y n = _
  simp only [AA]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · rw [if_pos ⟨hij, hx, hy⟩]
    · intro b _ hb
      refine if_neg ?_
      rintro ⟨_, _, h⟩
      exact hb (ppowq_inj hp (h.symm.trans hy))
    · intro hj
      exact absurd (Finset.mem_range.mpr (by rw [hy]; exact lt_ppowq hp j)) hj
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro c _
    refine if_neg ?_
    rintro ⟨_, h, _⟩
    exact hb (powq_inj hp (h.symm.trans hx))
  · intro hi
    exact absurd (Finset.mem_range.mpr (by rw [hx]; exact lt_powq hp i)) hi
end Formalism.InvariantFactorPaths.G7
