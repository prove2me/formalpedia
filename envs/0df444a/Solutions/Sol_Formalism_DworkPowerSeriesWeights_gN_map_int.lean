-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.gN_map_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:02.921055+00:00
-- url     : https://prove2.me/submissions/51a5e0a3-1be4-44e1-a126-59d1315e82ad

import Definitions.Def_Formalism_GaussJetBounds_StatementM
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_intCast_padicComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (l : ℕ) [Fact l.Prime] {σ : Type} (P : MvPolynomial σ ℤ)
    (hP : MvPolynomial.map (Int.castRingHom (ZMod l)) P ≠ 0) :
    gN (MvPolynomial.map (Int.castRingHom ℂ_[l]) P) = 1 := by
  apply le_antisymm
  · refine gN_le fun n => ?_
    rw [coeff_map, eq_intCast, norm_intCast_padicComplex]
    exact Padic.norm_int_le_one _
  · obtain ⟨n, hn⟩ := ne_zero_iff.mp hP
    rw [coeff_map, eq_intCast] at hn
    have hnd : ¬ (l : ℤ) ∣ coeff n P := fun h => hn ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h)
    have h1 : ‖((coeff n P : ℤ) : ℚ_[l])‖ = 1 :=
      le_antisymm (Padic.norm_int_le_one _)
        (not_lt.mp fun h => hnd (Padic.norm_intCast_lt_one_iff.mp h))
    have := le_gN (MvPolynomial.map (Int.castRingHom ℂ_[l]) P) n
    rwa [coeff_map, eq_intCast, norm_intCast_padicComplex, h1] at this
end Formalism.DworkPowerSeriesWeights
