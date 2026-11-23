-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_PullLatticeOrdinary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:31.815809+00:00
-- url     : https://prove2.me/submissions/3a5a115b-746b-4ba9-87c0-1d27b6e0b076

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x1_conj_real
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_conj_real
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x5_conj_real
import Theorems.Thm_Formalism_FourierDecayAlt_P_different_power_conj_stable
import Theorems.Thm_Formalism_FourierDecayAlt_P_localAwayFromLevel
import Theorems.Thm_Formalism_FourierDecayAlt_P_localTwistedLattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
open NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution : PullLatticeOrdinary := by
  intro E _ _ _ g ν s P hP hgP K _ R σ hσ ω hω hω' u α ψ η Θ hu t
  have key : ∀ B : S6.FI E, S6.ConjStable E B → ∀ x : E, x ∈ S6.locAt E P (S6.zsub E B) →
      x - (-1) ^ s * IsCMField.complexConj E x ∈ S6.locAt E P (S6.zsub E B) := by
    intro B hB x hx
    obtain ⟨a, ha, h⟩ := hx
    refine ⟨a, ha, ?_⟩
    have hc : IsCMField.complexConj E (algebraMap (𝓞 (maximalRealSubfield E)) E a * x) ∈ S6.zsub E B :=
      hB _ h
    rw [map_mul, Formalism.FourierDecayAlt.P.S6x2.conj_real] at hc
    have e : algebraMap (𝓞 (maximalRealSubfield E)) E a * (x - (-1) ^ s * IsCMField.complexConj E x) =
        algebraMap (𝓞 (maximalRealSubfield E)) E a * x -
          (-1) ^ s * (algebraMap (𝓞 (maximalRealSubfield E)) E a * IsCMField.complexConj E x) := by ring
    rw [e]
    rcases neg_one_pow_eq_or E s with h1 | h1 <;> rw [h1]
    · rw [one_mul]; exact (S6.zsub E B).sub_mem h hc
    · rw [neg_one_mul, sub_neg_eq_add]; exact (S6.zsub E B).add_mem h hc
  have hPer : t ∈ S6.locAt E P (S6.perLat E g ν s) ↔ t ∈ S6.locAt E P (S6.zsub E (S6.idl E g 0 ν)) := by
    unfold S6.perLat
    rw [Formalism.FourierDecayAlt.P.localTwistedLattice E _ _ s P hP t, Formalism.FourierDecayAlt.P.localAwayFromLevel E g 1 ν P hP hgP,
      Formalism.FourierDecayAlt.P.localAwayFromLevel E g 2 ν P hP hgP]
    exact ⟨fun h => h.1, fun h => ⟨h, key _ (Formalism.FourierDecayAlt.P.different_power_conj_stable E g 0 ν) t h⟩⟩
  have hLift : t ∈ S6.locAt E P (S6.liftLat E g ν s) ↔
      t ∈ S6.locAt E P (S6.zsub E (S6.idl E g 0 (-ν))) := by
    unfold S6.liftLat
    rw [Formalism.FourierDecayAlt.P.localTwistedLattice E _ _ s P hP t, Formalism.FourierDecayAlt.P.localAwayFromLevel E g (-1) (-ν) P hP hgP]
    exact ⟨fun h => h.1, fun h => ⟨h, key _ (Formalism.FourierDecayAlt.P.different_power_conj_stable E g 0 (-ν)) t h⟩⟩
  have hinv : ((u⁻¹ : Kˣ) : K) = σ ω⁻¹ := by
    by_cases hω0 : ω = 0
    · have h0 : (u : K) = 0 := by rw [hu, hω0, map_zero]
      have h10 : (1 : K) = 0 := by rw [← u.mul_inv, h0, zero_mul]
      have := subsingleton_of_zero_eq_one h10.symm
      exact Subsingleton.elim _ _
    · apply Units.inv_eq_of_mul_eq_one_right
      rw [hu, ← map_mul, mul_inv_cancel₀ hω0, map_one]
  refine ⟨?_, ?_⟩
  · show (u : K) * σ t ∈ R ↔ _
    rw [hu, ← map_mul, ← hσ, ← hω, hPer]
  · show ((u⁻¹ : Kˣ) : K) * σ t ∈ R ↔ _
    rw [hinv, ← map_mul, ← hσ, ← hω', hLift]
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
