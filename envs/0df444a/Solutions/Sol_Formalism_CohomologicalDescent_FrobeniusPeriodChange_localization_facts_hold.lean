-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.localization_facts_hold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:04:55.003199+00:00
-- url     : https://prove2.me/submissions/022673e7-ad18-4f99-bb81-0f6f9671158f

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_pi0SubstHom_apply
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_pi0Subst_C
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_constantCoeff_pi0
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_inc_X_sub_l_eq_q0
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_q_roots_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_r3_divisibility_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_r3_unit_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution : LocFacts := by
  intro l _ O L _ _ _ _ I ζ em u b jj hl2 hζ hζI hem hb hloc
  obtain ⟨hC, hX, -⟩ := hloc
  obtain ⟨w, hw⟩ := hX
  have hj : jj (X - C (ζ ^ b - 1)) = X * ((w⁻¹ : (L⟦X⟧)ˣ) : L⟦X⟧) := by
    rw [← hw, mul_assoc, Units.mul_inv, mul_one]
  have hbI : ζ ^ b - 1 ∈ I := by
    have h1 : ζ ^ b - 1 = (ζ - 1) * ∑ i ∈ Finset.range b, ζ ^ i := (mul_geom_sum ζ b).symm
    rw [h1]
    exact I.mul_mem_right _ hζI
  have hlI : (l : O) ∈ I := by
    obtain ⟨s, hs⟩ := r3_divisibility_holds l O ζ hl2 hζ b hb
    have h2 := congrArg constantCoeff hs
    rw [map_sub, map_mul, map_sub, constantCoeff_pi0 l O, constantCoeff_C, constantCoeff_C,
      constantCoeff_X] at h2
    have h3 : (l : O) = (ζ ^ b - 1) * constantCoeff s := by linear_combination -h2
    rw [h3]
    exact I.mul_mem_right _ hbI
  have hl0 : (l : O) ≠ 0 := by
    have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
    exact (hζ.neZero').out

  have hq0 : ∃ z : L⟦X⟧, IsUnit z ∧ jj (q0 l O) = X * z := by
    obtain ⟨g, hg, -⟩ := r3_unit_holds l O hl2
    have hq := q_roots_holds l O ζ hζ
    have hU : IsUnit (∏ b' ∈ (Finset.Ioo 0 l).erase b, jj (X - C (ζ ^ b' - 1))) := by
      refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one ?_
      intro b' hb'
      rw [Finset.mem_erase] at hb'
      rw [PowerSeries.isUnit_iff_constantCoeff]
      have e : (X - C (ζ ^ b' - 1) : O⟦X⟧) = (X - C (ζ ^ b - 1)) + C (ζ ^ b - ζ ^ b') := by
        rw [map_sub, map_sub, map_sub]; ring
      rw [e, map_add, hj, hC, map_add, map_mul, constantCoeff_X, zero_mul, zero_add,
        constantCoeff_C]
      refine IsUnit.mk0 _ ?_
      intro h0
      have h1 : ζ ^ b - ζ ^ b' = 0 := hem (by rw [h0, map_zero])
      have h2 : b = b' := hζ.pow_inj (Finset.mem_Ioo.1 hb).2 (Finset.mem_Ioo.1 hb'.2).2
        (sub_eq_zero.1 h1)
      exact hb'.1 h2.symm
    refine ⟨((w⁻¹ : (L⟦X⟧)ˣ) : L⟦X⟧) * (jj (g : O⟦X⟧) *
      ∏ b' ∈ (Finset.Ioo 0 l).erase b, jj (X - C (ζ ^ b' - 1))), ?_, ?_⟩
    · exact (Units.isUnit _).mul (((Units.isUnit g).map jj).mul hU)
    · rw [hg, hq, map_mul, map_prod, ← Finset.mul_prod_erase _ _ hb, hj]
      ring
  obtain ⟨z, hz, hzq⟩ := hq0
  refine ⟨hlI, hl0, ?_, ?_⟩
  · rw [hzq]
    exact associated_mul_unit_left _ _ hz
  · intro y a hya
    obtain ⟨s, hs⟩ := hya
    have hy : y = (X - C (l : O)) * s + C a := by linear_combination hs
    rw [hy, ← pi0SubstHom_apply, map_add, map_mul, pi0SubstHom_apply, pi0SubstHom_apply,
      pi0SubstHom_apply, inc_X_sub_l_eq_q0, pi0Subst_C, map_add, map_mul, hzq, hC, map_add, map_mul,
      map_mul, constantCoeff_X, zero_mul, zero_mul, zero_add, constantCoeff_C]
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
