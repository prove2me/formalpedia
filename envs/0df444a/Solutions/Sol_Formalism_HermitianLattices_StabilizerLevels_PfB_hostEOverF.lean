-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.PfB.hostEOverF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:21:19.770849+00:00
-- url     : https://prove2.me/submissions/1f582710-3486-4e5d-aced-bf2ac5fd4fd4

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_real
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalSpec
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalois
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_gen
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_Q3_hostGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.StabilizerLevels
open Formalism.HermitianLattices.StabilizerLevels.PfB
open NumberField IntermediateField
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open Formalism.HermitianLattices.FiltrationBoundaryCriterion
namespace Formalism.HermitianLattices.StabilizerLevels.PfB
theorem _root_.solution : HostEOverF := by
  intro e q d h L _ _ ζ a b hl x
  obtain ⟨_, _, hmul, hbij⟩ := hostGalois e q d h L ζ a b hl
  obtain ⟨c, hc⟩ := hbij.2 (cc e)
  have hreal := (Final.real e q d h L ζ a b hl).2
  have hone : galE e ζ a b 1 = 1 := by
    have := hmul 1 1
    rw [mul_one] at this
    exact (mul_eq_left.1 this.symm)
  have hcc : c * c = 1 := hbij.1 (by
    rw [hmul, hc, hone]
    simp [cc, c0, Prod.ext_iff])
  have hcc' : ∀ y, c (c y) = y := fun y => by
    have := congrArg (fun s : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b => s y) hcc
    simpa using this
  have hmem : ∀ y : hostE ζ a b, c y = y → y ∈ hostF ζ a b := fun y hy =>
    ((hreal y).1).2 (fun σ hσ => by rw [hbij.1 (hσ.trans hc.symm)]; exact hy)
  have hspec := hostGalSpec e q d h L ζ a b hl c
  have hca : c (aE ζ a b) = - aE ζ a b := by
    apply Subtype.ext
    rw [hspec.1, hc]
    simp [cc, c0, aE]
  have hcb : c (bE ζ a b) = - bE ζ a b := by
    apply Subtype.ext
    rw [hspec.2.1, hc]
    simp [cc, c0, bE]
  have ha0 : aE ζ a b ≠ 0 := by
    intro h0
    have : a = 0 := congrArg Subtype.val h0
    have h2 := hl.2.1
    rw [this] at h2
    have : (q : L) = 0 := by simpa using h2.symm
    exact h.1.ne_zero (by exact_mod_cast this)
  have hb0 : bE ζ a b ≠ 0 := by
    intro h0
    have : b = 0 := congrArg Subtype.val h0
    have h2 := hl.2.2.1
    rw [this] at h2
    have : (d : L) = 0 := by simpa using h2.symm
    exact h.2.1.ne_zero (by exact_mod_cast this)
  have gen : ∀ t : hostE ζ a b, c t = -t → t ≠ 0 →
      ∃ u ∈ hostF ζ a b, ∃ v ∈ hostF ζ a b, x = u + v * t := by
    intro t ht ht0
    refine ⟨(x + c x) / 2, hmem _ ?_, (x - c x) / (2 * t), hmem _ ?_, ?_⟩
    · simp only [map_div₀, map_add, hcc', map_ofNat]; ring
    · simp only [map_div₀, map_sub, map_mul, hcc', map_ofNat, ht]
      field_simp
      ring
    · field_simp
      ring
  exact ⟨gen _ hcb hb0, gen _ hca ha0⟩
end Formalism.HermitianLattices.StabilizerLevels.PfB
