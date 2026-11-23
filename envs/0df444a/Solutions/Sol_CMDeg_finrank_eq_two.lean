-- Prove2me | solution 1 for CMDeg.finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:31.258414+00:00
-- url     : https://prove2.me/submissions/742d24fb-5c47-4b9c-b102-ef81c17cad18

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_MassRatio
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDegreeEquality_FinrankEqTwo
import Theorems.Thm_CMDeg_sigma_sq
import Theorems.Thm_CMDeg_sigma_ne_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open CMDeg
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
namespace CMDeg
theorem _root_.solution (hFE : Formalism.L2.SG.MassRatio.IsCMPair F E) : finrank F E = 2 := by
  obtain ⟨hE, hR⟩ := hFE
  have hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x := by
    intro x
    have : algebraMap F E x ∈ Set.range (algebraMap F E) := ⟨x, rfl⟩
    rw [hR] at this
    exact this
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let σ := sigma hfix
  let H : Subgroup (E ≃ₐ[F] E) := Subgroup.zpowers σ
  have hord : orderOf σ = 2 := orderOf_eq_prime (sigma_sq hfix) (sigma_ne_one hE hfix)
  have hcard : finrank (IntermediateField.fixedField H) E = 2 := by
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hord]
  have hbot : IntermediateField.fixedField H = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hx' : star x = x := hx σ (Subgroup.mem_zpowers σ)
    rw [IntermediateField.mem_bot, hR]
    exact hx'
  have h1 : finrank F (IntermediateField.fixedField H) = 1 :=
    IntermediateField.finrank_eq_one_iff.mpr hbot
  rw [← Module.finrank_mul_finrank F (IntermediateField.fixedField H) E, h1, hcard, one_mul]
end CMDeg
