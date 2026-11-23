-- Prove2me | solution 1 for CompanionTheory.D.Upq.ModEx.modular_aut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:06.376724+00:00
-- url     : https://prove2.me/submissions/4be18766-365d-4c69-b691-a88f7440a0e2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_map_mul_right_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Matrix TopologicalSpace
open scoped ENNReal NNReal Pointwise
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.ModEx
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
namespace CompanionTheory.D.Upq.ModEx
theorem _root_.solution (α : H ≃ₜ* H) (g : H) :
    modularCharacterFun (α g) = modularCharacterFun g := by
  set μ : Measure H := haar
  set ν : Measure H := map α μ with hν
  have hαm : Measurable α := α.continuous.measurable
  have h1 : map (· * α g) ν = modularCharacterFun (α g) • ν := map_mul_right_eq ν (α g)
  have h2 : map (· * α g) ν = modularCharacterFun g • ν := by
    rw [hν, map_map (measurable_mul_const _) hαm]
    have : (fun x => x * α g) ∘ α = α ∘ (fun x => x * g) := by
      ext x; simp
    rw [this, ← map_map hαm (measurable_mul_const _), map_mul_right_eq μ g, Measure.map_smul]
  have K : PositiveCompacts H := Classical.arbitrary _
  have hpos : ν K ≠ 0 := (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have hfin : ν K ≠ ∞ := K.isCompact.measure_lt_top.ne
  have h3 : (modularCharacterFun (α g) • ν) K = (modularCharacterFun g • ν) K := by
    rw [← h1, h2]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
  exact_mod_cast (ENNReal.mul_left_inj hpos hfin).1 h3
end CompanionTheory.D.Upq.ModEx
