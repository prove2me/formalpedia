-- Prove2me | solution 1 for CompanionTheory.D.Upq.ModEx.modular_bdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:06.70691+00:00
-- url     : https://prove2.me/submissions/6495a071-0ea9-4eb3-a2ba-02cc1218f05d

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
theorem _root_.solution {V : Set H} (hV : IsCompact V) :
    ∃ M : ℝ, ∀ v ∈ V, (modularCharacterFun v : ℝ) ≤ M := by
  set μ : Measure H := haar
  have K : PositiveCompacts H := Classical.arbitrary _
  set A : Set H := closure (K : Set H) with hA
  have hAc : IsCompact A := K.isCompact.closure
  have hAm : MeasurableSet A := isClosed_closure.measurableSet
  have hpos : μ A ≠ 0 :=
    (measure_pos_of_nonempty_interior _
      (K.interior_nonempty.mono (interior_mono subset_closure))).ne'
  have hfin : μ A ≠ ∞ := hAc.measure_lt_top.ne
  have hB : IsCompact (A * V⁻¹) := hAc.mul hV.inv
  have hBfin : μ (A * V⁻¹) ≠ ∞ := hB.measure_lt_top.ne
  refine ⟨(μ (A * V⁻¹) / μ A).toReal, fun v hv => ?_⟩
  have h1 : (modularCharacterFun v : ℝ≥0∞) * μ A ≤ μ (A * V⁻¹) := by
    have h := congrArg (fun ρ : Measure H => ρ A) (map_mul_right_eq μ v)
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    rw [← h, map_apply (measurable_mul_const _) hAm]
    refine measure_mono fun x hx => ?_
    exact ⟨x * v, hx, v⁻¹, by simpa using hv, by simp⟩
  have h2 : (modularCharacterFun v : ℝ≥0∞) ≤ μ (A * V⁻¹) / μ A :=
    (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl hfin)).2 h1
  have h3 := ENNReal.toReal_mono (ENNReal.div_ne_top hBfin hpos) h2
  simpa using h3
end CompanionTheory.D.Upq.ModEx
