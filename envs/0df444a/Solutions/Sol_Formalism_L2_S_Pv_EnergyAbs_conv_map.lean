-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.conv_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:00:08.755366+00:00
-- url     : https://prove2.me/submissions/67b1654c-22f5-4cc2-a168-041e21953ef2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerConv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {S : Set G} {μS : Measure G} [SFinite μS] (hS : IsHaarSub S μS) {Ω : Set G}
    (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S) :
    ((μS.restrict Ω).prod (μS.restrict Ω)).map (fun p : G × G => p.1 * p.2⁻¹) = μS.withDensity (cnt μS Ω) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, hright, -⟩ := hS
  have hg : Measurable (fun p : G × G => p.1 * p.2⁻¹) := measurable_fst.mul measurable_snd.inv
  ext A hA
  rw [Measure.map_apply hg hA, withDensity_apply _ hA]
  set P : Set (G × G) := {p | p.1 ∈ A ∧ p.2 ∈ Ω ∧ p.1 * p.2 ∈ Ω} with hPdef
  have hP : MeasurableSet P :=
    (measurable_fst hA).inter ((measurable_snd hΩm).inter ((measurable_fst.mul measurable_snd) hΩm))
  have h1 : (μS.prod μS) P = ∫⁻ q in A, cnt μS Ω q ∂μS := by
    rw [Measure.prod_apply hP, ← lintegral_indicator hA]
    refine lintegral_congr fun q => ?_
    rw [Set.indicator_apply]
    by_cases hq : q ∈ A
    · rw [if_pos hq]
      unfold cnt
      congr 1
      ext t
      simp [hPdef, hq]
    · rw [if_neg hq]
      have hempty : Prod.mk q ⁻¹' P = ∅ := by
        ext t
        simp [hPdef, hq]
      rw [hempty, measure_empty]
  have h2 : (μS.prod μS) P =
      ((μS.restrict Ω).prod (μS.restrict Ω)) ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A) := by
    rw [Measure.prod_apply_symm hP, Measure.prod_apply_symm (hg hA), ← lintegral_indicator hΩm]
    refine lintegral_congr fun t => ?_
    rw [Set.indicator_apply]
    by_cases ht : t ∈ Ω
    · rw [if_pos ht]
      have hBt : MeasurableSet
          ((fun x => (x, t)) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A)) :=
        (measurable_mul_const t⁻¹) hA
      rw [Measure.restrict_apply hBt]
      have hmt := hright t (hΩS ht)
      calc μS ((fun x => (x, t)) ⁻¹' P)
          = μS ((fun x => x * t) ⁻¹'
              ((fun x => (x, t)) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A) ∩ Ω)) := by
            congr 1
            ext q
            simp [hPdef, ht]
        _ = (μS.map (fun x => x * t))
              ((fun x => (x, t)) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A) ∩ Ω) :=
            (Measure.map_apply (measurable_mul_const t) (hBt.inter hΩm)).symm
        _ = μS ((fun x => (x, t)) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A) ∩ Ω) := by
            rw [hmt]
    · rw [if_neg ht]
      have hempty : (fun x => (x, t)) ⁻¹' P = ∅ := by
        ext q
        simp [hPdef, ht]
      rw [hempty, measure_empty]
  exact h2.symm.trans h1
end Formalism.L2.S.Pv.EnergyAbs
