-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:36:34.572797+00:00
-- url     : https://prove2.me/submissions/7efefef4-fae3-4b17-bf38-c742deee9e82

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_uh_cancel
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_uh_measurableSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness
open Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.DDSmoothness
theorem _root_.solution {μG μS νq : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hG : μG {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    (hS0 : μS ≠ 0) (hS : μS {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS νq) :
    ∀ᵐ x ∂νq, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  classical
  set B : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} with hBdef
  have hBm : MeasurableSet B := uh_measurableSet
  have key := hq (B.indicator 1) (measurable_one.indicator hBm)
  rw [lintegral_indicator_one hBm, hG] at key
  have hc : μS Bᶜ ≠ 0 := by
    intro h0
    apply hS0
    rw [← Measure.measure_univ_eq_zero]
    refine le_antisymm ?_ zero_le
    calc μS Set.univ = μS (B ∪ Bᶜ) := by rw [Set.union_compl_self]
      _ ≤ μS B + μS Bᶜ := measure_union_le _ _
      _ = 0 := by rw [hS, h0, add_zero]
  have hle : ∀ x, μS Bᶜ * B.indicator 1 x ≤
      ∫⁻ s, B.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one, ← lintegral_indicator_one hBm.compl]
      refine lintegral_mono fun s => ?_
      by_cases hs : Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)
      · have hsx : (fun i j => (Matrix.of s * Matrix.of x) i j) ∈ B := fun hmem =>
          hx (uh_cancel (x := Matrix.of x) hs hmem)
        have hsB : s ∈ Bᶜ := fun h => h hs
        rw [Set.indicator_of_mem hsB, Set.indicator_of_mem hsx]
        exact le_rfl
      · have hsB : s ∉ Bᶜ := fun h => h hs
        rw [Set.indicator_of_notMem hsB]
        exact zero_le
    · rw [Set.indicator_apply, if_neg hx, mul_zero]
      exact zero_le
  have h0 : μS Bᶜ * νq B = 0 := by
    rw [← lintegral_indicator_one hBm, ← lintegral_const_mul _ (measurable_one.indicator hBm)]
    refine le_antisymm ?_ zero_le
    calc ∫⁻ x, μS Bᶜ * B.indicator 1 x ∂νq
        ≤ ∫⁻ x, ∫⁻ s, B.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ∂νq := lintegral_mono hle
      _ = 0 := key.symm
  have hνB : νq B = 0 := (mul_eq_zero.mp h0).resolve_left hc
  rw [ae_iff]
  exact hνB
end Formalism.FourierDecayAlt.P.DDSmoothness
