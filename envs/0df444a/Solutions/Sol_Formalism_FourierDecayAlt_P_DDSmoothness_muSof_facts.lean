-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:42:15.392157+00:00
-- url     : https://prove2.me/submissions/2e350983-f3ca-40be-a542-f50b999212e2

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_uh_mul
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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    muSof μW μN ≠ 0 ∧ muSof μW μN {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0 := by
  obtain ⟨hWs, hW0, hWb, -⟩ := hW
  obtain ⟨hNs, hN0, hNb, -⟩ := hN
  haveI := hWs
  haveI := hNs
  have hcont : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have hmeas := hcont.measurable
  refine ⟨?_, ?_⟩
  · intro h0
    unfold muSof at h0
    rw [Measure.map_eq_zero_iff hmeas.aemeasurable] at h0
    have h1 : (μW.prod μN) Set.univ = 0 := by rw [h0, Measure.coe_zero, Pi.zero_apply]
    rw [← Set.univ_prod_univ, Measure.prod_prod, mul_eq_zero] at h1
    rcases h1 with h | h
    · exact hW0 (Measure.measure_univ_eq_zero.mp h)
    · exact hN0 (Measure.measure_univ_eq_zero.mp h)
  · unfold muSof
    rw [Measure.map_apply hmeas uh_measurableSet]
    refine measure_mono_null (t := {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UWset k r z} ×ˢ Set.univ ∪
      Set.univ ×ˢ {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r}) ?_ ?_
    · rintro ⟨a, b⟩ hab
      by_contra hno
      simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, true_and, Set.mem_setOf_eq, not_or,
        not_not] at hno
      exact hab (uh_mul hno.1.1 hno.2.1)
    · refine measure_union_null ?_ ?_
      · rw [Measure.prod_prod, hWb, zero_mul]
      · rw [Measure.prod_prod, hNb, mul_zero]
end Formalism.FourierDecayAlt.P.DDSmoothness
