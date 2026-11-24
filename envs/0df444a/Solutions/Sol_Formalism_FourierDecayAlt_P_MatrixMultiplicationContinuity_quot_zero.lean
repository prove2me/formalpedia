-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.quot_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:33:52.278381+00:00
-- url     : https://prove2.me/submissions/428f0281-c622-4bc9-bdc4-0ed6af09a2d1

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_FrameInvMulVecNegativeVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_measurable_mulMt
import Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_quot_zero_real
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
private theorem continuous_mulMt_right_const {k r : ℕ} (x : Formalism.QuantumDeterminants.Mt k r) :
    Continuous (fun s : Formalism.QuantumDeterminants.Mt k r => mulMt s x) := by
  unfold mulMt
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop
section Groups
variable {k r : ℕ}
end Groups
section Pi
variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
end Pi
section Sigma
variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end Sigma
end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
end
end

set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
set_option maxHeartbeats 800000
namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
theorem _root_.solution {k r : ℕ} {μG μS νq : Measure (Formalism.QuantumDeterminants.Mt k r)} [SFinite μS]
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS νq) (F : Formalism.QuantumDeterminants.Mt k r → ℂ) (hFm : Measurable F)
    (hFi : Integrable F μG) (hin : ∀ᵐ x ∂νq, ∫ s, F (mulMt s x) ∂μS = 0) : ∫ x, F x ∂μG = 0 := by
  have hmm : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => F (mulMt p.2 p.1)) :=
    hFm.comp (measurable_mulMt.comp measurable_swap)
  have hab : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => ENNReal.ofReal ‖F (mulMt p.2 p.1)‖) :=
    ENNReal.measurable_ofReal.comp hmm.norm
  have hG := hab.lintegral_prod_right' (ν := μS)
  have hqa := hq (fun y => ENNReal.ofReal ‖F y‖) (ENNReal.measurable_ofReal.comp hFm.norm)
  have hfin : ∫⁻ x, ∫⁻ s, ENNReal.ofReal ‖F (mulMt s x)‖ ∂μS ∂νq ≠ ⊤ := by
    have h1 : ∫⁻ y, ENNReal.ofReal ‖F y‖ ∂μG < ⊤ := hFi.norm.lintegral_lt_top
    rw [hqa] at h1
    exact h1.ne
  have hae := ae_lt_top hG hfin
  have hint : ∀ᵐ x ∂νq, Integrable (fun s => F (mulMt s x)) μS := by
    refine hae.mono fun x hx => ⟨(hFm.comp (continuous_mulMt_right_const x).measurable).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    exact hx
  have hre := quot_zero_real hq (fun y => (F y).re) (Complex.measurable_re.comp hFm)
    (Complex.reCLM.integrable_comp hFi) ((hint.and hin).mono fun x hx => by
      have e := Complex.reCLM.integral_comp_comm hx.1
      simp only [Complex.reCLM_apply] at e
      show ∫ s, (F (mulMt s x)).re ∂μS = 0
      rw [e, hx.2, Complex.zero_re])
  have him := quot_zero_real hq (fun y => (F y).im) (Complex.measurable_im.comp hFm)
    (Complex.imCLM.integrable_comp hFi) ((hint.and hin).mono fun x hx => by
      have e := Complex.imCLM.integral_comp_comm hx.1
      simp only [Complex.imCLM_apply] at e
      show ∫ s, (F (mulMt s x)).im ∂μS = 0
      rw [e, hx.2, Complex.zero_im])
  have er := Complex.reCLM.integral_comp_comm hFi
  have ei := Complex.imCLM.integral_comp_comm hFi
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at er ei
  apply Complex.ext
  · rw [Complex.zero_re, ← er]
    exact hre
  · rw [Complex.zero_im, ← ei]
    exact him
end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
