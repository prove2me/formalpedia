-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.quot_zero_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:09:43.553908+00:00
-- url     : https://prove2.me/submissions/b048b412-0eba-4ffb-8347-01ca351edccd

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_FrameInvMulVecNegativeVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_measurable_mulMt
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
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS νq) (f : Formalism.QuantumDeterminants.Mt k r → ℝ) (hfm : Measurable f)
    (hfi : Integrable f μG) (hin : ∀ᵐ x ∂νq, ∫ s, f (mulMt s x) ∂μS = 0) : ∫ x, f x ∂μG = 0 := by
  have hmm : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => f (mulMt p.2 p.1)) :=
    hfm.comp (measurable_mulMt.comp measurable_swap)
  have hab : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => ENNReal.ofReal |f (mulMt p.2 p.1)|) :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hmm)
  have hG := hab.lintegral_prod_right' (ν := μS)
  have hqa := hq (fun y => ENNReal.ofReal |f y|) (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hfm))
  have hfin : ∫⁻ x, ∫⁻ s, ENNReal.ofReal |f (mulMt s x)| ∂μS ∂νq ≠ ⊤ := by
    have h1 : ∫⁻ y, ENNReal.ofReal |f y| ∂μG < ⊤ := hfi.abs.lintegral_lt_top
    rw [hqa] at h1
    exact h1.ne
  have hae := ae_lt_top hG hfin
  have hpos := hq (fun y => ENNReal.ofReal (f y)) (ENNReal.measurable_ofReal.comp hfm)
  have hneg := hq (fun y => ENNReal.ofReal (-f y)) (ENNReal.measurable_ofReal.comp hfm.neg)
  have heq : ∫⁻ y, ENNReal.ofReal (f y) ∂μG = ∫⁻ y, ENNReal.ofReal (-f y) ∂μG := by
    rw [hpos, hneg]
    refine lintegral_congr_ae ((hae.and hin).mono fun x hx => ?_)
    obtain ⟨hxG, hx0⟩ := hx
    have hxG' : ∫⁻ s, ENNReal.ofReal |f (mulMt s x)| ∂μS < ⊤ := hxG
    have hmeasx : Measurable (fun s : Formalism.QuantumDeterminants.Mt k r => f (mulMt s x)) :=
      hfm.comp (continuous_mulMt_right_const x).measurable
    have hint : Integrable (fun s => f (mulMt s x)) μS := by
      refine ⟨hmeasx.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_norm]
      simpa only [Real.norm_eq_abs] using hxG'
    have hp : ∫⁻ s, ENNReal.ofReal (f (mulMt s x)) ∂μS ≠ ⊤ :=
      (lt_of_le_of_lt (lintegral_mono fun s => ENNReal.ofReal_le_ofReal (le_abs_self _)) hxG').ne
    have hn : ∫⁻ s, ENNReal.ofReal (-f (mulMt s x)) ∂μS ≠ ⊤ :=
      (lt_of_le_of_lt (lintegral_mono fun s => ENNReal.ofReal_le_ofReal (neg_le_abs _)) hxG').ne
    have h2 := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint
    rw [hx0] at h2
    exact (ENNReal.toReal_eq_toReal_iff' hp hn).mp (sub_eq_zero.mp h2.symm)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi, heq, sub_self]
end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
