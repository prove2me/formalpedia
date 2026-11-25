-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.big_cell_density_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:14.367899+00:00
-- url     : https://prove2.me/submissions/707c04b6-1dd4-4529-8b52-83862ed2731b

import Definitions.Def_Formalism_HermitianCurvature_LemmaDensOfSteps
import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LUFactorOrbitBounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThresholdOfLargeConstant
import Theorems.Thm_Formalism_FourierDecayAlt_P_xi_eq_xiTau_one_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_threshold_of_large_constant
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_DifferentialOperatorClasses_inCC_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_bessel_function_trivial_index
import Theorems.Thm_Formalism_FourierDecayAlt_P_bessel_integral_converges
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
open Matrix MeasureTheory
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.DensityAveraging.DensBigOfParts := by
  intro hR
  refine ⟨19, ?_⟩
  intro CV hCV k r Wp Wq _ _ _ _ _ _ D A ε mm F' γ H hγ hrel O
  obtain ⟨hr, hε, hA, hmm, hF, hsupp, hbig⟩ := H
  have hRs : Rset γ = {1} := hR k r Wp Wq D γ hγ hrel
  have hconc : O.μR ({(1 : B.Mat k r)} : Set (Mt k r))ᶜ = 0 := by
    have := O.haarR.conc
    rw [hRs] at this
    exact this
  have hone : O.μR ({(1 : B.Mat k r)} : Set (Mt k r)) < ⊤ :=
    O.haarR.finite_compact _ isCompact_singleton
  have hfin : O.μR Set.univ < ⊤ := by
    calc O.μR Set.univ = O.μR (({(1 : B.Mat k r)} : Set (Mt k r)) ∪ ({(1 : B.Mat k r)} : Set (Mt k r))ᶜ) := by
          rw [Set.union_compl_self]
      _ ≤ O.μR ({(1 : B.Mat k r)} : Set (Mt k r)) + O.μR ({(1 : B.Mat k r)} : Set (Mt k r))ᶜ := measure_union_le _ _
      _ < ⊤ := by rw [hconc, add_zero]; exact hone
  have hne : O.μR Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr O.haarR.ne_zero
  set c : ℝ := O.μR.real Set.univ with hc_def
  have hc : 0 < c := by
    rw [hc_def, measureReal_def]; exact ENNReal.toReal_pos hne hfin.ne
  have hγOm : γ ∈ JF.Om k r D.z D.z' := ⟨hγ.1, fun l _ => hγ.2.2 l (Finset.mem_univ _), hγ.2.1⟩
  have hThr : JF.TransportedAlt k r A 0 := threshold_of_large_constant hr hCV hA
  have hint0 := (bessel_integral_converges k r Wp Wq D A F' hThr (DifferentialOperatorClasses.inCC_mono (Nat.zero_le mm) hF)).1 γ hγOm
  have hθ : ∀ p : B.SS k r, D.inSS p →
      ∫ x, (fun _ : B.SS k r => c⁻¹) (actR γ (Matrix.of x) p) ∂O.μR = 1 := by
    intro p _
    simp only [integral_const, smul_eq_mul]
    rw [← hc_def]; field_simp
  have hfun : (fun p : B.SS k r => (fun _ : B.SS k r => c⁻¹) p • (B.xiTau D (1, 1) p • B.rho D p F' γ)) =
      fun p => c⁻¹ • JF.integrand D F' γ p := by
    funext p; simp only [JF.integrand, xi_eq_xiTau_one_one]
  have hint : Integrable (fun p : B.SS k r => (fun _ : B.SS k r => c⁻¹) p • (B.xiTau D (1, 1) p • B.rho D p F' γ))
      D.μSS := by
    rw [hfun]; exact hint0.smul c⁻¹
  have hw := O.weil F' (fun _ => c⁻¹) measurable_const (fun _ => by positivity) hθ hint
  rw [← hw, integral_smul]
  have hJ : ∫ p, B.xiTau D (1, 1) p • B.rho D p F' γ ∂D.μSS = 0 := by
    have h1 : B.Jtau D (1, 1) F' γ = B.JF D F' γ := bessel_function_trivial_index k r Wp Wq D F' γ
    rw [hbig γ hγ] at h1
    exact h1
  rw [hJ, smul_zero]
end Formalism.FourierDecayAlt.P
