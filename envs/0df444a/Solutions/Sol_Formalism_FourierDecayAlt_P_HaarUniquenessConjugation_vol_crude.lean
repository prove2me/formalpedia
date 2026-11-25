-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.vol_crude
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:26:12.322495+00:00
-- url     : https://prove2.me/submissions/d4f1941e-3f5f-4561-ab00-e926b02015ef

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftErrorLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarUniquenessConjugation
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_conj_back
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_phi_measurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_haar_unique
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_hs_eq_gN
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_hs_nonneg__00ab320385b4
import Theorems.Thm_Formalism_REAL_frobenius_mul_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
variable {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r}
namespace Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
theorem _root_.solution (hE : UJEmb) (hV : VolGrowth) (hC : UHConj) (hP : IsUnit P.det) (hH : Pᴴ * Jm ε * P = Hpk k r)
    (ν : Measure (Mt k r)) (hν : IsHaarOn (GV k r) ν) :
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ν {g | gN (Matrix.of g) ≤ R} ≤
      ENNReal.ofReal (C * R ^ (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2)) := by
  obtain ⟨c, rfl⟩ := haar_unique hE hC hP hH ν hν
  obtain ⟨C, hCV⟩ := hV _ ε
  have hm := phi_measurable (ε := ε) hE hP
  set M : ℝ := 1 + hs P * hs P⁻¹ with hM
  have hM0 : 0 ≤ hs P * hs P⁻¹ := mul_nonneg (hs_nonneg' _) (hs_nonneg' _)
  have hM1 : 1 ≤ M := by linarith
  refine ⟨c * (C * M ^ (2 * (2 * r + k + 1) ^ 2)), fun R hR => ?_⟩
  have hms : MeasurableSet {g : Mt k r | gN (Matrix.of g) ≤ R} := by
    have : Measurable fun g : Mt k r => gN (Matrix.of g) := by
      unfold gN
      apply Measurable.sqrt
      refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
      have : Measurable fun g : Mt k r => g i j := (measurable_pi_apply j).comp (measurable_pi_apply i)
      exact Complex.continuous_normSq.measurable.comp this
    exact this measurableSet_Iic
  rw [Measure.smul_apply, Measure.map_apply hm hms, ENNReal.smul_def, smul_eq_mul]
  have hsub : phi ε P ⁻¹' {g : Mt k r | gN (Matrix.of g) ≤ R} ⊆ {u : UJ ε | hsG u ≤ (M * R) ^ 2} := by
    intro u hu
    have hu' : gN (Matrix.of (phi ε P u)) ≤ R := hu
    have h0 : 0 ≤ gN (Matrix.of (phi ε P u)) := Real.sqrt_nonneg _
    have h1 : hs (Matrix.of (phi ε P u) : Mat k r) ≤ R ^ 2 := by
      rw [hs_eq_gN]; exact pow_le_pow_left₀ h0 hu' 2
    have h2 : ((u : (Mat k r)ˣ) : Mat k r) = P * Matrix.of (phi ε P u) * P⁻¹ := (conj_back hP _).symm
    show hs ((u : (Mat k r)ˣ) : Mat k r) ≤ _
    rw [h2]
    have h3 : hs (P * Matrix.of (phi ε P u) * P⁻¹) ≤ hs P * hs (Matrix.of (phi ε P u) : Mat k r) * hs P⁻¹ :=
      (frobenius_mul_le _ _).trans (mul_le_mul_of_nonneg_right (frobenius_mul_le _ _) (hs_nonneg' _))
    have h4 : hs P * hs (Matrix.of (phi ε P u) : Mat k r) * hs P⁻¹ ≤ (hs P * hs P⁻¹) * R ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 hM0
      nlinarith
    have h5 : (hs P * hs P⁻¹) * R ^ 2 ≤ (M * R) ^ 2 := by
      rw [mul_pow]
      have : hs P * hs P⁻¹ ≤ M ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (sq_nonneg R)
    linarith
  have hMR : 1 ≤ M * R := by nlinarith
  have e : R ^ (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) = R ^ (2 * (2 * r + k + 1) ^ 2) := by
    rw [← Real.rpow_natCast R (2 * (2 * r + k + 1) ^ 2)]; push_cast; rfl
  calc (c : ℝ≥0∞) * muG ε (phi ε P ⁻¹' {g : Mt k r | gN (Matrix.of g) ≤ R})
      ≤ (c : ℝ≥0∞) * ENNReal.ofReal (C * (M * R) ^ (2 * (2 * r + k + 1) ^ 2)) :=
        mul_le_mul_right ((measure_mono hsub).trans (hCV _ hMR)) _
    _ = ENNReal.ofReal (c * (C * M ^ (2 * (2 * r + k + 1) ^ 2)) * R ^ (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2)) := by
        rw [e, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul c.coe_nonneg, mul_pow]
        congr 1; ring
end Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
