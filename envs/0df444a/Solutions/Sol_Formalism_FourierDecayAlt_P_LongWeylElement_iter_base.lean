-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.iter_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:31:20.037298+00:00
-- url     : https://prove2.me/submissions/e5ccc84f-80e9-434b-b7a0-a6d1e7bc57de

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_sf
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_haar_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_cell_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_haar_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lint_smul3
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_bc_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
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
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
variable {k r r' : ℕ}
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution (HU : HaarUnique) (hCb : ClosedWb) (hNB : NBase) (k : ℕ) : IterAt k 0 := by
  intro μG μN μb hG hN hb
  have hUW : UWb k 0 = GV k 0 := by
    ext g
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, fun a => a.elim0⟩
  have hG' : IsHaarOn (UWb k 0) μG := by rw [hUW]; exact hG
  obtain ⟨c₀, hc₀, hce⟩ := haar_smul HU (hCb k 0) hb hG'
  have : SigmaFinite μb := sf hb
  let o : Mt k 0 := (1 : Mat k 0)
  have hNd : μN = μN {o} • Measure.dirac o := by
    rw [← Measure.restrict_singleton, Measure.restrict_eq_self_of_ae_mem]
    have h := haar_ae hN
    rw [hNB k] at h
    exact h
  have hfin : μN {o} ≠ ∞ := (hN.finite_compact {o} isCompact_singleton).ne
  have hne : μN {o} ≠ 0 := by
    intro h
    apply hN.ne_zero
    rw [hNd, h, zero_smul]
  obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, μN {o} = a := ⟨(μN {o}).toNNReal, (ENNReal.coe_toNNReal hfin).symm⟩
  have ha0 : a ≠ 0 := by
    intro h; apply hne; rw [ha, h]; rfl
  have hNd' : μN = a • Measure.dirac o := by
    rw [hNd, ha]; rfl
  refine ⟨c₀ * (a * a)⁻¹, by positivity, fun f hf => ?_⟩
  have hF : ∀ c : Fin 0 → ℂ, Measurable fun p : (Mt k 0 × Mt k 0) × Mt k 0 =>
      f ((Matrix.of p.1.1)⁻¹ * bigCell k 0 c 1 * Matrix.of p.2 * Matrix.of p.1.2) := fun c =>
    hf.comp (cell_meas (N := fun p : (Mt k 0 × Mt k 0) × Mt k 0 => p.1.1) (T := fun _ => bcF k 0 c) (M := fun p => p.2)
      (N' := fun p => p.1.2) (by fun_prop) measurable_const (by fun_prop) (by fun_prop))
  have inner : ∀ c : Fin 0 → ℂ, ∫⁻ p : (Mt k 0 × Mt k 0) × Mt k 0,
      f ((Matrix.of p.1.1)⁻¹ * bigCell k 0 c 1 * Matrix.of p.2 * Matrix.of p.1.2) ∂((μN.prod μN).prod μb) =
      ((a * a : ℝ≥0) : ℝ≥0∞) * ∫⁻ m, f m ∂μb := by
    intro c
    have h1 : μb = (1 : ℝ≥0) • μb := (one_smul _ _).symm
    rw [hNd']
    conv_lhs => rw [h1]
    rw [lint_smul3 (Measure.dirac o) μb a 1, mul_one, Measure.dirac_prod_dirac, Measure.dirac_prod,
      lintegral_map (hF c) measurable_prodMk_left]
    congr 1
    refine lintegral_congr fun m => ?_
    refine congrArg f ?_
    show ((1 : Mat k 0)⁻¹ * bigCell k 0 c 1 * Matrix.of m * (1 : Mat k 0) : Mat k 0) = Matrix.of m
    rw [bc_zero, inv_one, one_mul, one_mul, mul_one]
  simp only [inner]
  rw [volume_pi, Measure.pi_of_empty, lintegral_dirac, hce, lintegral_smul_measure]
  have hw : cWeight k 0 (fun a => isEmptyElim a) = 1 := by simp [cWeight]
  rw [hw, ENNReal.ofReal_one, one_mul, ← mul_assoc, ← ENNReal.coe_mul, ENNReal.smul_def, smul_eq_mul]
  congr 2
  field_simp
end Formalism.FourierDecayAlt.P.LongWeylElement
