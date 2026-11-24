-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.adj_sub_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:43:55.844066+00:00
-- url     : https://prove2.me/submissions/103c25d1-c94e-40a8-b6d3-52188bb94af5

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_inv_mem_I
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_abs_inv_sub_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dg_norm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dg_sub_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_adj_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ne_zero_of_mem_I
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_four_pow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private lemma entry_le_lemma (A : Mat k r) (i j : Fin (2 * r + k + 1)) : ‖A i j‖ ≤ ‖A‖ := by
  first
    | exact Matrix.norm_entry_le_entrywise_sup_norm A
    | exact (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)
private lemma norm_le_lemma_2 {A : Mat k r} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i j, ‖A i j‖ ≤ c) :
    ‖A‖ ≤ c := by
  first
    | exact (Matrix.norm_le_iff hc).mpr h
    | exact (pi_norm_le_iff_of_nonneg hc).mpr fun i => (pi_norm_le_iff_of_nonneg hc).mpr (h i)
section
variable {t : ℝ × ℝ} (h1 : t.1 ∈ Set.Icc (1 / 2 : ℝ) 2) (h2 : t.2 ∈ Set.Icc (1 / 2 : ℝ) 2)
include h1 h2
end
end Formalism.FourierDecayAlt.P.B4
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {τ : ℝ} (hτ : τ ∈ Set.Icc (1 / 2 : ℝ) 2) (X : Mat k r) :
    ‖(aDil k r τ)⁻¹ * X * aDil k r τ - X‖ ≤ 8 * 4 ^ r * |τ - 1| * ‖X‖ := by
  have hτ0 := ne_zero_of_mem_I hτ
  have hA : 0 ≤ |τ - 1| := abs_nonneg _
  apply norm_le_lemma_2 (by positivity)
  intro i j
  rw [Matrix.sub_apply, adj_apply hτ0]
  have e : dg k r τ⁻¹ i * X i j * dg k r τ j - X i j =
      X i j * (dg k r τ⁻¹ i * (dg k r τ j - 1) + (dg k r τ⁻¹ i - 1)) := by ring
  rw [e, norm_mul]
  have a1 := dg_norm_le (k := k) (inv_mem_I hτ) i
  have a2 := dg_sub_one (k := k) hτ j
  have a3 := dg_sub_one (k := k) (inv_mem_I hτ) i
  have a4 := abs_inv_sub_one hτ
  have a5 : ‖X i j‖ ≤ ‖X‖ := entry_le_lemma X i j
  have a6 : ‖dg k r τ⁻¹ i - 1‖ ≤ 2 ^ (r + 1) * (2 * |τ - 1|) :=
    a3.trans (mul_le_mul_of_nonneg_left a4 (by positivity))
  have b : ‖dg k r τ⁻¹ i * (dg k r τ j - 1) + (dg k r τ⁻¹ i - 1)‖ ≤ 8 * 4 ^ r * |τ - 1| := by
    calc _ ≤ ‖dg k r τ⁻¹ i * (dg k r τ j - 1)‖ + ‖dg k r τ⁻¹ i - 1‖ := norm_add_le _ _
      _ = ‖dg k r τ⁻¹ i‖ * ‖dg k r τ j - 1‖ + ‖dg k r τ⁻¹ i - 1‖ := by rw [norm_mul]
      _ ≤ 2 ^ r * (2 ^ (r + 1) * |τ - 1|) + 2 ^ (r + 1) * (2 * |τ - 1|) := by gcongr
      _ ≤ 8 * 4 ^ r * |τ - 1| := by
          rw [four_pow, pow_succ]
          have h2r : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
          have h3 := mul_le_mul_of_nonneg_right (show (2 : ℝ) ^ r ≤ 2 ^ r * 2 ^ r by nlinarith) hA
          have h4 : 0 ≤ 2 ^ r * 2 ^ r * |τ - 1| := by positivity
          nlinarith
  calc ‖X i j‖ * _ ≤ ‖X‖ * (8 * 4 ^ r * |τ - 1|) := by gcongr
    _ = 8 * 4 ^ r * |τ - 1| * ‖X‖ := by ring
end Formalism.FourierDecayAlt.P.B4
