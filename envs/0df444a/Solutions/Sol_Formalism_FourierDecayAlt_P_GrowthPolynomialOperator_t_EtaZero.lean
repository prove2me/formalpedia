-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_EtaZero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:58.883802+00:00
-- url     : https://prove2.me/submissions/39fb05c0-3de4-44ed-a596-ead7baa562cd

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_exp_mul_one_sub_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
section Num1
open Formalism.FourierDecayAlt.PB Finset
end Num1
section Num2
open Formalism.FourierDecayAlt.PB Finset
end Num2
section Num3
open Formalism.FourierDecayAlt.PB Finset
private theorem exp_le_quad_lemma (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + x + 2 * x ^ 2 := by
  have h := exp_mul_one_sub_le x
  have hp := Real.exp_pos x
  nlinarith [mul_nonneg (sq_nonneg x) (show (0:ℝ) ≤ 1 / 2 - x by linarith),
    mul_nonneg h0 (show (0:ℝ) ≤ 1 / 2 - x by linarith), mul_nonneg hp.le h0]
end Num3
section Num4
open Formalism.FourierDecayAlt.PB
end Num4
section Hil1
open Formalism.FourierDecayAlt.PB Finset
end Hil1
section Hil2
open Formalism.FourierDecayAlt.PB Finset
section
variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Terms τ Rw I H H₁)
end
end Hil2
section Hil3
open Formalism.FourierDecayAlt.PB Finset
end Hil3
section Hil4
open Formalism.FourierDecayAlt.PB Finset
open Classical
open scoped ComplexOrder
end Hil4
section Hil5
open Formalism.FourierDecayAlt.PB Finset
open Classical
section
variable {τ H₁ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
end
end Hil5
section Hil6
open Formalism.FourierDecayAlt.PB
end Hil6
section LocA
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB
open scoped ComplexOrder ComplexConjugate
open Classical
variable {E : Type} [Field E]
end LocA
section LocB
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB
open scoped ComplexOrder ComplexConjugate
open Classical
variable {E : Type} [Field E]
end LocB
section Loc
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB
open scoped ComplexOrder ComplexConjugate
open Classical
end Loc
section Lat
open NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB
end Lat
section Main
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Formalism.FourierDecayAlt.PB
open scoped ComplexOrder ComplexConjugate
end Main
section Loops
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB Finset
end Loops
section From
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB Finset NumberField
end From
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
open Formalism.FourierDecayAlt.PB Finset
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution : SqrtSumSqLeOneAddInvPowSix := by
  intro b Pg A ε ε' hb hPg0 hPg hA hε hε'
  have hb0 : 0 < b := by linarith
  obtain ⟨u, hu⟩ : ∃ u, u = (b ^ 7)⁻¹ := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; exact inv_pos.mpr (pow_pos hb0 7)
  have hb7 : (1000:ℝ) ≤ b ^ 7 := by
    have h16 : (16:ℝ) ^ 7 ≤ b ^ 7 := pow_le_pow_left₀ (by norm_num) hb 7
    have : (1000:ℝ) ≤ 16 ^ 7 := by norm_num
    linarith
  have hu1 : u ≤ 1 / 1000 := by
    rw [hu, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hb7
  have hw : (0:ℝ) ≤ 1 / 1000 - u := by linarith
  have h14 : (b ^ 14)⁻¹ = u ^ 2 := by
    rw [hu, inv_pow, ← pow_mul] <;> norm_num
  have h6 : 16 * u ≤ (b ^ 6)⁻¹ := by
    have e : (b ^ 6)⁻¹ = b * u := by
      have hbne : b ≠ 0 := hb0.ne'
      rw [hu]
      field_simp
      try ring
    rw [e]
    nlinarith
  rw [← hu] at hPg hA
  rw [h14] at hA hε hε'
  have hE : Real.exp (6 * u) ≤ 1 + 7 * u := by
    have := exp_le_quad_lemma (6 * u) (by linarith) (by linarith)
    nlinarith [mul_nonneg hu0.le hw]
  have hF : Real.exp (u ^ 2) ≤ 1 + u := by
    have := exp_le_quad_lemma (u ^ 2) (by positivity) (by nlinarith)
    nlinarith [mul_nonneg hu0.le hw, mul_nonneg (sq_nonneg u) hw,
      mul_nonneg (pow_nonneg hu0.le 3) hw]
  have hM : A + 2 * ε ≤ 1 + 3 * u := by
    have h1 : (1 + u) * Real.exp (u ^ 2) ≤ (1 + u) * (1 + u) :=
      mul_le_mul_of_nonneg_left hF (by linarith)
    nlinarith [mul_nonneg hu0.le hw]
  have hX : Pg * (A + 2 * ε) ≤ 1 + 11 * u := by
    have h1 : Pg * (A + 2 * ε) ≤ Pg * (1 + 3 * u) := mul_le_mul_of_nonneg_left hM hPg0
    have h2 : Pg * (1 + 3 * u) ≤ (1 + 7 * u) * (1 + 3 * u) :=
      mul_le_mul_of_nonneg_right (hPg.trans hE) (by linarith)
    nlinarith [mul_nonneg hu0.le hw]
  have hY : Pg * (ε + ε') ≤ 3 * u ^ 2 := by
    have h1 : Pg * (ε + ε') ≤ Pg * (2 * u ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hPg0
    have h2 : Pg * (2 * u ^ 2) ≤ (1 + 7 * u) * (2 * u ^ 2) :=
      mul_le_mul_of_nonneg_right (hPg.trans hE) (by positivity)
    nlinarith [mul_nonneg (sq_nonneg u) hw]
  have hs0 : 0 ≤ √(Pg * (A + 2 * ε)) := Real.sqrt_nonneg _
  have ht0 : 0 ≤ √(Pg * (ε + ε')) := Real.sqrt_nonneg _
  have hs2 : √(Pg * (A + 2 * ε)) ^ 2 ≤ 1 + 11 * u := by
    calc √(Pg * (A + 2 * ε)) ^ 2 ≤ (√(1 + 11 * u)) ^ 2 :=
          pow_le_pow_left₀ hs0 (Real.sqrt_le_sqrt hX) 2
      _ = 1 + 11 * u := Real.sq_sqrt (by linarith)
  have ht2 : √(Pg * (ε + ε')) ^ 2 ≤ 3 * u ^ 2 := by
    calc √(Pg * (ε + ε')) ^ 2 ≤ (√(3 * u ^ 2)) ^ 2 :=
          pow_le_pow_left₀ ht0 (Real.sqrt_le_sqrt hY) 2
      _ = 3 * u ^ 2 := Real.sq_sqrt (by positivity)
  have hc1 : (0:ℝ) ≤ 1 + 11 / 2 * u := by linarith
  have hc2 : (0:ℝ) ≤ 7 / 4 * u := by linarith
  have hsb : √(Pg * (A + 2 * ε)) ≤ 1 + 11 / 2 * u := by
    nlinarith [hs2, hs0, hc1, sq_nonneg u]
  have htb : √(Pg * (ε + ε')) ≤ 7 / 4 * u := by
    nlinarith [ht2, ht0, hc2, sq_nonneg u]
  calc (√(Pg * (A + 2 * ε)) + √(Pg * (ε + ε'))) ^ 2 ≤ (1 + 11 / 2 * u + 7 / 4 * u) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (add_le_add hsb htb) 2
    _ ≤ 1 + 16 * u := by nlinarith [mul_nonneg hu0.le hw]
    _ ≤ 1 + (b ^ 6)⁻¹ := by linarith
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
