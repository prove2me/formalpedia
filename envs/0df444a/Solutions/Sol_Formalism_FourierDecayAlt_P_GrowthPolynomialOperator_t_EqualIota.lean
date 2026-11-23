-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_EqualIota
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:33.944516+00:00
-- url     : https://prove2.me/submissions/c2ba0be7-31e3-4cf7-b36c-011c238fa6d6

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
open Formalism.FourierDecayAlt.PB Finset
open Classical
open scoped ComplexOrder
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution : GramSumLeOfPosSemidef := by
  intro I H₁ _ _ _ Γ c a hM
  obtain ⟨m, v, hv0⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hM
  have hM' : ∀ i j, ((c : ℂ) • (1 : Matrix I I ℂ) - Matrix.of Γ) i j = ∑ l, v l i * star (v l j) := by
    intro i j
    rw [hv0]
    simp [Matrix.sum_apply, Matrix.vecMulVec_apply]
  have hw : ∀ l, inner ℂ (∑ i, star (v l i) • a i) (∑ i, star (v l i) • a i) =
      ∑ i, ∑ j, v l i * star (v l j) * inner ℂ (a i) (a j) := by
    intro l
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, starRingEnd_apply,
      star_star, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hsum : ∑ i, ∑ j, ((c : ℂ) • (1 : Matrix I I ℂ) - Matrix.of Γ) i j * inner ℂ (a i) (a j) =
      ∑ l, inner ℂ (∑ i, star (v l i) • a i) (∑ i, star (v l i) • a i) := by
    simp_rw [hw, hM', Finset.sum_mul]
    calc ∑ i, ∑ j, ∑ l, v l i * star (v l j) * inner ℂ (a i) (a j)
        = ∑ i, ∑ l, ∑ j, v l i * star (v l j) * inner ℂ (a i) (a j) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ l, ∑ i, ∑ j, v l i * star (v l j) * inner ℂ (a i) (a j) := Finset.sum_comm
  have hnn : 0 ≤ (∑ l, inner ℂ (∑ i, star (v l i) • a i) (∑ i, star (v l i) • a i)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_nonneg (fun l _ => ?_)
    have := inner_self_nonneg (𝕜 := ℂ) (x := ∑ i, star (v l i) • a i)
    simpa using this
  have hsplit : ∑ i, ∑ j, ((c : ℂ) • (1 : Matrix I I ℂ) - Matrix.of Γ) i j * inner ℂ (a i) (a j) =
      (c : ℂ) * ∑ i, inner ℂ (a i) (a i) - ∑ i, ∑ j, Γ i j * inner ℂ (a i) (a j) := by
    simp [Matrix.sub_apply, Matrix.one_apply, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, ite_mul]
  have hre : ((c : ℂ) * ∑ i, inner ℂ (a i) (a i)).re = c * ∑ i, ‖a i‖ ^ 2 := by
    rw [Complex.re_ofReal_mul, Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (a i)
  rw [hsum] at hsplit
  have htot := congrArg Complex.re hsplit
  rw [Complex.sub_re, hre] at htot
  linarith
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
