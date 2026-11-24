-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NormBallVolumes.shellInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:22:54.1372+00:00
-- url     : https://prove2.me/submissions/2404aea0-2c62-4fc5-b753-aedfda4555a4

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftingTheory
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormBallVolumes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology Metric
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NormBallVolumes
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.NormBallVolumes
theorem _root_.solution : ShellInt := by
  intro X _ μ N C d A hN h1 hd hV hA
  have hA0 : 0 < A := lt_of_le_of_lt hd hA
  let S : ℕ → Set X := fun j => {x | N x ≤ (2 : ℝ) ^ (j + 1)}
  let c : ℕ → ℝ := fun j => ((2 : ℝ) ^ j) ^ (-A)
  have hSm : ∀ j, MeasurableSet (S j) := fun j => measurableSet_le hN measurable_const
  have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal (N x ^ (-A)) ≤ ∑' j, (S j).indicator (fun _ => ENNReal.ofReal (c j)) x := by
    filter_upwards [h1] with x hx
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near hx one_lt_two
    refine le_trans ?_ (ENNReal.le_tsum j)
    rw [Set.indicator_of_mem (show x ∈ S j from hj2.le)]
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hj1 (by linarith)
  have hterm : ∀ j : ℕ, c j * (C * ((2 : ℝ) ^ (j + 1)) ^ d) = C * (2 : ℝ) ^ d * ((2 : ℝ) ^ (d - A)) ^ j := by
    intro j
    have h2 : (0 : ℝ) < 2 := two_pos
    have e1 : c j = (2 : ℝ) ^ ((j : ℝ) * (-A)) := by
      show ((2 : ℝ) ^ j) ^ (-A) = _
      rw [← Real.rpow_natCast 2 j, ← Real.rpow_mul h2.le]
    have e2 : ((2 : ℝ) ^ (j + 1)) ^ d = (2 : ℝ) ^ (((j : ℝ) + 1) * d) := by
      rw [← Real.rpow_natCast 2 (j + 1), ← Real.rpow_mul h2.le]
      push_cast
      rfl
    have e3 : ((2 : ℝ) ^ (d - A)) ^ j = (2 : ℝ) ^ ((d - A) * (j : ℝ)) := by
      rw [Real.rpow_mul_natCast h2.le]
    rw [e1, e2, e3]
    have e4 : (2 : ℝ) ^ ((j : ℝ) * (-A)) * (2 : ℝ) ^ (((j : ℝ) + 1) * d) = (2 : ℝ) ^ d * (2 : ℝ) ^ ((d - A) * (j : ℝ)) := by
      rw [← Real.rpow_add h2, ← Real.rpow_add h2]
      congr 1
      ring
    calc (2 : ℝ) ^ ((j : ℝ) * (-A)) * (C * (2 : ℝ) ^ (((j : ℝ) + 1) * d))
        = C * ((2 : ℝ) ^ ((j : ℝ) * (-A)) * (2 : ℝ) ^ (((j : ℝ) + 1) * d)) := by ring
      _ = _ := by rw [e4]; ring
  have hsum : Summable fun j : ℕ => c j * (C * ((2 : ℝ) ^ (j + 1)) ^ d) := by
    simp only [hterm]
    apply Summable.mul_left
    exact summable_geometric_of_lt_one (Real.rpow_nonneg two_pos.le _)
      (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith))
  calc (∫⁻ x, ENNReal.ofReal (N x ^ (-A)) ∂μ)
      ≤ ∫⁻ x, ∑' j, (S j).indicator (fun _ => ENNReal.ofReal (c j)) x ∂μ := lintegral_mono_ae hpt
    _ = ∑' j, ∫⁻ x, (S j).indicator (fun _ => ENNReal.ofReal (c j)) x ∂μ :=
        lintegral_tsum fun j => (measurable_const.indicator (hSm j)).aemeasurable
    _ = ∑' j, ENNReal.ofReal (c j) * μ (S j) := by
        congr 1
        funext j
        exact lintegral_indicator_const (hSm j) _
    _ ≤ ∑' j, ENNReal.ofReal (c j) * ENNReal.ofReal (C * ((2 : ℝ) ^ (j + 1)) ^ d) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        gcongr
        exact hV _ (one_le_pow₀ one_le_two)
    _ = ∑' j, ENNReal.ofReal (c j * (C * ((2 : ℝ) ^ (j + 1)) ^ d)) := by
        congr 1
        funext j
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
    _ < ∞ := hsum.tsum_ofReal_lt_top
end Formalism.FourierDecayAlt.P.NormBallVolumes
