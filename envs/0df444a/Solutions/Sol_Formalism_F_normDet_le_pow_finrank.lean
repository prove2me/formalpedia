-- Prove2me | solution 1 for Formalism.F.normDet_le_pow_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:09.010568+00:00
-- url     : https://prove2.me/submissions/73696048-3f57-4b0c-9c88-9410c3242d84

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_GramDetLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.F
namespace Formalism.F
theorem _root_.solution {R F : Type*} [NormedAddCommGroup R] [InnerProductSpace ℝ R]
    [FiniteDimensional ℝ R] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : R →ₗ[ℝ] F) (K : ℝ) (hK : 0 ≤ K) (hg : ∀ y, ‖g y‖ ≤ K * ‖y‖) :
    g.normDet ≤ K ^ finrank ℝ R := by
  unfold LinearMap.normDet
  split_ifs with h
  swap
  · positivity
  letI : MeasurableSpace R := borel R
  haveI : BorelSpace R := ⟨rfl⟩

  let φ : LinearMap.range g ≃ₗᵢ[ℝ] R := h.some.repr.trans (stdOrthonormalBasis ℝ R).repr.symm
  let T : R →ₗ[ℝ] R := φ.toLinearEquiv.toLinearMap ∘ₗ g.rangeRestrict
  have hmat : LinearMap.toMatrix (stdOrthonormalBasis ℝ R).toBasis h.some.toBasis g.rangeRestrict =
      LinearMap.toMatrix (stdOrthonormalBasis ℝ R).toBasis (stdOrthonormalBasis ℝ R).toBasis T := by
    ext i j
    simp [LinearMap.toMatrix_apply, T, φ]
  rw [hmat, LinearMap.det_toMatrix, Real.norm_eq_abs]
  have hT : ∀ y, ‖T y‖ = ‖g y‖ := by
    intro y
    simp [T]
  have hsub : T '' Metric.ball 0 1 ⊆ Metric.closedBall 0 K := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_ball_zero_iff] at hy
    rw [mem_closedBall_zero_iff, hT]
    calc ‖g y‖ ≤ K * ‖y‖ := hg y
      _ ≤ K * 1 := by gcongr
      _ = K := mul_one K
  have hm := MeasureTheory.measure_mono (μ := (MeasureTheory.volume : MeasureTheory.Measure R)) hsub
  rw [MeasureTheory.Measure.addHaar_image_linearMap, MeasureTheory.Measure.addHaar_closedBall _ _ hK] at hm
  have hpos : 0 < MeasureTheory.volume (Metric.ball (0 : R) 1) := Metric.measure_ball_pos _ _ one_pos
  have hfin : MeasureTheory.volume (Metric.ball (0 : R) 1) ≠ ⊤ := MeasureTheory.measure_ball_lt_top.ne
  have h2 := (ENNReal.mul_le_mul_iff_left hpos.ne' hfin).1 hm
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
end Formalism.F
