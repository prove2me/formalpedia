-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.fatouStep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:52.197627+00:00
-- url     : https://prove2.me/submissions/e9d55566-aaa1-435f-b9d5-aec2e05e383d

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_meas_sq
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LEx2_sq_nonneg__b7974ad0744f
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LEx2_ld_zero__1805213b0513

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : FatouStep := by
  intro hRange hLim B A _ wt v σ K hσ hpos hmw hmv hInt hBd
  have hsqm : Measurable (LE.sq B wt v) := meas_sq B wt v hmw hmv
  have hsq0 : ∀ ω, 0 ≤ LE.sq B wt v ω := sq_nonneg' B wt hpos v
  set e : ℕ → ℝ := fun n => 1 / ((n:ℝ) + 1) with he
  have he0 : ∀ n, 0 < e n := fun n => by simp only [he]; positivity
  have hte : Tendsto e atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall he0⟩
  have hmth : ∀ ε : ℝ, Measurable fun ω => th ε σ (B.G ω) := fun ε => by
    unfold th; exact (B.G_meas.div (B.G_meas.add_const ε)).pow_const σ
  have hlim : ∀ ω, Tendsto (fun n => th (e n) σ (B.G ω) * LE.sq B wt v ω) atTop (𝓝 (LE.sq B wt v ω)) := by
    intro ω
    have h := (hLim σ 0 (B.G ω) (B.G_pos ω)).comp hte
    simp only [Function.comp_def, ld_zero' _ _ (B.G_pos ω), if_true] at h
    simpa using h.mul_const (LE.sq B wt v ω)
  have hK0 : 0 ≤ K := by
    refine le_trans (integral_nonneg fun ω => ?_) (hBd 1 one_pos)
    exact mul_nonneg (hRange 1 σ _ one_pos hσ (B.G_pos ω)).1.le (hsq0 ω)
  have hle : ∫⁻ ω, ENNReal.ofReal (LE.sq B wt v ω) ∂B.μ ≤ ENNReal.ofReal K := by
    calc ∫⁻ ω, ENNReal.ofReal (LE.sq B wt v ω) ∂B.μ
        = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (th (e n) σ (B.G ω) * LE.sq B wt v ω)) atTop ∂B.μ := by
          refine lintegral_congr fun ω => ?_
          exact ((ENNReal.tendsto_ofReal (hlim ω)).liminf_eq).symm
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (th (e n) σ (B.G ω) * LE.sq B wt v ω) ∂B.μ) atTop :=
          lintegral_liminf_le fun n => ((hmth (e n)).mul hsqm).ennreal_ofReal
      _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal K) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
          rw [← ofReal_integral_eq_lintegral_ofReal (hInt (e n) (he0 n))
            (Eventually.of_forall fun ω => mul_nonneg (hRange (e n) σ _ (he0 n) hσ (B.G_pos ω)).1.le (hsq0 ω))]
          exact ENNReal.ofReal_le_ofReal (hBd (e n) (he0 n))
      _ = ENNReal.ofReal K := by simp
  refine ⟨⟨hsqm.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hsq0)]
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hsq0) hsqm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hK0 hle
end Formalism.FourierDecayAlt.P.LEx2
