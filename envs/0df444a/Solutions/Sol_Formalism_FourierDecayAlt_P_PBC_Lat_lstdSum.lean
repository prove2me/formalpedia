-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBC.Lat.lstdSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:29:30.606655+00:00
-- url     : https://prove2.me/submissions/896904f7-3a17-4cb5-814d-ddf909678329

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCStmt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeSummability
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalConditionsAndQuotientSplitting
import Definitions.Def_Lemmata_GeneralBFactRightSide_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_mL_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_mfac_shift0
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_dual_sep
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_vol_ball_V
import Theorems.Thm_Formalism_FourierDecayAlt_P_LatticeSummability_mfac_anti
import Theorems.Thm_Formalism_FourierDecayAlt_P_LatticeSummability_mfac_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_MajorantIntegrals_majIntegralProd_ok


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBC
open Formalism.FourierDecayAlt Finset Filter Topology NumberField MeasureTheory
open scoped Pointwise
noncomputable section
open Classical
open Formalism.FourierDecayAlt.P.PBC.Lat
namespace Formalism.FourierDecayAlt.P.PBC.Lat
theorem _root_.solution : PBC.LstdSum := by
  refine ⟨54, by norm_num, ?_⟩
  intro f R g L hR hg hL
  set K := C.Kst with hKdef
  have hK : 2 < K := by simp [hKdef, C.Kst]
  set large₂ : Fin f → ℝ := fun v => L v / g with hLg
  have hLg0 : ∀ v, 0 ≤ large₂ v := fun v => div_nonneg (hL v) hg.le
  set δ : ℝ := 1 / (4 * R) with hδdef
  have hδ : 0 < δ := by positivity
  set L' : Fin f → ℝ := fun v => large₂ v + δ with hL'
  have hL'pos : ∀ v, 0 < L' v := fun v => by simp only [hL']; linarith [hLg0 v]
  have hmaj := Formalism.FourierDecayAlt.P.MajorantIntegrals.majIntegralProd_ok f K L' hK hL'pos
  have hint := hmaj.1
  have hnn : ∀ y : crystallineComparison.V f, 0 ≤ crystallineComparison.mL K L' y := fun y =>
    Finset.prod_nonneg (fun v _ => Formalism.FourierDecayAlt.P.LatticeSummability.mfac_nonneg K (hL'pos v).le _ (norm_nonneg _))
  have hnn0 : ∀ y : crystallineComparison.V f, 0 ≤ crystallineComparison.mL K large₂ y := fun y =>
    Finset.prod_nonneg (fun v _ => Formalism.FourierDecayAlt.P.LatticeSummability.mfac_nonneg K (hLg0 v) _ (norm_nonneg _))
  set vb := (volume : Measure (crystallineComparison.V f)).real (Metric.ball 0 δ) with hvb
  have hvb0 : 0 < vb := by rw [hvb, vol_ball_V f δ hδ]; positivity
  have hvbσ : ∀ σ : crystallineComparison.V f, (volume : Measure (crystallineComparison.V f)).real (Metric.ball σ δ) = vb := by
    intro σ; rw [hvb, Measure.real, Measure.real, Measure.addHaar_ball_center]
  have hpt : ∀ σ : crystallineComparison.V f, ∀ y ∈ Metric.ball σ δ, crystallineComparison.mL K large₂ σ ≤ crystallineComparison.mL K L' y := by
    intro σ y hy
    apply Finset.prod_le_prod (fun v _ => Formalism.FourierDecayAlt.P.LatticeSummability.mfac_nonneg K (hLg0 v) _ (norm_nonneg _))
    intro v _
    have hyv : ‖y v‖ ≤ ‖σ v‖ + δ := by
      have h1 : ‖y v - σ v‖ ≤ ‖y - σ‖ := norm_le_pi_norm (y - σ) v
      have h2 : ‖y - σ‖ < δ := by rw [← dist_eq_norm]; exact hy
      have h3 : ‖y v‖ ≤ ‖σ v‖ + ‖y v - σ v‖ := by
        calc ‖y v‖ = ‖σ v + (y v - σ v)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith
    exact (mfac_shift0 K (hLg0 v) hδ (norm_nonneg _)).trans
      (Formalism.FourierDecayAlt.P.LatticeSummability.mfac_anti K (hL'pos v) (norm_nonneg _) hyv)
  have hloc : ∀ σ : crystallineComparison.V f, crystallineComparison.mL K large₂ σ * vb ≤ ∫ y in Metric.ball σ δ, crystallineComparison.mL K L' y := by
    intro σ
    rw [← hvbσ σ, mul_comm, ← smul_eq_mul, ← setIntegral_const]
    exact setIntegral_mono_on (integrableOn_const (measure_ball_lt_top).ne) hint.integrableOn
      measurableSet_ball (fun y hy => hpt σ y hy)
  have hsum : ∀ u : Finset (crystallineComparison.dualSet (Lstd f R)),
      ∑ σ ∈ u, crystallineComparison.mL K L (g • (σ : crystallineComparison.V f)) ≤ (∫ y, crystallineComparison.mL K L' y) / vb := by
    intro u
    simp only [mL_scale K L g hg]
    rw [le_div_iff₀ hvb0, Finset.sum_mul]
    have hdisj : Set.Pairwise (↑u : Set (crystallineComparison.dualSet (Lstd f R)))
        (Function.onFun Disjoint fun σ : crystallineComparison.dualSet (Lstd f R) => Metric.ball (σ : crystallineComparison.V f) δ) := by
      intro σ _ σ' _ hne
      apply Metric.ball_disjoint_ball
      have := dual_sep f R hR σ σ' σ.2 σ'.2 (fun h => hne (Subtype.ext h))
      rw [dist_eq_norm]
      have e : δ + δ = 1 / (2 * R) := by rw [hδdef]; field_simp; ring
      linarith
    calc ∑ σ ∈ u, crystallineComparison.mL K large₂ (σ : crystallineComparison.V f) * vb
        ≤ ∑ σ ∈ u, ∫ y in Metric.ball (σ : crystallineComparison.V f) δ, crystallineComparison.mL K L' y :=
          Finset.sum_le_sum (fun σ _ => hloc σ)
      _ = ∫ y in ⋃ σ ∈ u, Metric.ball (σ : crystallineComparison.V f) δ, crystallineComparison.mL K L' y :=
          (integral_biUnion_finset u (fun σ _ => measurableSet_ball) hdisj
            (fun σ _ => hint.integrableOn)).symm
      _ ≤ ∫ y, crystallineComparison.mL K L' y := setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)
  have hnng : ∀ σ : crystallineComparison.dualSet (Lstd f R), 0 ≤ crystallineComparison.mL K L (g • (σ : crystallineComparison.V f)) := fun σ =>
    Finset.prod_nonneg (fun v _ => Formalism.FourierDecayAlt.P.LatticeSummability.mfac_nonneg K (hL v) _ (norm_nonneg _))
  have hS : Summable (fun σ : crystallineComparison.dualSet (Lstd f R) => crystallineComparison.mL K L (g • (σ : crystallineComparison.V f))) :=
    summable_of_sum_le hnng hsum
  refine ⟨hS, (hS.tsum_le_of_sum_le hsum).trans ?_⟩

  rw [hmaj.2, hvb, vol_ball_V f δ hδ, show (Real.pi * δ ^ 2) ^ f = ∏ _v : Fin f, (Real.pi * δ ^ 2) by simp]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_le_prod
  · intro v _
    have hK2 : (0 : ℝ) < (K : ℝ) - 2 := by simp [hKdef, C.Kst]; norm_num
    have := hL'pos v
    exact div_nonneg (div_nonneg (by positivity) hK2.le) (by positivity)
  intro v _
  have hKr : (K : ℝ) = 5 := by simp [hKdef, C.Kst]
  rw [hKr]
  set x : ℝ := R * L v / g with hxdef
  have hx0 : 0 ≤ x := by have := hL v; positivity
  have hx : L' v = 4 * δ * x + δ := by
    show L v / g + δ = _
    rw [hxdef, hδdef]; field_simp
  rw [hx]
  have ht : 0 < Real.pi * δ ^ 2 := by positivity
  have e : Real.pi * (4 * δ * x + δ) ^ 2 * 5 / (5 - 2) / (Real.pi * δ ^ 2) = (4 * x + 1) ^ 2 * 5 / 3 := by
    field_simp; ring
  rw [e]
  nlinarith [sq_nonneg (x - 1)]
end Formalism.FourierDecayAlt.P.PBC.Lat
