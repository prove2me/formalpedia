-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.substitution_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:14:21.44674+00:00
-- url     : https://prove2.me/submissions/88ae4a54-2074-46dc-b189-1ac455aa343e

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WtGeProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoWtGe_iff
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_prod
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_pow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : SubstWt.{u, v, w} := by
  intro K _ _ pi h0 h1 σ τ _ a r r' wt f ha0 ha hf
  classical
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hp : ∀ d : σ →₀ ℕ, WtGe pi r' (dot d r) (d.prod fun s e => a s ^ e) := by
    intro d
    have := wtGe_prod h0 d.support (fun s => (d s : ℝ) * r s) (fun s => a s ^ d s)
      fun s _ => wtGe_pow h0 (ha s) (d s)
    simpa [dot, Finsupp.sum, Finsupp.prod] using this
  intro m
  rw [monoWtGe_iff, MvPowerSeries.coeff_subst hs]
  refine norm_finsum_le_of (Real.rpow_nonneg h0.le _) fun d => ?_
  rw [smul_eq_mul, norm_mul]
  calc ‖MvPowerSeries.coeff d f‖ * ‖MvPowerSeries.coeff m (d.prod fun s e => a s ^ e)‖
      ≤ pi ^ (wt - dot d r) * pi ^ (dot d r - dot m r') :=
        mul_le_mul (hf d) (hp d m) (norm_nonneg _) (Real.rpow_nonneg h0.le _)
    _ = pi ^ (wt - dot m r') := by rw [← Real.rpow_add h0]; congr 1; ring
end Formalism.DworkPowerSeriesWeights
