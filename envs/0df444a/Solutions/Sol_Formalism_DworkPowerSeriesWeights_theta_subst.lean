-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.theta_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:14:38.269308+00:00
-- url     : https://prove2.me/submissions/e4647f8e-baeb-4d84-9805-f91ad0c665f4

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_constantCoeff_linSub
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_constantCoeff_bSum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_subst_linSub
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_subst_mvExp
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs


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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {K : Type} [NormedField K] [CharZero K] {d N0 N1 : ℕ} [NeZero d]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (M Mg A : ZV d N0 N1 → ZV d N0 N1 → K)
    (h : ∀ z i, Mg z i = ∑ y, M z y * A i y) (G : MvPowerSeries (ZV d N0 N1) K) (ε : K)
    (be : MvPowerSeries (ZMod d) K) (hbe : MvPowerSeries.constantCoeff be = 0) :
    MvPowerSeries.subst (linSub Mg) G * mvExp (ε • bSum Mg be) =
      MvPowerSeries.subst
        (fun j : ZV d N0 N1 => (∑ i : ZV d N0 N1, MvPowerSeries.C (A i j) * MvPowerSeries.X i :
          MvPowerSeries (ZV d N0 N1) K))
        (MvPowerSeries.subst (linSub M) G * mvExp (ε • bSum M be)) := by
  set aa : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K := fun j =>
    ∑ i : ZV d N0 N1, MvPowerSeries.C (A i j) * MvPowerSeries.X i with haa
  have hs : MvPowerSeries.HasSubst aa :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => by simp [haa]
  have hlin : ∀ z, MvPowerSeries.subst aa (linSub M z) = linSub Mg z := subst_linSub _ _ _ h
  have hbS : MvPowerSeries.subst aa (bSum M be) = bSum Mg be := by
    unfold bSum
    rw [← MvPowerSeries.coe_substAlgHom hs, map_sum]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [MvPowerSeries.coe_substAlgHom hs, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => constantCoeff_linSub M _) hs]
    simp only [hlin]
  rw [MvPowerSeries.subst_mul hs, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_linSub M)) hs,
    subst_mvExp hs _ (by
      rw [MvPowerSeries.smul_eq_C_mul, map_mul, constantCoeff_bSum _ _ hbe, mul_zero]),
    MvPowerSeries.subst_smul hs, hbS]
  simp only [hlin]
end Formalism.DworkPowerSeriesWeights
