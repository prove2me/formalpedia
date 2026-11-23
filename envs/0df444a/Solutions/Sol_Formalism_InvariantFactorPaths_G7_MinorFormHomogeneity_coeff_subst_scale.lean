-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.MinorFormHomogeneity.coeff_subst_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:03.206419+00:00
-- url     : https://prove2.me/submissions/411effe1-67ea-492f-ba23-b84dc47624e2

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_EntryDegree
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EJoint

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)
open Formalism.InvariantFactorPaths.G7.MinorFormHomogeneity
namespace Formalism.InvariantFactorPaths.G7.MinorFormHomogeneity
theorem _root_.solution {K ι : Type} [Field K] (ϖ : K) (Th : MvPowerSeries ι K) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (MvPowerSeries.subst
      (fun i => MvPowerSeries.C ϖ * (MvPowerSeries.X i : MvPowerSeries ι K)) Th) =
      ϖ ^ n.degree * MvPowerSeries.coeff n Th := by
  have h : (fun i => MvPowerSeries.C ϖ * (MvPowerSeries.X i : MvPowerSeries ι K)) =
      (fun _ : ι => ϖ) • (MvPowerSeries.X : ι → MvPowerSeries ι K) := by
    funext i
    simp [MvPowerSeries.smul_eq_C_mul]
  rw [h, ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale, Finsupp.prod,
    Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
end Formalism.InvariantFactorPaths.G7.MinorFormHomogeneity
