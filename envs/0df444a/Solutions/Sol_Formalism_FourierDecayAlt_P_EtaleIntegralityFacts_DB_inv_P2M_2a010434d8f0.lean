-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.DB_inv_P2M_2a010434d8f0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:11.819709+00:00
-- url     : https://prove2.me/submissions/a2b94b58-9f99-493e-a7c9-b3c5d3d2c8ab

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EtaleIntegralityFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
open Filter Topology
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
theorem _root_.solution (q : ℕ) (c : ℂ) (hc : c ≠ 0) :
    DB q (fun z : ℂ => z⁻¹) c (q.factorial * ‖c‖⁻¹) ‖c‖⁻¹ := by
  refine ⟨contDiffAt_inv ℝ hc, fun j hj => ?_⟩
  have h : ContDiffAt ℂ j (Inv.inv : ℂ → ℂ) c := contDiffAt_inv ℂ hc
  have e := h.restrictScalars_iteratedFDeriv (𝕜 := ℝ)
  have e' : iteratedFDeriv ℝ j (fun z : ℂ => z⁻¹) c = iteratedFDeriv ℝ j (Inv.inv : ℂ → ℂ) c := rfl
  rw [e', ← e, Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_inv]
  have hfac : (j.factorial : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_le hj
  have hn : ‖c ^ (-1 - (j : ℤ))‖ = ‖c‖⁻¹ * ‖c‖⁻¹ ^ j := by
    rw [norm_zpow, sub_eq_add_neg, zpow_add₀ (norm_ne_zero_iff.mpr hc), zpow_neg_one, zpow_neg, zpow_natCast,
      inv_pow]
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, hn, Complex.norm_natCast, mul_assoc]
  gcongr
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
