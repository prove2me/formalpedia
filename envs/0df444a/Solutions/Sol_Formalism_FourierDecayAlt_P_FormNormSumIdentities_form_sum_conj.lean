-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FormNormSumIdentities.form_sum_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:59:36.437649+00:00
-- url     : https://prove2.me/submissions/ac4ca70c-0db6-49e0-99f9-4733889de7f9

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormSumLeOfForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FormNormSumIdentities
open Finset
open scoped ComplexConjugate InnerProductSpace
noncomputable section
variable {ι κ : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities
theorem _root_.solution (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (J : Finset κ) (a : κ → ℂ) (y : κ → V) :
    B (∑ j ∈ J, conj (a j) • y j) (∑ l ∈ J, conj (a l) • y l) =
      ∑ j ∈ J, ∑ l ∈ J, conj (a j) * a l * B (y j) (y l) := by
  rw [LinearMap.map_sum₂]
  refine sum_congr rfl fun j _ => ?_
  rw [map_smul, LinearMap.smul_apply, map_sum, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [map_smulₛₗ, smul_eq_mul, Complex.conj_conj]
  ring
end Formalism.FourierDecayAlt.P.FormNormSumIdentities
