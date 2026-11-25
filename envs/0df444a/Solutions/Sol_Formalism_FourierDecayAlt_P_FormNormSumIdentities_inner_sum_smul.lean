-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FormNormSumIdentities.inner_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:59:39.62643+00:00
-- url     : https://prove2.me/submissions/e136207a-35d5-46be-911e-008f7b99977c

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
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities
theorem _root_.solution (k : ι → ι → ℂ) (v : ι → H) (hv : ∀ p q, k p q = ⟪v p, v q⟫_ℂ) (J : Finset κ)
    (a : κ → ℂ) (P : κ → ι) :
    ⟪∑ j ∈ J, a j • v (P j), ∑ l ∈ J, a l • v (P l)⟫_ℂ =
      ∑ j ∈ J, ∑ l ∈ J, conj (a j) * a l * k (P j) (P l) := by
  rw [sum_inner]
  refine sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_sum, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [inner_smul_right, hv]
  ring
end Formalism.FourierDecayAlt.P.FormNormSumIdentities
