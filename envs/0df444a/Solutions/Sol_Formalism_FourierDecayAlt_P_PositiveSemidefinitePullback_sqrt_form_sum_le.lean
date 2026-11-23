-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback.sqrt_form_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:11.036743+00:00
-- url     : https://prove2.me/submissions/5c183be3-b67e-48c0-adb8-17033d91ca5b

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveSemidefinitePullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
open Finset Matrix Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
theorem _root_.solution {n ι : Type} [Fintype n] (M : Matrix n n ℂ) (hM : M.PosSemidef)
    (I : Finset ι) (x : ι → n → ℂ) :
    √(((M *ᵥ (∑ s ∈ I, x s)) ⬝ᵥ star (∑ s ∈ I, x s)).re) ≤
      ∑ s ∈ I, √(((M *ᵥ x s) ⬝ᵥ star (x s)).re) :=
  @norm_sum_le _ _ (M.toSeminormedAddCommGroup hM) I x
end Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
