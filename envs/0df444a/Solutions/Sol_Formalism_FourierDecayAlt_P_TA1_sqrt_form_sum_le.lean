-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TA1.sqrt_form_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:22.223348+00:00
-- url     : https://prove2.me/submissions/8b8ea925-869d-47c1-9a72-a5a05ddef6fc

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagonalTopBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TA1
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {α : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Formalism.FourierDecayAlt.P.TA1
theorem _root_.solution (P : Finset α) (k : α → α → ℂ) (hk : PSDOn P k) {ι : Type} (T : Finset ι)
    (U : ι → α → H) :
    √(form P k (∑ s ∈ T, U s) (∑ s ∈ T, U s)).re ≤ ∑ s ∈ T, √(form P k (U s) (U s)).re := by
  let c : PreInnerProductSpace.Core ℂ (α → H) := core P k hk
  let _ : SeminormedAddCommGroup (α → H) :=
    @InnerProductSpace.Core.toSeminormedAddCommGroup ℂ (α → H) _ _ _ c
  exact norm_sum_le T U
end Formalism.FourierDecayAlt.P.TA1
