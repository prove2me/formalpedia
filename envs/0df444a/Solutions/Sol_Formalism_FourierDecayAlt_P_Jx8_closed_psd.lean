-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.closed_psd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:20.574183+00:00
-- url     : https://prove2.me/submissions/6fa24b30-54bb-4de7-9939-f2a744e1a64f

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psdOn_iff_isPSD
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_closed_and

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
variable {α : Type}
namespace Formalism.FourierDecayAlt.P.Jx8
theorem _root_.solution {X : Type} [TopologicalSpace X] (F : Finset α) (g : X → α → α → ℂ)
    (hg : ∀ x y, Continuous fun T => g T x y) : IsClosed {T | TB.PSDOn F (g T)} := by
  simp only [psdOn_iff_isPSD, A5.IsPSD, Set.ofPred_forall]
  refine isClosed_iInter fun a => ?_
  have hc : Continuous fun T => ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * g T x y :=
    continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun y _ => continuous_const.mul (hg x y)
  exact closed_and (isClosed_eq (Complex.continuous_im.comp hc) continuous_const)
    (isClosed_le continuous_const (Complex.continuous_re.comp hc))
end Formalism.FourierDecayAlt.P.Jx8
