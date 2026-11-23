-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B.step1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:13.233471+00:00
-- url     : https://prove2.me/submissions/66183501-a093-47cd-affa-a29486c37816

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
section
open Finset
open Formalism.FourierDecayAlt
end
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
section
open Finset
open Classical
variable {Cl Nu : Type}
private theorem sum_le_mul_sum_of_fiber_weight_bound {X Dt : Type} [Fintype Dt] [DecidableEq Dt] (S : Finset X)
    (dat : X → Option Dt) (f w : X → ℝ) (F W : Dt → ℝ) (V : ℝ) (hF : ∀ d, 0 ≤ F d)
    (hnone : ∀ x, dat x = none → f x = 0) (hsome : ∀ x d, dat x = some d → f x = w x * F d)
    (hU : ∀ d (T : Finset X), (∀ x ∈ T, dat x = some d) → ∑ x ∈ T, w x ≤ V * W d) :
    ∑ x ∈ S, f x ≤ V * ∑ d, W d * F d := by
  rw [← Finset.sum_fiberwise S dat f, Fintype.sum_option, Finset.mul_sum]
  have h0 : ∑ x ∈ S with dat x = none, f x = 0 :=
    Finset.sum_eq_zero (fun x hx => hnone x (Finset.mem_filter.1 hx).2)
  rw [h0, zero_add]
  refine Finset.sum_le_sum (fun d _ => ?_)
  have h1 : ∑ x ∈ S with dat x = some d, f x = (∑ x ∈ S with dat x = some d, w x) * F d := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun x hx => hsome x d (Finset.mem_filter.1 hx).2)
  rw [h1, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hU d _ (fun x hx => (Finset.mem_filter.1 hx).2)) (hF d)
end
section
open Finset
open Classical
end
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
section
open Finset
end
section
open Finset
section
variable {ι V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
end
end
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
section
open Finset
open Classical
end
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D1
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
section
open Finset
open Classical
end
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D2
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
section
open Finset
open Classical
end
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
section
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open scoped ComplexOrder ComplexConjugate
open Classical
end
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.F
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
section
open Finset NumberField
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
end
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.F
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Classical
variable {Cl Nu : Type}
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
theorem _root_.solution (L : LocalNG Cl Nu) (hU : L.Unfold) (S : Finset (Cl × Nu)) :
    ∑ x ∈ S, L.a2 x.1 x.2 ≤ L.V0 * ∑ d, (∏ p, L.wt p (d p)) * ‖L.ampNG d‖ ^ 2 := by
  unfold LocalNG.Unfold at hU
  refine sum_le_mul_sum_of_fiber_weight_bound S (fun x => L.dat x.1 x.2) (fun x => L.a2 x.1 x.2) (fun x => L.rw x.1)
    (fun d => ‖L.ampNG d‖ ^ 2) (fun d => ∏ p, L.wt p (d p)) L.V0 (fun d => sq_nonneg _) ?_ ?_
    (fun d T hT => hU d T hT)
  · intro x h
    unfold LocalNG.a2
    simp only [h]
  · intro x d h
    unfold LocalNG.a2
    simp only [h]
    try rfl
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
