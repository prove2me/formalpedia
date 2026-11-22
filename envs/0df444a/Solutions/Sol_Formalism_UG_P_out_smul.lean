-- Prove2me | solution 1 for Formalism.UG.P.out_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:27:42.335821+00:00
-- url     : https://prove2.me/submissions/5ecce4f1-1b4a-426e-8321-d5b2c7769810

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G]
namespace Formalism.UG.P
theorem _root_.solution (K : Subgroup G) (c : G) (x : G ⧸ K) :
    ∃ κ : K, (c • x).out = c * x.out * (κ : G) := by
  have h : ((c * x.out : G) : G ⧸ K) = ((c • x).out : G ⧸ K) := by
    rw [QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' x]
    rw [MulAction.Quotient.smul_mk]
    rfl
  refine ⟨⟨_, QuotientGroup.eq.1 h⟩, ?_⟩
  simp only [mul_inv_cancel_left]
end Formalism.UG.P
