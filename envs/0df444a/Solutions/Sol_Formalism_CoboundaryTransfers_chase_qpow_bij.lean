-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.chase_qpow_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:15.384801+00:00
-- url     : https://prove2.me/submissions/9460bae0-5ba3-484d-a3cd-76d4c5d84d1f

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_DiffOneSmulOfTower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  {D' : Type} [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']
namespace Formalism.CoboundaryTransfers
theorem _root_.solution (W : WachMod B M D) (j : ℕ) :
    Function.Bijective (fun x : D => B.Q ^ j • x) := by
  induction j with
  | zero =>
    simp only [pow_zero, one_smul]
    exact Function.bijective_id
  | succ n ih =>
    have h : (fun x : D => B.Q ^ (n + 1) • x) = (fun x : D => B.Q ^ n • x) ∘ (fun x : D => B.Q • x) := by
      funext x
      simp only [Function.comp, pow_succ, mul_smul]
    rw [h]
    exact ih.comp W.Q_bij
end Formalism.CoboundaryTransfers
