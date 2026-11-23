-- Prove2me | solution 1 for Formalism.UG.P.csEasy_formJ_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:17.508805+00:00
-- url     : https://prove2.me/submissions/6d244c2d-e870-4a17-a72b-c67b46f3c683

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsEasy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ e, σ (σ e) = e)
    {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n E) (c : E) (x y : n → E) :
    Formalism.UG.CS.formJ σ hσ J c x y = c * Formalism.UG.hform σ J x y := by
  unfold Formalism.UG.CS.formJ Formalism.UG.hform
  rw [Matrix.toLinearMapₛₗ₂'_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show σ (x i) * (y j * (c * J i j)) = c * (σ (x i) * J i j * y j)
  ring
end Formalism.UG.P
