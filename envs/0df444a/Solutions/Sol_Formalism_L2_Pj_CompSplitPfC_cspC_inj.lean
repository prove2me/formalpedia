-- Prove2me | solution 1 for Formalism.L2.Pj.CompSplitPfC.cspC_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:14:48.6964+00:00
-- url     : https://prove2.me/submissions/fce209c3-6097-481a-8370-881ab693caff

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfC
import Theorems.Thm_Formalism_L2_Pj_CompSplitPfC_cspC_alg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.CompSplitPfC
open TensorProduct
variable {P S : Type} [CommRing P] [IsDomain P] [IsIntegrallyClosed P] [CommRing S] [Algebra P S]
  [Algebra.Etale P S]
namespace Formalism.L2.Pj.CompSplitPfC
theorem _root_.solution : Function.Injective (algebraMap S (S ⊗[P] FractionRing P)) := by
  have hf : Function.Injective (Algebra.linearMap P (FractionRing P)) :=
    IsFractionRing.injective P (FractionRing P)
  have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := S)
    (Algebra.linearMap P (FractionRing P)) hf
  have key : ∀ s : S, algebraMap S (S ⊗[P] FractionRing P) s =
      (LinearMap.lTensor S (Algebra.linearMap P (FractionRing P))) ((TensorProduct.rid P S).symm s) := by
    intro s
    rw [cspC_alg, TensorProduct.rid_symm_apply, LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one]
  intro a b h
  rw [key, key] at h
  exact (TensorProduct.rid P S).symm.injective (h2 h)
end Formalism.L2.Pj.CompSplitPfC
