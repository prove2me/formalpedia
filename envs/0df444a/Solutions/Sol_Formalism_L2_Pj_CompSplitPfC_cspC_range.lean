-- Prove2me | solution 1 for Formalism.L2.Pj.CompSplitPfC.cspC_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:14:50.18283+00:00
-- url     : https://prove2.me/submissions/bec9f07a-bc9d-4da3-82ab-8374690eb875

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
theorem _root_.solution (y : S ⊗[P] integralClosure P (FractionRing P)) :
    ∃ s : S, algebraMap S (S ⊗[P] FractionRing P) s =
      Algebra.TensorProduct.map (AlgHom.id P S) (integralClosure P (FractionRing P)).val y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s z =>
    obtain ⟨p, hp⟩ := (IsIntegrallyClosed.isIntegral_iff (R := P) (K := FractionRing P)).mp z.2
    refine ⟨p • s, ?_⟩
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val, cspC_alg, ← hp,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add a b ha hb =>
    obtain ⟨s, hs⟩ := ha
    obtain ⟨s', hs'⟩ := hb
    exact ⟨s + s', by rw [map_add, map_add, hs, hs']⟩
end Formalism.L2.Pj.CompSplitPfC
