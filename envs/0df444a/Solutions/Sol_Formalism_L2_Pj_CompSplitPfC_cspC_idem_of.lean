-- Prove2me | solution 1 for Formalism.L2.Pj.CompSplitPfC.cspC_idem_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:22:07.388542+00:00
-- url     : https://prove2.me/submissions/2cf00b8b-14ca-432b-8e36-82262e0ff53c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfC
import Theorems.Thm_Formalism_L2_Pj_CompSplitPfC_cspC_range

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
theorem _root_.solution {r : S ⊗[P] FractionRing P} (hr : IsIdempotentElem r) :
    ∃ s : S, algebraMap S (S ⊗[P] FractionRing P) s = r := by
  have hint : IsIntegral S r := by
    refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C 1), Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
    simp [mul_sub, hr.eq]
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := P) (S := S)
    (B := FractionRing P)).2 ⟨r, hint⟩
  obtain ⟨s, hs⟩ := cspC_range y
  refine ⟨s, hs.trans ?_⟩
  exact congrArg Subtype.val hy
end Formalism.L2.Pj.CompSplitPfC
