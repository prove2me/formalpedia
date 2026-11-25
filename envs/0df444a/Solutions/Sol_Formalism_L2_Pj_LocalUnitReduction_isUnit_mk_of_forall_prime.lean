-- Prove2me | solution 1 for Formalism.L2.Pj.LocalUnitReduction.isUnit_mk_of_forall_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:10:25.737704+00:00
-- url     : https://prove2.me/submissions/be430dec-2dcf-4596-9240-9a24c9b7c61d

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalUnitReduction_FinRedStatement
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalUnitReduction_IsUnitMkOfForallPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LocalUnitReduction
variable {K' Fr : Type*} [Field K'] [CommRing Fr] [Algebra K' Fr] (J : Ideal Fr)
  {ι : Type*} {R : ι → Type*} [∀ c, CommRing (R c)] [∀ c, Algebra K' (R c)]
  (φ : ∀ c, Fr →ₐ[K'] R c)
namespace Formalism.L2.Pj.LocalUnitReduction
theorem _root_.solution {I : Ideal Fr} {p : Fr}
    (hp : ∀ Q : Ideal Fr, Q.IsPrime → I ≤ Q → p ∉ Q) : IsUnit (Ideal.Quotient.mk I p) := by
  by_contra h
  have hne : Ideal.span {Ideal.Quotient.mk I p} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  haveI := hM.isPrime
  refine hp (M.comap (Ideal.Quotient.mk I)) inferInstance (fun x hx => ?_) ?_
  · rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact M.zero_mem
  · exact hle (Ideal.mem_span_singleton_self _)
end Formalism.L2.Pj.LocalUnitReduction
