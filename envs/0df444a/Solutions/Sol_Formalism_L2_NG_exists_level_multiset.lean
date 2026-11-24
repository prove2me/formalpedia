-- Prove2me | solution 1 for Formalism.L2.NG.exists_level_multiset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:52:09.021801+00:00
-- url     : https://prove2.me/submissions/d797439f-afc9-4879-bfee-43bfa41c4e00

import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsLab
import Theorems.Thm_Formalism_L2_NG_exists_level_elt
import Theorems.Thm_Formalism_L2_NG_pow_level_mul
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.L2 Formalism.L2.NG
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {p : ℕ} [Fact p.Prime]
namespace Formalism.L2.NG
theorem _root_.solution (s : Multiset (Formalism.CyclotomicNorms.Fbar p)) (hs : (0 : Formalism.CyclotomicNorms.Fbar p) ∉ s) :
    ∃ d, 0 < d ∧ ∀ x ∈ s, x ^ (p ^ d - 1) = 1 := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | cons a s ih =>
    obtain ⟨d, hd, h⟩ := ih (fun h => hs (Multiset.mem_cons_of_mem h))
    obtain ⟨e, he, h'⟩ := exists_level_elt a (fun h => hs (h ▸ Multiset.mem_cons_self a s))
    refine ⟨d * e, Nat.mul_pos hd he, fun x hx => ?_⟩
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · rw [mul_comm]; exact pow_level_mul h' d
    · exact pow_level_mul (h x hx) e
end Formalism.L2.NG
