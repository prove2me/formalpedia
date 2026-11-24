-- Prove2me | solution 1 for Formalism.L2.Pj.GenericSectionMinimum.IsDer.pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:49:29.764881+00:00
-- url     : https://prove2.me/submissions/3a2d7277-9a0d-4e9b-89ad-bc02832537aa

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem
import Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_IsDer_pow_map_mem_of_pow_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenericSectionMinimum
open Formalism.L2.Pj.GenericSectionMinimum.IsDer
variable {A : Type*} [CommRing A] {δ : A → A}
namespace Formalism.L2.Pj.GenericSectionMinimum.IsDer
theorem _root_.solution (h : IsDer δ) (I : Ideal A) (hI : ∀ x ∈ I, δ x ∈ I) (hu : ∀ n : ℕ, 0 < n → IsUnit (n : A))
    {y : A} {n : ℕ} (hy : y ^ n ∈ I) : δ y ^ (2 * n) ∈ I := by
  have e := h.pow_map_mem_of_pow_mul_mem I hI hu y n 0 (by simpa using hy)
  simpa using e
end Formalism.L2.Pj.GenericSectionMinimum.IsDer
