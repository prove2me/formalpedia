-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.KK_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:19:36.845825+00:00
-- url     : https://prove2.me/submissions/9b34c82e-ae0a-45a3-8e4f-818639de4651

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_mem_zpowers_JJ
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_psi_JJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Subgroup
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open ModelEmbedding
open ModelEmbedding
open Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
namespace Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
theorem _root_.solution (k : ℕ) : KK (k + 3) ≤ (psi k).ker := by
  intro g hg
  rw [KK, Subgroup.mem_comap, MonoidHom.mem_range] at hg
  obtain ⟨q, hq⟩ := hg
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (zpowers (JJ (k + 3))) q
  have hq' : ((h ^ 2 : GalL (k + 3)) : GalL (k + 3) ⧸ zpowers (JJ (k + 3))) = g := by
    rw [QuotientGroup.mk_pow]; simpa using hq
  have hm := QuotientGroup.eq.1 hq'
  have hsq : ∀ x : ℤˣ × ℤˣ × ℤˣ, x ^ 2 = 1 := fun x =>
    Prod.ext (by simp [Int.units_sq]) (Prod.ext (by simp [Int.units_sq]) (by simp [Int.units_sq]))
  rw [MonoidHom.mem_ker]
  rcases mem_zpowers_JJ hm with h1 | h1
  · rw [← inv_mul_eq_one.1 h1, map_pow, hsq]
  · rw [inv_mul_eq_iff_eq_mul.1 h1, map_mul, map_pow, hsq, psi_JJ, one_mul]
end Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
