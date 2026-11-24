-- Prove2me | solution 1 for Formalism.L2.NT.offs_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:21:11.559841+00:00
-- url     : https://prove2.me/submissions/b51efc6d-5925-42cf-bbc4-bc2e7bb4ea74

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
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
open NumberField IsDedekindDomain Polynomial
open Formalism Formalism.L2 Formalism.L2.NT
open Formalism.L2.Host
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
namespace Formalism.L2.NT
theorem _root_.solution {m : ℕ} (c : Fin m → ℕ) {i j : Fin m} (h : j < i) : offs c j + c j ≤ offs c i := by
  unfold offs
  have e : c j = ∑ k : Fin m, if k = j then c k else 0 := by rw [Finset.sum_ite_eq']; simp
  rw [e, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  by_cases h1 : k < j
  · have h2 : k < i := lt_trans h1 h
    have h3 : k ≠ j := ne_of_lt h1
    simp [h1, h2, h3]
  · by_cases h3 : k = j
    · subst h3
      simp [h]
    · simp [h1, h3]
end Formalism.L2.NT
