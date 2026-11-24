-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.BN.lin_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:11:45.008346+00:00
-- url     : https://prove2.me/submissions/3444b4c6-5c55-4c99-a1d0-b66c45e4592a

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_Kills_mul_left
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_exists_kills
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_exists_lsmul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z Formalism.IrreducibleCountingLemmas.Z.BN
namespace Formalism.IrreducibleCountingLemmas.Z.BN
theorem _root_.solution {K A : Type} [Field K] [IsAlgClosed K] [Ring A] [Algebra K A]
    (t : Finset (A → K[X])) (ht : ↑t ⊆ simpleCps K A) (c : (A → K[X]) → K)
    (h : ∀ a : A, ∑ F ∈ t, c F * (F a).nextCoeff = 0) : ∀ F ∈ t, c F = 0 := by
  classical
  intro F0 hF0
  obtain ⟨S0, i1, i2, i3, i4, i5, i6, hF⟩ := ht (Finset.mem_coe.mpr hF0)
  obtain ⟨a, ha, s, hs⟩ := exists_kills S0 (t.erase F0)
    (fun G hG => ht (Finset.mem_coe.mpr (Finset.mem_of_mem_erase (Finset.mem_coe.mp hG))))
    (by rw [← hF]; simp)
  obtain ⟨l, hl⟩ : ∃ l : Module.Dual K S0, l (a • s) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hs ((Module.forall_dual_apply_eq_zero_iff K _).mp hcon)
  obtain ⟨u, hu⟩ := exists_lsmul_eq (A := A) S0 (l.smulRight s)
  have hlin : Algebra.lsmul K K S0 (u * a) = (l ∘ₗ Algebra.lsmul K K S0 a).smulRight s := by
    ext v
    simp [hu]
  have h1 : (F0 (u * a)).nextCoeff = - l (a • s) := by
    rw [hF, nextCoeff_cp, hlin, LinearMap.trace_smulRight]
    simp
  have h2 := h (u * a)
  rw [← Finset.add_sum_erase t _ hF0, Finset.sum_eq_zero (fun G hG => by
    rw [(ha.mul_left u).nextCoeff hG, mul_zero]), add_zero, h1] at h2
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exact absurd (neg_eq_zero.mp h3) hl
end Formalism.IrreducibleCountingLemmas.Z.BN
