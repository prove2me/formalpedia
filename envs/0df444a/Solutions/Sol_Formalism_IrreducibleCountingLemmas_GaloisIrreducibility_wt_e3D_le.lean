-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.wt_e3D_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:52:55.087897+00:00
-- url     : https://prove2.me/submissions/733300e0-0c44-42fa-9b84-1e10832ca256

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_SquareSetMemExceptionalUnion
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_divisor_square_weight_sum_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_monic
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_natDegree
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_sqWeight_nonneg
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_square_mass_le_one
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
import Theorems.Thm_P2M_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wtOf_eq_filter__b757eed49bc8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (N : ℕ) (h : K[X]) (hm : h.Monic) :
    wtOf (e3μ K N) (e3D K N h) ≤ sqWeight h := by
  classical
  unfold e3D
  rw [wtOf_eq_filter']
  by_cases hd : h.natDegree ≤ N
  · exact divisor_square_weight_sum_le square_mass_le_one K N h hm hd _ (fun c hc => by
      simpa only [Finset.mem_filter] using hc)
  · rw [Finset.filter_eq_empty_iff.mpr, Finset.sum_empty]
    · exact sqWeight_nonneg h
    · intro c _ hdiv
      apply hd
      have := natDegree_le_of_dvd hdiv (monicOf_monic c).ne_zero
      rwa [monicOf_natDegree] at this
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
