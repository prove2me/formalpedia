-- Prove2me | solution 1 for Formalism.MainNotions.UnusedSlot33.HK.norm_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:10:16.853489+00:00
-- url     : https://prove2.me/submissions/b52a9e2c-b531-44e5-9e40-707161cbacb3

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_EqOfLeOfAbsNormEq
import Theorems.Thm_Formalism_MainNotions_UnusedSlot33_HK_conj_b
import Theorems.Thm_Formalism_MainNotions_UnusedSlot33_HK_b_ne_zero
import Theorems.Thm_Formalism_MainNotions_UnusedSlot33_HK_cases_K
import Theorems.Thm_Formalism_MainNotions_UnusedSlot33_HK_bE_mem
import Theorems.Thm_Formalism_MainNotions_UnusedSlot33_HK_isGalK
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj
import Theorems.Thm_Formalism_FrobeniusOrbits_hostE_isGalois
import Theorems.Thm_Formalism_HC_HostAx_hostE_isGalois


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.UnusedSlot33 Formalism.MainNotions.UnusedSlot33.HK
open NumberField Polynomial Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.TwoAdicCyclotomicDecomposition
open scoped Pointwise
variable {R : Ranks} (H : Host R)
namespace Formalism.MainNotions.UnusedSlot33.HK
theorem _root_.solution (x : H.K) :
    algebraMap ℚ H.E (Algebra.norm ℚ x) = (x : H.E) * H.conj (x : H.E) := by
  classical
  have hG := isGalK H
  have hE := H.hostE_isGalois
  obtain ⟨cK, hcK⟩ : ∃ cK : Gal(H.K/ℚ), cK = H.conj.restrictNormal H.K := ⟨_, rfl⟩
  have hcK' : ∀ y : H.K, ((cK y : H.K) : H.E) = H.conj (y : H.E) := by
    intro y
    rw [hcK]
    exact AlgEquiv.restrictNormal_commutes H.conj H.K y
  have hne : (1 : Gal(H.K/ℚ)) ≠ cK := by
    intro h1
    have h2 := hcK' ⟨_, bE_mem H⟩
    rw [← h1] at h2
    change H.sqd = _ at h2
    rw [show H.conj (H.sqd) = - H.sqd from conj_b H] at h2
    have h3 : (2 : H.E) * H.sqd = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact two_ne_zero h4
    · exact b_ne_zero H h4
  have huniv : (Finset.univ : Finset Gal(H.K/ℚ)) = {1, cK} := by
    symm
    rw [Finset.eq_univ_iff_forall]
    intro τ
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective H.E τ
    rw [Finset.mem_insert, Finset.mem_singleton]
    rcases cases_K H σ with h | h
    · left
      apply AlgEquiv.ext
      intro y
      apply Subtype.ext
      have := AlgEquiv.restrictNormal_commutes σ H.K y
      exact this.trans (h _ y.2)
    · right
      apply AlgEquiv.ext
      intro y
      apply Subtype.ext
      have := AlgEquiv.restrictNormal_commutes σ H.K y
      exact (this.trans (h _ y.2)).trans (hcK' y).symm
  have h := Algebra.norm_eq_prod_automorphisms ℚ x
  rw [huniv, Finset.prod_pair hne] at h
  have h2 := congrArg (fun z : H.K => (z : H.E)) h
  rw [← hcK' x]
  exact h2
end Formalism.MainNotions.UnusedSlot33.HK
