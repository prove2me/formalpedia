-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.eFam_li
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:19:35.175053+00:00
-- url     : https://prove2.me/submissions/cc206f05-7557-4052-8f7d-e291bf0d3a2d

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_eFam_of_mem
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_eFam_of_not_mem
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_eq_of_out_sub_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.PairingIndexBounds Formalism.L2.PairingIndexBounds.Mv
variable {k : Type*} [Field k] {A B T : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]
namespace Formalism.L2.PairingIndexBounds.Mv
theorem _root_.solution (A₀ : AddSubgroup A) : LinearIndependent k (eFam (k := k) A₀) := by
  classical
  rw [linearIndependent_iff']
  rintro s g hg ⟨q₀, χ₀⟩ hi₀
  have hli := linearIndependent_monoidHom (Multiplicative A₀) k
  rw [linearIndependent_iff'] at hli
  refine hli ((s.filter (fun i => i.1 = q₀)).image Prod.snd) (fun χ => g (q₀, χ)) ?_ χ₀ ?_
  · funext x
    have h1 := congrFun hg (((Multiplicative.toAdd x : A₀) : A) - q₀.out)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 ⊢
    rw [Finset.sum_image, Finset.sum_filter]
    · refine (Finset.sum_congr rfl ?_).trans h1
      rintro ⟨q, χ⟩ _
      by_cases hq : q = q₀
      · subst hq
        have hm : ((Multiplicative.toAdd x : A₀) : A) - q.out + q.out ∈ A₀ := by
          rw [sub_add_cancel]; exact (Multiplicative.toAdd x).2
        rw [if_pos rfl, eFam_of_mem A₀ (q, χ) _ hm]
        congr 2
        apply Subtype.ext
        simp
      · have hm : ((Multiplicative.toAdd x : A₀) : A) - q₀.out + q.out ∉ A₀ := by
          intro hm
          apply hq
          apply eq_of_out_sub_mem A₀
          have := A₀.sub_mem hm (Multiplicative.toAdd x).2
          have e : ((Multiplicative.toAdd x : A₀) : A) - q₀.out + q.out - ((Multiplicative.toAdd x : A₀) : A)
              = q.out - q₀.out := by abel
          rwa [e] at this
        rw [if_neg hq, eFam_of_not_mem A₀ (q, χ) _ hm, mul_zero]
    · rintro ⟨q, χ⟩ h ⟨q', χ'⟩ h' hh
      rw [Finset.mem_coe, Finset.mem_filter] at h h'
      simp only at hh
      exact Prod.ext (h.2.trans h'.2.symm) hh
  · exact Finset.mem_image.mpr ⟨(q₀, χ₀), Finset.mem_filter.mpr ⟨hi₀, rfl⟩, rfl⟩
end Formalism.L2.PairingIndexBounds.Mv
