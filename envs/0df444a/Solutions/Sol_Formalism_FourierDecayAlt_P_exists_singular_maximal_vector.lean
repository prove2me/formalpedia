-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.exists_singular_maximal_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:08:39.545526+00:00
-- url     : https://prove2.me/submissions/a6ca8f9c-7da9-4c3b-a057-b3c0e1b072cb

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommonEigenvectors
import Theorems.Thm_Formalism_FourierDecayAlt_P_CommonEigenvectors_common
import Theorems.Thm_Formalism_FourierDecayAlt_P_CommonEigenvectors_diag_move
import Theorems.Thm_Formalism_FourierDecayAlt_P_CommonEigenvectors_hop_move
import Theorems.Thm_Formalism_FourierDecayAlt_P_CommonEigenvectors_hop_weight
import Theorems.Thm_Formalism_FourierDecayAlt_P_CommonEigenvectors_hval_re
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr CommonEigenvectors
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Qr.ExistsSingMax := by
  intro V _ _ _ n E hE S hS hS0
  have hcomm : ∀ a b : Fin n, E a a * E b b = E b b * E a a := by
    intro a b
    have h := hE a a b b
    rw [sub_eq_iff_eq_add] at h
    rw [h]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  have hstab : ∀ a b, ∀ x ∈ S, E a b x ∈ S := by
    intro a b x hx
    exact hS a b x hx
  obtain ⟨G', ν0, hG'S, hG'0, -, hG'ν⟩ :=
    common (fun a => E a a) hcomm Finset.univ S hS0 (fun a => hstab a a)
  obtain ⟨x0, hx0G, hx00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hG'0
  let W : Set (Fin n → ℂ) := {θ | ∃ x ∈ S, x ≠ 0 ∧ ∀ a, E a a x = θ a • x}
  have hWne : W.Nonempty := ⟨ν0, x0, hG'S hx0G, hx00, fun a => hG'ν a (Finset.mem_univ a) x0 hx0G⟩
  have hWfin : W.Finite := by
    refine (Set.Finite.pi (t := fun a => {μ | (E a a).HasEigenvalue μ})
      fun a => Module.End.finite_hasEigenvalue (E a a)).subset ?_
    rintro θ ⟨x, -, hx0, hx⟩
    exact Set.mem_univ_pi.2 fun a =>
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 (hx a), hx0⟩
  obtain ⟨ν, ⟨v, hvS, hv0, hv⟩, hmax⟩ := Set.exists_max_image W hval hWfin hWne
  refine ⟨ν, v, hvS, hv0, ⟨hv, fun a b hab => ?_⟩, fun θ x hxS hx0 hx => hmax θ ⟨x, hxS, hx0, hx⟩⟩
  by_contra hy
  set y := E a b v with hydef
  have hyS : y ∈ S := hstab a b v hvS
  let θ' : Fin n → ℂ := fun c => ν c + ((if c = a then 1 else 0) - (if b = c then 1 else 0))
  have hy' : ∀ c, E c c y = θ' c • y := by
    intro c
    rw [hydef, diag_move hE, hv c, map_smul]
    simp only [θ', add_smul, sub_smul, ite_smul, one_smul, zero_smul]
  have hle := hmax θ' ⟨y, hyS, hy, hy'⟩
  have k1 := hop_weight hy'
  have k2 := hop_move hE a b v
  rw [hop_weight hv, map_smul, ← hydef, ← add_smul, k1] at k2
  have k3 := smul_left_injective ℂ hy k2
  have hv' : hval θ' = hval ν + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    rw [← hval_re, ← hval_re, k3]
    simp
  have hba : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by
    have := Fin.lt_iff_val_lt_val.1 hab
    exact_mod_cast this
  linarith
end Formalism.FourierDecayAlt.P
