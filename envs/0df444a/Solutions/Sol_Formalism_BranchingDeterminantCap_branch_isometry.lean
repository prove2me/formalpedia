-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.branch_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:59.948733+00:00
-- url     : https://prove2.me/submissions/ee272a82-1024-49b1-86ac-b231b1f960cf

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
import Theorems.Thm_Formalism_BranchingDeterminantCap_bs_fock_smul_left
import Theorems.Thm_Formalism_BranchingDeterminantCap_bs_fock_smul_right
import Theorems.Thm_Formalism_BranchingDeterminantCap_BsForm_eq_zero
import Theorems.Thm_Formalism_BranchingDeterminantCap_bs_extM_conj
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylRowStable
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockRowAdj
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
open Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : BranchIsometry := by
  intro n sg hsg io heq f h hh
  obtain ⟨io', hio'⟩ := LinearMap.exists_extend io
  have hio : ∀ p (hp : p ∈ dualWeyl ℂ n n sg), io' p = io ⟨p, hp⟩ := by
    intro p hp
    rw [← hio']
    rfl
  have hact : ∀ (g : Matrix (Fin n) (Fin n) ℂ), ∀ p ∈ dualWeyl ℂ n n sg,
      io' (rowAct ℂ g p) = rowAct ℂ (extM ℂ g) (io' p) := by
    intro g p hp
    rw [hio _ (dualWeylRowStable ℂ n n sg g p hp), hio p hp]
    exact heq g ⟨p, hp⟩ ⟨_, dualWeylRowStable ℂ n n sg g p hp⟩ rfl
  let D : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ → ℂ := fun p q =>
    fockF (io' p) (io' q) * fockF (hw ℂ le_rfl sg) (hw ℂ le_rfl sg) -
      fockF (io' (hw ℂ le_rfl sg)) (io' (hw ℂ le_rfl sg)) * fockF p q
  have H : BsForm sg D := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro p p' q
      simp only [D, map_add, fischerInner_add_left]; ring
    · intro c p q
      simp only [D, map_smul, bs_fock_smul_left]; ring
    · intro p q q'
      simp only [D, map_add, fischerInner_add_right]; ring
    · intro c p q
      simp only [D, map_smul, bs_fock_smul_right]; ring
    · intro g p hp q hq
      simp only [D]
      rw [hact g p hp, hact _ q hq, fockRowAdj (n + 1) n, fockRowAdj n n, bs_extM_conj]
  have h0 : D (hw ℂ le_rfl sg) (hw ℂ le_rfl sg) = 0 := by
    simp only [D]; ring
  have e := H.eq_zero hsg h0 f f.2 f f.2
  simp only [D] at e
  have e1 : io' (f : MvPolynomial (Fin n × Fin n) ℂ) = io f := hio _ f.2
  have e2 : io' (hw ℂ le_rfl sg) = io h := by
    rw [← hh]; exact hio _ h.2
  rw [e1, e2] at e
  rw [hh]
  exact sub_eq_zero.mp e
end Formalism.BranchingDeterminantCap
