-- Prove2me | solution 1 for FiniteField.nonempty_algEquiv_of_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/bc9e955d-bcfe-55bb-9bad-f57e2f9547d2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FiniteField_nonempty_algEquiv_of_card_eq

set_option autoImplicit false

theorem solution
    (K : Type) [Field K] (L₁ : Type) [Field L₁] [Algebra K L₁] [Finite L₁]
    (L₂ : Type) [Field L₂] [Algebra K L₂] [Finite L₂]
    (h : Nat.card L₁ = Nat.card L₂) :
    Nonempty (L₁ ≃ₐ[K] L₂) := by
  classical
  haveI := Fintype.ofFinite L₁
  haveI := Fintype.ofFinite L₂
  have h' : Fintype.card L₁ = Fintype.card L₂ := by
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  haveI i₁ : Polynomial.IsSplittingField K L₁ (Polynomial.X ^ Fintype.card L₁ - Polynomial.X) :=
    FiniteField.isSplittingField_sub L₁ K
  haveI i₂ : Polynomial.IsSplittingField K L₂ (Polynomial.X ^ Fintype.card L₁ - Polynomial.X) := by
    rw [h']; exact FiniteField.isSplittingField_sub L₂ K
  exact ⟨(Polynomial.IsSplittingField.algEquiv L₁ (Polynomial.X ^ Fintype.card L₁ - Polynomial.X)).trans
    (Polynomial.IsSplittingField.algEquiv L₂ (Polynomial.X ^ Fintype.card L₁ - Polynomial.X)).symm⟩

end S_FiniteField_nonempty_algEquiv_of_card_eq
end P2MW
export P2MW.S_FiniteField_nonempty_algEquiv_of_card_eq (solution)
