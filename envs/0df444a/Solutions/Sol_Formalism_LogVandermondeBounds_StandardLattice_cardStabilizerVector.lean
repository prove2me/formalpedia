-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.cardStabilizerVector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:53:00.209388+00:00
-- url     : https://prove2.me/submissions/9fadcdeb-3f5f-4069-a09a-c3ca8fff425c

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_CardStabilizerVector
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_vecMul_inv_eq_iff
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_exists_row

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution : CardStabilizerVector := by
  intro F _ _ _ n v hv
  have hcardne : Fintype.card {w : Fin n → F // w ≠ 0} = Fintype.card F ^ n - 1 := by
    have h := Fintype.card_congr (Equiv.optionSubtypeNe (0 : Fin n → F))
    rw [Fintype.card_option, Fintype.card_fun, Fintype.card_fin] at h
    omega
  have horbit : Nat.card (@MulAction.orbit (GL (Fin n) F) (RowVec F n) _ v) =
      Fintype.card F ^ n - 1 := by
    have e : @MulAction.orbit (GL (Fin n) F) (RowVec F n) _ v ≃ {w : Fin n → F // w ≠ 0} :=
      Equiv.subtypeEquivRight (fun w => by
        refine MulAction.mem_orbit_iff.trans ?_
        constructor
        · rintro ⟨g, rfl⟩ h0
          apply hv
          have h1 : Matrix.vecMul (Matrix.vecMul v ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
              (g : Matrix (Fin n) (Fin n) F) = v := by
            rw [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]
          have h0' : Matrix.vecMul v ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 0 := h0
          rw [← h1, h0', Matrix.zero_vecMul]
        · intro hw0
          obtain ⟨A, hA⟩ := exists_row v w hv hw0
          refine ⟨A⁻¹, ?_⟩
          show Matrix.vecMul v (((A⁻¹)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = w
          rw [inv_inv, hA])
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, hcardne]
  have hstab : Fintype.card {A : GL (Fin n) F // Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F) = v} =
      Nat.card (@MulAction.stabilizer (GL (Fin n) F) (RowVec F n) _ _ v) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun A => by
      exact (vecMul_inv_eq_iff v A).symm))
  have hos : Nat.card (@MulAction.stabilizer (GL (Fin n) F) (RowVec F n) _ _ v) *
      Nat.card (@MulAction.orbit (GL (Fin n) F) (RowVec F n) _ v) = Nat.card (GL (Fin n) F) := by
    first
    | (rw [← MulAction.index_stabilizer]; exact Subgroup.card_mul_index _)
    | (rw [mul_comm]; exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group _ _)
    | (rw [mul_comm, ← Nat.card_prod]; exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup _ _))
  rw [hstab, ← horbit, hos, Nat.card_eq_fintype_card]
end Formalism.LogVandermondeBounds.StandardLattice
