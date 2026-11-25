-- Prove2me | solution 1 for ChromaticReconstruction.phi_uniformLeafExt_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:37:08.106346+00:00
-- url     : https://prove2.me/submissions/e14b41f8-fe6d-481a-8366-09469dac9182

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Uniform
import Theorems.Thm_ChromaticReconstruction_sum_sigma_const_fin
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_phi_leafExt
import Theorems.Thm_ChromaticReconstruction_prod_compSets_split
import Theorems.Thm_ChromaticReconstruction_sum_compOf
attribute [local simp] ChromaticReconstruction.killP1_X_one
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inr
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inr



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution (q : ℕ) (hq : 2 ≤ q) (G : SimpleGraph V) :
    phi (uniformLeafExt q G) = ∑ F ∈ G.edgeFinset.powerset,
      (-1) ^ ((q - 1) * Fintype.card V - 1 + F.card) * ((q - 1 : ℕ) : ℚ) • innerSum q F := by
  unfold uniformLeafExt
  rw [phi_leafExt (S := G) (m := fun _ => q - 1) (fun _ => by show 1 ≤ q - 1; omega)]
  have hL : ∑ _i : V, (q - 1) = (q - 1) * Fintype.card V := by
    rw [sum_const, card_univ, smul_eq_mul, mul_comm]
  have hw : ∀ C : Finset V, ∑ _i ∈ C, (q - 1 + 1) = q * C.card := by
    intro C; rw [sum_const, smul_eq_mul, Nat.sub_add_cancel (by omega : 1 ≤ q), mul_comm]
  have key : ∀ (x : V) (F : Finset (Sym2 V)), (∏ C ∈ compSets (F : Set (Sym2 V)),
      (X (q * C.card - if x ∈ C then 1 else 0) : MvPolynomial ℕ ℚ)) =
      X (q * (compOf (F : Set (Sym2 V)) x).card - 1) *
        ∏ C ∈ (compSets (F : Set (Sym2 V))).erase (compOf (F : Set (Sym2 V)) x),
          X (q * C.card) := by
    intro x F
    rw [← prod_compSets_split (F : Set (Sym2 V)) x (fun C => X (q * C.card))
      (fun C => X (q * C.card - 1))]
    refine prod_congr rfl fun C _ => ?_
    split_ifs <;> simp
  simp only [hL, hw]
  rw [sum_comm]
  refine sum_congr rfl fun F _ => ?_
  rw [← mul_sum]
  congr 1
  rw [sum_sigma_const_fin (q - 1) (fun x => killP1 (∏ C ∈ compSets (F : Set (Sym2 V)),
      (X (q * C.card - if x ∈ C then 1 else 0) : MvPolynomial ℕ ℚ)))]
  simp only [key]
  rw [sum_compOf (F : Set (Sym2 V)) (fun C0 => killP1
    (X (q * C0.card - 1) * ∏ C ∈ (compSets (F : Set (Sym2 V))).erase C0, X (q * C.card)))]
  rw [innerSum, smul_sum, smul_sum]
  refine sum_congr rfl fun C0 _ => ?_
  rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  rw [Algebra.smul_def, map_natCast]
end ChromaticReconstruction
