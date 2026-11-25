-- Prove2me | solution 1 for CongruenceSubgroup.index_Gamma1_eq_sq_mul_prod_primeFactors
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T14:02:53.637858+00:00
-- url     : https://prove2.me/submissions/32817393-f16b-4fef-bfd0-1c1b7d6f3573

import Mathlib
import Definitions.Def_RPLib_S3_HypParI

set_option autoImplicit false

open scoped MatrixGroups

namespace UploadSW112432

open CongruenceSubgroup RamanujanPetersson
open scoped RamanujanPetersson.S3.Conj

open Classical in
/-- `Γ₁(M)` is the stabilizer of `e₁ = (1, 0)` for the action on `(ℤ/M)²`, whose orbit is the set of vectors of
exact order `M`; so the index is the number of such vectors. -/
theorem index_eq_card (M : ℕ) [NeZero M] :
    (Gamma1 M).index = (Finset.univ.filter fun v : Fin 2 → ZMod M => S3.Conj.IsExact M v).card := by
  have hstab : Gamma1 M = MulAction.stabilizer SL(2, ℤ) (S3.Conj.e1 M) := by
    ext g
    rw [S3.Conj.mem_Gamma1_iff, MulAction.mem_stabilizer_iff]
  have horb : MulAction.orbit SL(2, ℤ) (S3.Conj.e1 M) = {v | S3.Conj.IsExact M v} := by
    ext v
    constructor
    · rintro ⟨g, rfl⟩
      exact S3.Conj.isExact_smul (S3.Conj.isExact_e1 M) g
    · intro hv
      exact ⟨S3.Conj.rep v, S3.Conj.rep_spec hv⟩
  rw [hstab, MulAction.index_stabilizer, horb, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

/-- `±Γ = Γ ⊔ ⟨-1⟩`. -/
theorem pmSL_eq (Γ : Subgroup SL(2, ℤ)) :
    RP.FundDomain.pmSL Γ = Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) := by
  apply le_antisymm
  · intro g hg
    rcases RP.FundDomain.mem_pmSL.1 hg with h | h
    · exact Subgroup.mem_sup_left h
    · have e : g = -g * (-1 : SL(2, ℤ)) := by simp
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  · refine sup_le (RP.FundDomain.le_pmSL Γ) ?_
    rw [Subgroup.zpowers_le]
    exact RP.FundDomain.mem_pmSL.2 (Or.inr (by rw [neg_neg]; exact Γ.one_mem))

end UploadSW112432

open UploadSW112432 RamanujanPetersson in
theorem solution (M : ℕ) [NeZero M] :
    ((CongruenceSubgroup.Gamma1 M).index : ℚ) =
        (M : ℚ) ^ 2 * ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℚ) ^ 2) ∧
      ((CongruenceSubgroup.Gamma1 M).index : ℚ) =
        ((M : ℚ) * ∏ p ∈ M.primeFactors, (1 + 1 / (p : ℚ))) * (M.totient : ℚ) ∧
      (3 ≤ M → ((CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index : ℚ) =
        (M : ℚ) ^ 2 / 2 * ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℚ) ^ 2)) := by
  have hcard : ((CongruenceSubgroup.Gamma1 M).index : ℚ) = S3.dedekindPsi M * (Nat.totient M : ℚ) := by
    rw [index_eq_card, HypPar.card_exact_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [hcard, HypPar.psi_mul_totient]
  · rw [hcard, S3.dedekindPsi]
  · intro hM
    have h2 := HypPar.two_mul_index (M := M) hM
    rw [pmSL_eq, HypPar.psi_mul_totient] at h2
    linear_combination h2 / 2
