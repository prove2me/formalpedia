-- Prove2me | solution 1 for Castro2006.schur_zassenhaus_abelian
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T16:14:18.125531+00:00
-- url     : https://prove2.me/submissions/d98c2068-87cc-4e14-b211-7eedf0f4def5

import Mathlib

/-- The class in `A.QuotientDiff` of a complement `K` of `A`, viewed as a left transversal. -/
noncomputable def Castro2006_qd {E : Type} [Group E] [Finite E]
    (A : Subgroup E) [IsMulCommutative A] (K : Subgroup E) (hK : K.IsComplement' A) :
    A.QuotientDiff :=
  Quotient.mk'' (⟨(K : Set E), hK⟩ : A.LeftTransversal)

open MulOpposite MulAction Pointwise in
/-- A complement `K` of an abelian normal subgroup `A` of coprime order and index is the
stabilizer of its own class in `A.QuotientDiff`. -/
theorem Castro2006_complement_eq_stabilizer {E : Type} [Group E] [Finite E]
    (A : Subgroup E) [A.Normal] [IsMulCommutative A]
    (hcop : Nat.Coprime (Nat.card A) A.index) (K : Subgroup E) (hK : K.IsComplement' A) :
    K = stabilizer E (Castro2006_qd A K hK) := by
  have hle : K ≤ stabilizer E (Castro2006_qd A K hK) := by
    intro k hk
    rw [mem_stabilizer_iff]
    change Quotient.mk'' (op k⁻¹ • (⟨(K : Set E), hK⟩ : A.LeftTransversal)) = _
    congr 1
    apply Subtype.ext
    change op k⁻¹ • (K : Set E) = (K : Set E)
    ext x
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [op_smul_eq_mul]
      exact K.mul_mem hy (K.inv_mem hk)
    · intro hx
      refine ⟨x * k, K.mul_mem hx hk, ?_⟩
      rw [op_smul_eq_mul, mul_inv_cancel_right]
  refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
  have h1 := hK.card_mul_card
  have h2 := (Subgroup.isComplement'_stabilizer_of_coprime
    (α := Castro2006_qd A K hK)
    hcop).card_mul_card
  have hpos : 0 < Nat.card A := Nat.card_pos
  rw [mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left hpos (h2.trans h1.symm)

theorem solution {E : Type} [Group E] [Fintype E] (k m : ℕ)
    (hcard : Fintype.card E = k * m) (hcop : k.Coprime m)
    (A : Subgroup E) [A.Normal] [IsMulCommutative A] (hA : Nat.card A = k) :
    (∃ H : Subgroup E, H.IsComplement' A) ∧
    (∀ H₁ H₂ : Subgroup E, Nat.card H₁ = m → Nat.card H₂ = m →
      ∃ g : E, H₁.map (MulAut.conj g).toMonoidHom = H₂) := by
  have hcardE : Nat.card E = k * m := by rw [Nat.card_eq_fintype_card, hcard]
  have hk : 0 < k := by
    rw [← hA]; exact Nat.card_pos
  have hidx : A.index = m := by
    have := A.card_mul_index
    rw [hA, hcardE] at this
    exact Nat.eq_of_mul_eq_mul_left hk this
  have hcop' : Nat.Coprime (Nat.card A) A.index := by rw [hA, hidx]; exact hcop
  refine ⟨Subgroup.exists_left_complement'_of_coprime hcop', ?_⟩
  intro H₁ H₂ h₁ h₂
  have hc : ∀ H : Subgroup E, Nat.card H = m → H.IsComplement' A := fun H hH =>
    Subgroup.isComplement'_of_coprime (by rw [hH, hA, hcardE, mul_comm])
      (by rw [hH, hA]; exact hcop.symm)
  have e₁ := Castro2006_complement_eq_stabilizer A hcop' H₁ (hc H₁ h₁)
  have e₂ := Castro2006_complement_eq_stabilizer A hcop' H₂ (hc H₂ h₂)
  obtain ⟨a, ha⟩ := Subgroup.exists_smul_eq hcop'
    (Castro2006_qd A H₁ (hc H₁ h₁)) (Castro2006_qd A H₂ (hc H₂ h₂))
  refine ⟨(a : E), ?_⟩
  rw [e₂, ← ha, Subgroup.smul_def, MulAction.stabilizer_smul_eq_stabilizer_map_conj, ← e₁]
