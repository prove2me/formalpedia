-- Prove2me | solution 1 for ExtCitation.LocalLevel.isSolvable_of_faithfulSMul_of_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/462e9034-244c-5bf4-91d0-8156a5867a69

import Mathlib
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_ExtCitation_LocalLevel_finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq
import Theorems.Thm_IntermediateField_isSolvable_algEquiv_of_padic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_isSolvable_of_faithfulSMul_of_padic
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "CategoryTheory ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_isSolvable_of_faithfulSMul_of_padic.ExtCitation.LocalLevel"

set_option linter.unusedSectionVars false

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.IsBase LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "IsBase finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq"
namespace SolvProof
p2m_open "ExtCitation.LocalLevel ExtCitation"

theorem exists_isBase (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [MulSemiringAction G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) :
    ∃ (K : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] K), ExtCitation.LocalLevel.IsBase q L G K := by
  haveI : SMulCommClass G ℚ_[q] L := ⟨fun g c x => by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hG]⟩
  refine ⟨IntermediateField.lift (FixedPoints.intermediateField G : IntermediateField ℚ_[q] L), ?_, ?_⟩
  · exact FiniteDimensional.of_injective
      (IntermediateField.inclusion (IntermediateField.lift_le (FixedPoints.intermediateField G : IntermediateField ℚ_[q] L))).toLinearMap
      (fun a b h => (IntermediateField.inclusion
        (IntermediateField.lift_le (FixedPoints.intermediateField G : IntermediateField ℚ_[q] L))).toRingHom.injective h)
  · refine ⟨IntermediateField.lift_le _, fun x => ?_⟩
    rw [IntermediateField.mem_lift]
    exact Iff.rfl

section Solvable
p2m_open "ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_isSolvable_of_faithfulSMul_of_padic.ExtCitation.LocalLevel"

theorem isSolvable_layer (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀] (hK : IsBase q L G K₀) : Group.IsSolvable G := by
  classical
  haveI := Fintype.ofFinite G
  let E' : IntermediateField K₀ (PadicAlgCl q) := IntermediateField.extendScalars hK.le
  have memE : ∀ x : PadicAlgCl q, x ∈ E' ↔ x ∈ L := fun x => Iff.rfl
  let toL : E' → L := fun x => ⟨x.1, (memE x.1).1 x.2⟩
  let ofL : L → E' := fun y => ⟨y.1, (memE y.1).2 y.2⟩
  have hfix : ∀ (g : G) (r : K₀), g • toL (algebraMap K₀ E' r) = toL (algebraMap K₀ E' r) :=
    fun g r => (hK.mem_iff _).1 r.2 g

  let ψ₀ : G → (E' ≃ₐ[K₀] E') := fun g =>
    { toFun := fun x => ofL (g • toL x)
      invFun := fun x => ofL (g⁻¹ • toL x)
      left_inv := fun x => by
        change ofL (g⁻¹ • g • toL x) = x
        rw [← mul_smul, inv_mul_cancel, one_smul]
      right_inv := fun x => by
        change ofL (g • g⁻¹ • toL x) = x
        rw [← mul_smul, mul_inv_cancel, one_smul]
      map_mul' := fun x y => by
        change ofL (g • (toL x * toL y)) = ofL (g • toL x) * ofL (g • toL y)
        rw [smul_mul']
        rfl
      map_add' := fun x y => by
        change ofL (g • (toL x + toL y)) = ofL (g • toL x) + ofL (g • toL y)
        rw [smul_add]
        rfl
      commutes' := fun r => by
        change ofL (g • toL (algebraMap K₀ E' r)) = _
        rw [hfix] }
  have ψ₀_apply : ∀ (g : G) (x : E'), toL (ψ₀ g x) = g • toL x := fun g x => rfl
  let ψ : G →* (E' ≃ₐ[K₀] E') :=
    { toFun := ψ₀
      map_one' := by
        ext x
        change ((ofL ((1 : G) • toL x) : E') : PadicAlgCl q) = x
        rw [one_smul]
      map_mul' := fun g h => by
        ext x
        change ((ofL ((g * h) • toL x) : E') : PadicAlgCl q) = ((ofL (g • toL (ofL (h • toL x))) : E') : PadicAlgCl q)
        rw [mul_smul] }
  have hψ : Function.Injective ψ := by
    intro g h hgh
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro y
    have := congrArg (fun f : E' ≃ₐ[K₀] E' => toL (f (ofL y))) hgh
    exact this

  let eL : E' ≃ₗ[ℚ_[q]] L :=
    { toFun := toL, invFun := ofL, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  haveI : Module.Finite ℚ_[q] E' := Module.Finite.equiv eL.symm
  haveI : FiniteDimensional K₀ E' := Module.Finite.of_restrictScalars_finite ℚ_[q] K₀ E'
  have hdeg : Module.finrank K₀ E' = Fintype.card G := by
    have h1 := ExtCitation.LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq q L G hG K₀ hK.le hK.mem_iff
    have h2 := Module.finrank_mul_finrank ℚ_[q] K₀ E'
    rw [LinearEquiv.finrank_eq eL, h1, Nat.card_eq_fintype_card, mul_comm] at h2
    have hpos : 0 < Module.finrank ℚ_[q] K₀ := Module.finrank_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  have hcard : Fintype.card (E' ≃ₐ[K₀] E') = Module.finrank K₀ E' := by
    apply le_antisymm AlgEquiv.card_le
    rw [hdeg]
    exact Fintype.card_le_of_injective ψ hψ
  haveI : IsGalois K₀ E' := IsGalois.of_card_aut_eq_finrank K₀ E' (by rw [Nat.card_eq_fintype_card]; exact hcard)
  haveI := IntermediateField.isSolvable_algEquiv_of_padic q K₀ E'
  exact solvable_of_solvable_injective hψ

end Solvable

end ExtCitation.LocalLevel.SolvProof

open ExtCitation.LocalLevel.SolvProof in

theorem solution
    (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L'] [FaithfulSMul G L']
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x) :
    Group.IsSolvable G := by
  obtain ⟨K₀, _, hK⟩ := exists_isBase q L' G hG
  exact isSolvable_layer q L' G hG K₀ hK

end S_ExtCitation_LocalLevel_isSolvable_of_faithfulSMul_of_padic
end P2MW
export P2MW.S_ExtCitation_LocalLevel_isSolvable_of_faithfulSMul_of_padic (solution)
