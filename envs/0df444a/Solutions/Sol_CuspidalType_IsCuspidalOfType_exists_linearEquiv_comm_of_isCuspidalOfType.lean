-- Prove2me | solution 1 for CuspidalType.IsCuspidalOfType.exists_linearEquiv_comm_of_isCuspidalOfType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/330ba8dd-bdd6-5fd1-baeb-5a2df9699ade

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Theorems.Thm_CuspidalType_IsCuspidalOfType_toSubmodule_eq_top_of_ne_bot
import Theorems.Thm_CuspidalType_character_scalar_mul
import Theorems.Thm_CuspidalType_character_unipotent
import Theorems.Thm_CuspidalType_character_unipotent_mul_diagElem
import Theorems.Thm_CuspidalType_exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly
import Theorems.Thm_CuspidalType_eq_scalarElem_mul_unipotent_or_eq_unipotent_mul_scalarElem_mul_diagElem_of_apply_one_zero_eq_zero
import Theorems.Thm_CuspidalType_exists_conj_eq_torus
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_IsCuspidalOfType_exists_linearEquiv_comm_of_isCuspidalOfType

set_option autoImplicit false

open Polynomial

namespace Ws41
namespace CuspUniq

open CuspidalType

section LinAlg

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

private theorem _root_.Ws41.CuspUniq.trace_eq_neg_charpoly_nextCoeff (f : V →ₗ[K] V) :
    LinearMap.trace K V f = -f.charpoly.nextCoeff := by
  classical
  rw [LinearMap.trace_eq_matrix_trace K (Module.finBasis K V) f, Matrix.trace_eq_neg_charpoly_nextCoeff,
    LinearMap.charpoly_toMatrix]

p2m_export "Ws41.CuspUniq" "trace_eq_neg_charpoly_nextCoeff"
end LinAlg

section GL2

variable {q : ℕ} [Fact q.Prime]

theorem unipotent_zero : unipotent q 0 = 1 := by
  apply Units.ext
  simp [unipotent_val, Matrix.one_fin_two]

theorem scalarElem_comm (d : (ZMod q)ˣ) (g : GL2 q) : g * scalarElem q d = scalarElem q d * g := by
  apply Units.ext
  simp only [Units.val_mul, scalarElem, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact ((Matrix.scalar_commute (d : ZMod q) (fun r' => Commute.all _ _)
    (g : Matrix (Fin 2) (Fin 2) (ZMod q))).eq).symm

end GL2

section Rep

variable {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {θ : (GaloisField q 2)ˣ →* Kˣ} {ρ : Representation K (GL2 q) V}

theorem natCast_ne_zero (K : Type*) [Field K] [CharZero K] : (q : K) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero

theorem natCast_sub_one_ne_zero (K : Type*) [Field K] [CharZero K] : (q : K) - 1 ≠ 0 := by
  have h2 := (Fact.out : q.Prime).two_le
  have h : ((q - 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rwa [Nat.cast_sub (by omega), Nat.cast_one] at h

theorem nontrivial (h : IsCuspidalOfType θ ρ) : Nontrivial V :=
  Module.nontrivial_of_finrank_eq_succ (R := K) (n := q - 2)
    (by rw [h.finrank_eq]; have := (Fact.out : q.Prime).two_le; omega)

theorem irreducible' [CharZero K] (h : IsCuspidalOfType θ ρ) :
    ∀ W : Subrepresentation ρ, W.toSubmodule ≠ ⊥ → W.toSubmodule = ⊤ := fun W hW =>
  h.toSubmodule_eq_top_of_ne_bot (natCast_ne_zero K) (natCast_sub_one_ne_zero K) W hW

theorem isIrreducible [CharZero K] (h : IsCuspidalOfType θ ρ) : ρ.IsIrreducible := by
  haveI := nontrivial h
  haveI : Nontrivial (Subrepresentation ρ) :=
    ⟨⟨⊥, ⊤, fun e => bot_ne_top (α := Submodule K V) (congrArg Subrepresentation.toSubmodule e)⟩⟩
  refine ⟨fun W => ?_⟩
  by_cases hW : W.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hW)
  · exact Or.inr (Subrepresentation.toSubmodule_injective (irreducible' h W hW))

variable {V' : Type*} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  {ρ' : Representation K (GL2 q) V'}

theorem character_eq [IsAlgClosed K] [CharZero K] (h : IsCuspidalOfType θ ρ) (h' : IsCuspidalOfType θ ρ')
    (g : GL2 q) : ρ.character g = ρ'.character g := by
  haveI := nontrivial h
  haveI := nontrivial h'
  by_cases hroot : ∃ x : ZMod q, (g : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly.IsRoot x
  · obtain ⟨x, hx⟩ := hroot
    obtain ⟨c, hc⟩ := exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly q g x hx
    rw [← ρ.char_conj g c, ← ρ'.char_conj g c]
    rcases eq_scalarElem_mul_unipotent_or_eq_unipotent_mul_scalarElem_mul_diagElem_of_apply_one_zero_eq_zero
        q (c * g * c⁻¹) hc with ⟨z, t, hb⟩ | ⟨a, d, s, had, hb⟩
    · rw [hb, character_scalar_mul ρ h.central, character_scalar_mul ρ' h'.central]
      by_cases ht : t = 0
      · subst ht
        rw [unipotent_zero, Representation.char_one, Representation.char_one, h.finrank_eq, h'.finrank_eq]
      · rw [character_unipotent ρ (irreducible' h) h.cuspidal ht,
          character_unipotent ρ' (irreducible' h') h'.cuspidal ht]
    · have ha : a * d⁻¹ ≠ 1 := fun e => had (mul_inv_eq_one.mp e)
      rw [hb, ← mul_assoc, scalarElem_comm, mul_assoc,
        character_scalar_mul ρ h.central, character_scalar_mul ρ' h'.central,
        character_unipotent_mul_diagElem ρ h.cuspidal ha,
        character_unipotent_mul_diagElem ρ' h'.cuspidal ha]
  · simp only [not_exists] at hroot
    obtain ⟨c, α, -, hc⟩ := exists_conj_eq_torus q g hroot
    rw [← ρ.char_conj g c, ← ρ'.char_conj g c, hc]
    have hne : (X - C ((θ α : Kˣ) : K)) * (X - C (((θ α)⁻¹ : Kˣ) : K)) ≠ 0 :=
      mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
    have hcp : (ρ (torus q α)).charpoly = (ρ' (torus q α)).charpoly :=
      mul_right_cancel₀ hne ((h.torus_charpoly α).trans (h'.torus_charpoly α).symm)
    show LinearMap.trace K V _ = LinearMap.trace K V' _
    rw [trace_eq_neg_charpoly_nextCoeff, trace_eq_neg_charpoly_nextCoeff, hcp]

theorem nonempty_equiv [IsAlgClosed K] [CharZero K] (h : IsCuspidalOfType θ ρ) (h' : IsCuspidalOfType θ ρ') :
    Nonempty (ρ'.Equiv ρ) := by
  classical
  haveI := nontrivial h
  haveI := nontrivial h'
  haveI : ρ.IsIrreducible := isIrreducible h
  haveI : ρ'.IsIrreducible := isIrreducible h'
  haveI : Invertible (Nat.card (GL2 q) : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hchar : ∀ g, ρ'.character g = ρ.character g := fun g => (character_eq h h' g).symm
  have key := Representation.char_orthonormal ρ ρ'
  have key1 := Representation.char_orthonormal ρ ρ
  rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at key1
  simp_rw [hchar] at key
  rw [key1] at key
  by_contra hc
  rw [if_neg hc] at key
  exact absurd key (by norm_num)

end Rep

end Ws41.CuspUniq

open Ws41.CuspUniq in
theorem solution
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {θ : (GaloisField q 2)ˣ →* Kˣ}
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {ρ : Representation K (CuspidalType.GL2 q) V}
    {V' : Type*} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] {ρ' : Representation K (CuspidalType.GL2 q) V'}
    (h : CuspidalType.IsCuspidalOfType θ ρ) (h' : CuspidalType.IsCuspidalOfType θ ρ') :
    ∃ e : V ≃ₗ[K] V', ∀ (g : CuspidalType.GL2 q) (v : V), e (ρ g v) = ρ' g (e v) := by
  obtain ⟨φ⟩ := nonempty_equiv h h'
  exact ⟨φ.symm.toLinearEquiv, fun g v =>
    Representation.IntertwiningMap.isIntertwining ρ ρ' φ.symm.toIntertwiningMap g v⟩

end S_CuspidalType_IsCuspidalOfType_exists_linearEquiv_comm_of_isCuspidalOfType
end P2MW
export P2MW.S_CuspidalType_IsCuspidalOfType_exists_linearEquiv_comm_of_isCuspidalOfType (solution)
