-- Prove2me | solution 1 for Deformation.DieudonneModule.exists_mem_fontaineHodge_add_eq_of_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/929b9494-4f67-54db-8fd1-77d4e13bbb1f

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Theorems.Thm_Deformation_mem_wittHom_of_mem_fontaineKer_of_verschiebung_mem_wittHom
import Theorems.Thm_Deformation_TruncWitt_exists_mem_fontaineKer_truncate_eq_of_frobeniusFun_mem_fontaineKer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_exists_mem_fontaineHodge_add_eq_of_smul_eq_zero

set_option autoImplicit false

universe u v w

namespace FontaineTors

open Deformation Deformation.TruncWitt Deformation.DieudonneModule

variable {p : ℕ} [hp : Fact p.Prime]
variable {k : Type u} [CommRing k] {A : Type v} [CommRing A] [Bialgebra k A]
variable {ℛ : Type w} [CommRing ℛ] {π : ℛ →+* A}

structure Inputs (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] (A : Type v) [CommRing A]
    [Bialgebra k A] {ℛ : Type w} [CommRing ℛ] (π : ℛ →+* A) : Prop where
  crit : ∀ (n : ℕ) (a : TruncatedWittVector p n A), a ∈ fontaineKer p n π →
    TruncWitt.verschiebung a ∈ wittHom k p n A → a ∈ wittHom k p n A
  lift : ∀ (n : ℕ) (u : TruncatedWittVector p n A), frobeniusFun u ∈ fontaineKer p n π →
    ∃ b : TruncatedWittVector p (n + 1) A, b ∈ fontaineKer p (n + 1) π ∧
      TruncatedWittVector.truncate (Nat.le_succ n) b = u

theorem exists_restrict_eq (H : Inputs p k A π) {n : ℕ} (x : wittHom k p n A)
    (hFx : frobeniusFun (x : TruncatedWittVector p n A) ∈ fontaineKer p n π) :
    ∃ b : wittHom k p (n + 1) A, (b : TruncatedWittVector p (n + 1) A) ∈ fontaineKer p (n + 1) π ∧
      wittHomRestrict k p A (Nat.le_succ n) b = x := by
  obtain ⟨b, hb, hbx⟩ := H.lift n x hFx
  have hVb : TruncWitt.verschiebung b ∈ wittHom k p (n + 1) A := by
    rw [← shift_truncate_succ, hbx]
    exact shift_mem_wittHom x.2
  exact ⟨⟨b, H.crit (n + 1) b hb hVb⟩, hb, Subtype.ext hbx⟩

theorem exists_mem_verschiebung_of_eq (H : Inputs p k A π) {n : ℕ} (x : wittHom k p n A)
    (hFx : frobeniusFun (x : TruncatedWittVector p n A) ∈ fontaineKer p n π) :
    ∃ b : wittHom k p (n + 1) A, of k p A (n + 1) b ∈ fontaineHodge k p π ∧
      wittHomVerschiebung k p (n + 1) A b = wittHomShift k p n A x := by
  obtain ⟨b, hb, hbx⟩ := exists_restrict_eq H x hFx
  exact ⟨b, of_mem_fontaineHodge hb, by rw [← wittHomShift_restrict, hbx]⟩

theorem exists_mem_add_eq_of_smul_eq_zero (H : Inputs p k A π) (hpA : (p : A) = 0)
    {z : DieudonneModule k p A} (hz : (p : ℤ) • z = 0) :
    ∃ y ∈ fontaineHodge k p π, ∃ x : DieudonneModule k p A,
      verschiebung k p A x = 0 ∧ y + x = z := by
  obtain ⟨n, ξ, rfl⟩ := exists_of z
  cases n with
  | zero =>
    refine ⟨0, zero_mem _, of k p A 0 ξ, ?_, zero_add _⟩
    rw [verschiebung_of]
    have : wittHomVerschiebung k p 0 A ξ = 0 := Subtype.ext (TruncatedWittVector.ext fun i => i.elim0)
    rw [this, map_zero]
  | succ m =>

    have hpξ : (p : ℤ) • ξ = 0 := of_injective (m + 1) (by rw [map_zsmul, hz, map_zero])
    have hVF : TruncWitt.verschiebung (frobeniusFun (ξ : TruncatedWittVector p (m + 1) A)) = 0 := by
      rw [verschiebung_frobeniusFun hpA]
      exact congrArg Subtype.val hpξ
    set ξ' : wittHom k p m A := wittHomRestrict k p A (Nat.le_succ m) ξ with hξ'
    have hFξ' : frobeniusFun (ξ' : TruncatedWittVector p m A) = 0 := by
      refine TruncatedWittVector.ext fun i => ?_
      rw [coeff_frobeniusFun, hξ', coe_wittHomRestrict, TruncatedWittVector.coeff_truncate,
        TruncatedWittVector.coeff_zero]
      have hi : (i : ℕ) + 1 < m + 1 := by omega
      have h := congrArg (TruncatedWittVector.coeff ⟨(i : ℕ) + 1, hi⟩) hVF
      rw [coeff_verschiebung_succ _ _ hi, coeff_frobeniusFun, TruncatedWittVector.coeff_zero] at h
      rw [show Fin.castLE (Nat.le_succ m) i = ⟨(i : ℕ), Nat.lt_of_succ_lt hi⟩ from Fin.ext rfl]
      exact h
    have hFξ'K : frobeniusFun (ξ' : TruncatedWittVector p m A) ∈ fontaineKer p m π := by
      rw [hFξ']; exact zero_mem _
    obtain ⟨b, hbL, hVb⟩ := exists_mem_verschiebung_of_eq H ξ' hFξ'K

    rw [hξ', wittHomShift_restrict] at hVb
    refine ⟨of k p A (m + 1) b, hbL, of k p A (m + 1) (ξ - b), ?_, ?_⟩
    · rw [verschiebung_of, map_sub, hVb, sub_self, map_zero]
    · rw [← map_add, add_sub_cancel]

namespace Inst
open scoped TensorProduct

theorem natCast_mem_nonZeroDivisors {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} {ℛ : Type w} [CommRing ℛ]
    [Algebra 𝓞 ℛ] [Module.Flat 𝓞 ℛ] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) :
    (p : ℛ) ∈ nonZeroDivisors ℛ := by
  have hreg : IsSMulRegular ℛ (p : 𝓞) := Module.Flat.isSMulRegular_of_nonZeroDivisors hp
  refine mem_nonZeroDivisors_iff_right.2 fun x hx => hreg ?_
  change (p : 𝓞) • x = (p : 𝓞) • (0 : ℛ)
  rw [smul_zero, Algebra.smul_def, map_natCast, mul_comm, hx]

variable {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} [Fact p.Prime]
variable {k : Type v} [CommRing k] [Algebra 𝓞 k]
variable {ℛ : Type w} [CommRing ℛ] [Bialgebra 𝓞 ℛ] [Module.Flat 𝓞 ℛ]

theorem inputs (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) :
    @Inputs p _ k _ (k ⊗[𝓞] ℛ) inferInstance inferInstance ℛ _
      (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom where
  crit _ _ ha hVa := mem_wittHom_of_mem_fontaineKer_of_verschiebung_mem_wittHom p hp hk hker ℛ ha hVa
  lift n u hu :=
    @TruncWitt.exists_mem_fontaineKer_truncate_eq_of_frobeniusFun_mem_fontaineKer ℛ _ p _
      (k ⊗[𝓞] ℛ) inferInstance
      (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom
      (SpecialFibre.reduction_surjective hk) (SpecialFibre.ker_reduction_eq_span hk hker).le n u hu

end Inst

end FontaineTors

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {k : Type v} [CommRing k] [Algebra 𝓞 k]
    (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (ℛ : Type w) [CommRing ℛ] [Bialgebra 𝓞 ℛ] [Module.Flat 𝓞 ℛ]
    {z : Deformation.DieudonneModule k p (TensorProduct 𝓞 k ℛ)} (hz : (p : ℤ) • z = 0) :
    ∃ y ∈ Deformation.fontaineHodge k p
        (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 k ℛ).toRingHom,
      ∃ x : Deformation.DieudonneModule k p (TensorProduct 𝓞 k ℛ),
        Deformation.DieudonneModule.verschiebung k p (TensorProduct 𝓞 k ℛ) x = 0 ∧ y + x = z :=
  FontaineTors.exists_mem_add_eq_of_smul_eq_zero (FontaineTors.Inst.inputs hp hk hker)
    (Deformation.SpecialFibre.natCast_eq_zero hk hker) hz

end S_Deformation_DieudonneModule_exists_mem_fontaineHodge_add_eq_of_smul_eq_zero
end P2MW
export P2MW.S_Deformation_DieudonneModule_exists_mem_fontaineHodge_add_eq_of_smul_eq_zero (solution)
