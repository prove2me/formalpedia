-- Prove2me | solution 1 for Deformation.wittHomShift_surjective_of_forall_convPow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a95cf492-2c46-5ec9-964f-422976862d4a

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Theorems.Thm_Deformation_convPow_prime_apply_coeff_of_mem_wittHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_wittHomShift_surjective_of_forall_convPow_eq_zero

set_option autoImplicit false

namespace Deformation
p2m_export "Deformation" "TruncWitt.shift TruncWitt.coeff_shift_zero TruncWitt.coeff_shift_succ wittHom mem_wittHom_iff counit_coeff_of_mem_wittHom wittHomShift convPow_prime_apply_coeff_of_mem_wittHom"
namespace WittHomLevel
p2m_open "Deformation"

p2m_open "Deformation.TruncWitt"

universe u v

variable (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
variable (A : Type v) [CommRing A] [Bialgebra k A]

abbrev Bd : Type (max u v) := WithConv (A →ₗ[k] k)

theorem convPow_pow_apply_coeff {n : ℕ} {x : TruncatedWittVector p n A} (hx : x ∈ wittHom k p n A)
    (i : ℕ) (hi : i < n) (β : Bd k A) :
    (β ^ p ^ i).ofConv (x.coeff ⟨i, hi⟩) = (β.ofConv (x.coeff ⟨0, Nat.zero_lt_of_lt hi⟩)) ^ p ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, pow_mul,
      (Deformation.convPow_prime_apply_coeff_of_mem_wittHom k p A k (β ^ p ^ i) hx).2 i hi,
      ih (Nat.lt_of_succ_lt hi), ← pow_mul]

omit [CharP k p] in

theorem one_ofConv_coeff {n : ℕ} {x : TruncatedWittVector p n A} (hx : x ∈ wittHom k p n A)
    (i : Fin n) : (1 : Bd k A).ofConv (x.coeff i) = 0 := by
  rw [LinearMap.convOne_apply, counit_coeff_of_mem_wittHom hx, map_zero]

omit [CharP k p] in

theorem mem_wittHom_of_shift_mem {n : ℕ} {x : TruncatedWittVector p n A}
    (hx : TruncWitt.shift x ∈ wittHom k p (n + 1) A) : x ∈ wittHom k p n A := by
  rw [mem_wittHom_iff] at hx ⊢
  rw [map_shift, map_shift, map_shift, ← map_add] at hx
  exact shift_injective hx

variable {k p A}

theorem coeff_zero_eq_zero {n : ℕ}
    (hV : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ n = 0)
    {m : ℕ} (hnm : n < m) {x : TruncatedWittVector p m A} (hx : x ∈ wittHom k p m A) :
    x.coeff ⟨0, Nat.zero_lt_of_lt hnm⟩ = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff k]
  intro φ

  let β : Bd k A := WithConv.toConv φ
  let β' : Bd k A := β - (β.ofConv 1) • (1 : Bd k A)
  have hβ' : β'.ofConv 1 = 0 := by
    simp only [β', WithConv.ofConv_sub, WithConv.ofConv_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.convOne_apply, Bialgebra.counit_one, map_one, smul_eq_mul,
      mul_one, sub_self]
  have h1 : (β' ^ p ^ n).ofConv (x.coeff ⟨n, hnm⟩) = 0 := by
    rw [hV β' hβ']; rfl
  have h2 : (β'.ofConv (x.coeff ⟨0, Nat.zero_lt_of_lt hnm⟩)) ^ p ^ n = 0 := by
    rw [← convPow_pow_apply_coeff k p A hx n hnm β', h1]
  have h3 : β'.ofConv (x.coeff ⟨0, Nat.zero_lt_of_lt hnm⟩) = 0 :=
    (pow_eq_zero_iff (pow_ne_zero _ hp.out.ne_zero)).1 h2
  have h4 : β.ofConv (x.coeff ⟨0, Nat.zero_lt_of_lt hnm⟩) = 0 := by
    have e : β = β' + (β.ofConv 1) • (1 : Bd k A) := by simp [β']
    rw [e, WithConv.ofConv_add, WithConv.ofConv_smul, LinearMap.add_apply, LinearMap.smul_apply,
      h3, one_ofConv_coeff k p A hx, smul_zero, add_zero]
  exact h4

theorem wittHomShift_surjective {n : ℕ}
    (hV : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ n = 0)
    (m : ℕ) (hm : n ≤ m) : Function.Surjective (wittHomShift k p m A) := by
  intro x
  have h0 : (x : TruncatedWittVector p (m + 1) A).coeff ⟨0, m.succ_pos⟩ = 0 :=
    coeff_zero_eq_zero hV (Nat.lt_succ_of_le hm) x.2
  let x' : TruncatedWittVector p m A :=
    TruncatedWittVector.mk p fun j => (x : TruncatedWittVector p (m + 1) A).coeff j.succ
  have hx' : TruncWitt.shift x' = x := by
    refine TruncatedWittVector.ext fun j => ?_
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [TruncWitt.coeff_shift_zero]; exact h0.symm
    · rw [TruncWitt.coeff_shift_succ, TruncatedWittVector.coeff_mk]
  have hmem : x' ∈ wittHom k p m A := by
    apply mem_wittHom_of_shift_mem k p A
    rw [hx']
    exact x.2
  exact ⟨⟨x', hmem⟩, Subtype.ext hx'⟩

end Deformation.WittHomLevel

universe u v in

theorem solution
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [Bialgebra k A] (n : ℕ)
    (hV : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ n = 0)
    (m : ℕ) (hm : n ≤ m) :
    Function.Surjective (Deformation.wittHomShift k p m A) :=
  Deformation.WittHomLevel.wittHomShift_surjective hV m hm

end S_Deformation_wittHomShift_surjective_of_forall_convPow_eq_zero
end P2MW
export P2MW.S_Deformation_wittHomShift_surjective_of_forall_convPow_eq_zero (solution)
