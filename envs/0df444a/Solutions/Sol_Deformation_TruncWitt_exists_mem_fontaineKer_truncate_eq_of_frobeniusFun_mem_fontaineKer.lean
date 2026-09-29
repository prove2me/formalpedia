-- Prove2me | solution 1 for Deformation.TruncWitt.exists_mem_fontaineKer_truncate_eq_of_frobeniusFun_mem_fontaineKer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/b318ef42-0d66-5d2d-8b4b-7427f797e1c1

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_TruncWitt_exists_mem_fontaineKer_truncate_eq_of_frobeniusFun_mem_fontaineKer

set_option autoImplicit false

universe u v w

namespace FontaineLift

open Deformation Deformation.TruncWitt

variable {ℛ : Type u} [CommRing ℛ] {p : ℕ} [hp : Fact p.Prime]
variable {A : Type v} [CommRing A] {π : ℛ →+* A}

noncomputable def powCoeff (U : WittVector p ℛ) : WittVector p ℛ :=
  WittVector.mk p fun i => U.coeff i ^ p

omit hp in
@[scoped simp] theorem coeff_powCoeff (U : WittVector p ℛ) (i : ℕ) : (powCoeff U).coeff i = U.coeff i ^ p :=
  congrFun (WittVector.coeff_mk p _) i

theorem truncate_map_powCoeff (n : ℕ) (U : WittVector p ℛ) :
    WittVector.truncate n (WittVector.map π (powCoeff U)) =
      frobeniusFun (WittVector.truncate n (WittVector.map π U)) :=
  TruncatedWittVector.ext fun i => by
    simp only [WittVector.coeff_truncate, WittVector.map_coeff, coeff_powCoeff, map_pow,
      coeff_frobeniusFun]

theorem ghostComponent_powCoeff (m : ℕ) (U : WittVector p ℛ) :
    WittVector.ghostComponent m (powCoeff U) =
      ∑ i ∈ Finset.range (m + 1), (p : ℛ) ^ i * U.coeff i ^ p ^ (m + 1 - i) := by
  rw [WittGhost.ghostComponent_eq_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [coeff_powCoeff, ← pow_mul, ← pow_succ', Nat.succ_sub (Nat.le_of_lt_succ hi)]

noncomputable def extend (m : ℕ) (U : WittVector p ℛ) (c : ℛ) : WittVector p ℛ :=
  WittVector.mk p fun i => if i ≤ m then U.coeff i else if i = m + 1 then c else 0

omit hp in
theorem coeff_extend_of_le {m : ℕ} (U : WittVector p ℛ) (c : ℛ) {i : ℕ} (hi : i ≤ m) :
    (extend m U c).coeff i = U.coeff i := by
  rw [extend, WittVector.coeff_mk, if_pos hi]

omit hp in
theorem coeff_extend_succ (m : ℕ) (U : WittVector p ℛ) (c : ℛ) :
    (extend m U c).coeff (m + 1) = c := by
  rw [extend, WittVector.coeff_mk, if_neg (by omega), if_pos rfl]

theorem ghostComponent_extend (m : ℕ) (U : WittVector p ℛ) (c : ℛ) :
    WittVector.ghostComponent (m + 1) (extend m U c) =
      (∑ i ∈ Finset.range (m + 1), (p : ℛ) ^ i * U.coeff i ^ p ^ (m + 1 - i)) +
        (p : ℛ) ^ (m + 1) * c := by
  rw [WittGhost.ghostComponent_eq_sum, Finset.sum_range_succ, coeff_extend_succ, Nat.sub_self,
    pow_zero, pow_one]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [coeff_extend_of_le U c (Nat.le_of_lt_succ hi)]

theorem exists_mem_fontaineKer_truncate_eq (hπs : Function.Surjective π)
    (hker : RingHom.ker π ≤ Ideal.span {(p : ℛ)}) {n : ℕ} {u : TruncatedWittVector p n A}
    (hu : frobeniusFun u ∈ fontaineKer p n π) :
    ∃ b : TruncatedWittVector p (n + 1) A, b ∈ fontaineKer p (n + 1) π ∧
      TruncatedWittVector.truncate (Nat.le_succ n) b = u := by
  cases n with
  | zero => exact ⟨0, zero_mem _, TruncatedWittVector.ext fun i => i.elim0⟩
  | succ m =>
    obtain ⟨U, rfl⟩ := exists_truncate_map_eq hπs u

    have hG : WittVector.ghostComponent m (powCoeff U) ∈ Ideal.span {(p : ℛ) ^ (m + 1)} := by
      have := (truncate_map_mem_fontaineKer_iff (n := m + 1) hker (powCoeff U)).1
        (by rw [truncate_map_powCoeff]; exact hu)
      rwa [Nat.add_sub_cancel] at this
    rw [ghostComponent_powCoeff] at hG
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hG

    refine ⟨WittVector.truncate (m + 2) (WittVector.map π (extend m U (-t))), ?_, ?_⟩
    · refine truncate_map_mem_fontaineKer ?_
      rw [show m + 2 - 1 = m + 1 from rfl, ghostComponent_extend, ← ht, mul_neg, mul_comm t,
        add_neg_cancel]
      exact zero_mem _
    · rw [TruncatedWittVector.truncate_wittVector_truncate]
      refine TruncatedWittVector.ext fun i => ?_
      rw [WittVector.coeff_truncate, WittVector.coeff_truncate, WittVector.map_coeff,
        WittVector.map_coeff, coeff_extend_of_le U _ (Nat.le_of_lt_succ i.isLt)]

end FontaineLift
p2m_reactivate "P2MW.S_Deformation_TruncWitt_exists_mem_fontaineKer_truncate_eq_of_frobeniusFun_mem_fontaineKer.FontaineLift"

open Deformation Deformation.TruncWitt in
theorem solution
    {ℛ : Type u} [CommRing ℛ] (p : ℕ) [Fact p.Prime]
    {A : Type v} [CommRing A] (π : ℛ →+* A) (hπ : Function.Surjective π)
    (hker : RingHom.ker π ≤ Ideal.span {(p : ℛ)})
    {n : ℕ} {u : TruncatedWittVector p n A}
    (hu : Deformation.TruncWitt.frobeniusFun u ∈ Deformation.TruncWitt.fontaineKer p n π) :
    ∃ b : TruncatedWittVector p (n + 1) A,
      b ∈ Deformation.TruncWitt.fontaineKer p (n + 1) π ∧
      TruncatedWittVector.truncate (Nat.le_succ n) b = u :=
  FontaineLift.exists_mem_fontaineKer_truncate_eq hπ hker hu

end S_Deformation_TruncWitt_exists_mem_fontaineKer_truncate_eq_of_frobeniusFun_mem_fontaineKer
end P2MW
export P2MW.S_Deformation_TruncWitt_exists_mem_fontaineKer_truncate_eq_of_frobeniusFun_mem_fontaineKer (solution)
