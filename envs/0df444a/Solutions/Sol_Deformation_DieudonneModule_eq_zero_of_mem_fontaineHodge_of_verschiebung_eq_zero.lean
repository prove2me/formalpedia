-- Prove2me | solution 1 for Deformation.DieudonneModule.eq_zero_of_mem_fontaineHodge_of_verschiebung_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/dedbf005-f5d7-5322-9d3f-40f93c787743

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_eq_zero_of_mem_fontaineHodge_of_verschiebung_eq_zero

set_option autoImplicit false

universe u v w

namespace FontaineSH3

open Deformation Deformation.TruncWitt

variable {ℛ : Type u} [CommRing ℛ] {p : ℕ} [hp : Fact p.Prime]
variable {A : Type w} [CommRing A] {π : ℛ →+* A}

omit hp in

theorem natCast_eq_zero_of_ker_eq (hker : RingHom.ker π = Ideal.span {(p : ℛ)}) : (p : A) = 0 := by
  have : (p : ℛ) ∈ RingHom.ker π := hker ▸ Ideal.mem_span_singleton_self _
  rwa [RingHom.mem_ker, map_natCast] at this

theorem eq_zero_of_mem_fontaineKer_of_forall_coeff_castSucc_eq_zero
    (hp' : (p : ℛ) ∈ nonZeroDivisors ℛ) (hker : RingHom.ker π = Ideal.span {(p : ℛ)}) {n : ℕ}
    {a : TruncatedWittVector p (n + 1) A} (ha : a ∈ fontaineKer p (n + 1) π)
    (h0 : ∀ i : Fin n, a.coeff i.castSucc = 0) : a = 0 := by
  obtain ⟨X, rfl, hX⟩ := ha
  rw [Nat.add_sub_cancel] at hX

  have hXi : ∀ i < n, X.coeff i ∈ Ideal.span {(p : ℛ)} := by
    intro i hi
    rw [← hker, RingHom.mem_ker, ← WittVector.map_coeff]
    have := h0 ⟨i, hi⟩
    rwa [WittVector.coeff_truncate] at this

  have hsplit : WittVector.ghostComponent n X =
      (∑ i ∈ Finset.range n, (p : ℛ) ^ i * X.coeff i ^ p ^ (n - i)) + (p : ℛ) ^ n * X.coeff n := by
    rw [WittGhost.ghostComponent_eq_sum, Finset.sum_range_succ, Nat.sub_self, pow_zero, pow_one]
  have hS : (∑ i ∈ Finset.range n, (p : ℛ) ^ i * X.coeff i ^ p ^ (n - i)) ∈
      Ideal.span {(p : ℛ) ^ (n + 1)} :=
    Ideal.sum_mem _ fun i hi => by
      rw [Finset.mem_range] at hi
      exact WittGhost.pow_mul_pow_mem_span_pow (hXi i hi) hi.le
  have hlast : (p : ℛ) ^ n * X.coeff n ∈ Ideal.span {(p : ℛ) ^ (n + 1)} := by
    have : (p : ℛ) ^ n * X.coeff n = WittVector.ghostComponent n X -
        ∑ i ∈ Finset.range n, (p : ℛ) ^ i * X.coeff i ^ p ^ (n - i) := by
      rw [hsplit]; ring
    rw [this]
    exact sub_mem hX hS

  have hXn : X.coeff n ∈ Ideal.span {(p : ℛ)} := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hlast
    have hpn : (p : ℛ) ^ n ∈ nonZeroDivisors ℛ := Submonoid.pow_mem _ hp' n
    have h0 : (X.coeff n - (p : ℛ) * c) * (p : ℛ) ^ n = 0 := by
      rw [sub_mul, mul_comm (X.coeff n), hc]; ring
    have := mem_nonZeroDivisors_iff_right.1 hpn _ h0
    rw [sub_eq_zero] at this
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

  have hpA : (p : A) = 0 := natCast_eq_zero_of_ker_eq hker
  refine TruncatedWittVector.ext fun i => ?_
  rw [TruncatedWittVector.coeff_zero]
  refine Fin.lastCases ?_ (fun j => h0 j) i
  rw [WittVector.coeff_truncate, WittVector.map_coeff, Fin.val_last]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hXn
  rw [← hb, map_mul, map_natCast, hpA, mul_zero]

theorem eq_zero_of_mem_fontaineKer_of_verschiebung_eq_zero
    (hp' : (p : ℛ) ∈ nonZeroDivisors ℛ) (hker : RingHom.ker π = Ideal.span {(p : ℛ)}) {n : ℕ}
    {a : TruncatedWittVector p n A} (ha : a ∈ fontaineKer p n π)
    (hV : TruncWitt.verschiebung a = 0) : a = 0 := by
  cases n with
  | zero => exact TruncatedWittVector.ext fun i => i.elim0
  | succ n =>
    refine eq_zero_of_mem_fontaineKer_of_forall_coeff_castSucc_eq_zero hp' hker ha fun i => ?_
    have h := congrArg (TruncatedWittVector.coeff i.succ) hV
    rw [TruncatedWittVector.coeff_zero] at h
    have hi : (i : ℕ) + 1 < n + 1 := by omega
    have h' := coeff_verschiebung_succ a i hi
    rw [show (⟨(i : ℕ) + 1, hi⟩ : Fin (n + 1)) = i.succ from Fin.ext rfl] at h'
    rw [h'] at h
    rw [show i.castSucc = ⟨(i : ℕ), Nat.lt_of_succ_lt hi⟩ from Fin.ext rfl]
    exact h

end FontaineSH3

open Deformation Deformation.TruncWitt Deformation.DieudonneModule in
theorem solution
    {ℛ : Type u} [CommRing ℛ] (p : ℕ) [Fact p.Prime] (hp : (p : ℛ) ∈ nonZeroDivisors ℛ)
    {R : Type v} [CommRing R] {A : Type w} [CommRing A] [Bialgebra R A]
    (π : ℛ →+* A) (hker : RingHom.ker π = Ideal.span {(p : ℛ)})
    {z : Deformation.DieudonneModule R p A} (hz : z ∈ Deformation.fontaineHodge R p π)
    (hV : Deformation.DieudonneModule.verschiebung R p A z = 0) : z = 0 := by
  obtain ⟨n, x, hx, rfl⟩ := hz
  rw [verschiebung_of] at hV
  have hVx : wittHomVerschiebung R p n A x = 0 := of_injective n (hV.trans (map_zero _).symm)
  have hx0 : (x : TruncatedWittVector p n A) = 0 :=
    FontaineSH3.eq_zero_of_mem_fontaineKer_of_verschiebung_eq_zero hp hker hx
      (by rw [← coe_wittHomVerschiebung, hVx]; rfl)
  have : x = 0 := Subtype.ext hx0
  rw [this, map_zero]

end S_Deformation_DieudonneModule_eq_zero_of_mem_fontaineHodge_of_verschiebung_eq_zero
end P2MW
export P2MW.S_Deformation_DieudonneModule_eq_zero_of_mem_fontaineHodge_of_verschiebung_eq_zero (solution)
