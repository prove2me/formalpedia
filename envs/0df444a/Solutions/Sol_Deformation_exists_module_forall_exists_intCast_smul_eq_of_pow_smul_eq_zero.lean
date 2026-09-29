-- Prove2me | solution 1 for Deformation.exists_module_forall_exists_intCast_smul_eq_of_pow_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/35ddabea-aa35-51bc-b3b2-4db0f68faacc

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_exists_module_forall_exists_intCast_smul_eq_of_pow_smul_eq_zero

universe u v

namespace WEK0

variable {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} [Fact p.Prime]

private lemma exists_sub_intCast_mem_span [Algebra 𝓞 (ZMod p)]
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)}) (a : 𝓞) :
    ∃ m : ℤ, a - (m : 𝓞) ∈ Ideal.span {(p : 𝓞)} := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine ⟨((algebraMap 𝓞 (ZMod p) a).val : ℤ), ?_⟩
  rw [← hker, RingHom.mem_ker, map_sub, map_intCast, Int.cast_natCast, ZMod.natCast_zmod_val,
    sub_self]

private lemma exists_sub_intCast_mem_span_pow [Algebra 𝓞 (ZMod p)]
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)}) (k : ℕ) (a : 𝓞) :
    ∃ m : ℤ, a - (m : 𝓞) ∈ Ideal.span {((p : 𝓞) ^ k)} := by
  induction k generalizing a with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih a
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hm
    obtain ⟨m', hm'⟩ := exists_sub_intCast_mem_span hker b
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hm'
    refine ⟨m + (p : ℤ) ^ k * m', Ideal.mem_span_singleton'.mpr ⟨c, ?_⟩⟩
    push_cast
    linear_combination (p : 𝓞) ^ k * hc + hb

private lemma pow_dvd_of_pow_dvd_intCast [Algebra 𝓞 (ZMod p)] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)}) :
    ∀ (k : ℕ) (d : ℤ), (p : 𝓞) ^ k ∣ (d : 𝓞) → (p : ℤ) ^ k ∣ d := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro k
  induction k with
  | zero => intro d _; simp
  | succ k ih =>
    intro d hd
    have hk : (p : 𝓞) ^ k ∣ (d : 𝓞) := (pow_dvd_pow (p : 𝓞) (Nat.le_succ k)).trans hd
    obtain ⟨d', rfl⟩ := ih d hk
    obtain ⟨c, hc⟩ := hd
    push_cast at hc
    have h0 : ((d' : 𝓞) - p * c) * (p : 𝓞) ^ k = 0 := by linear_combination hc
    have h1 : (d' : 𝓞) - p * c = 0 := (mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hp k)).mp h0
    have h2 : (d' : 𝓞) ∈ RingHom.ker (algebraMap 𝓞 (ZMod p)) := by
      rw [hker, Ideal.mem_span_singleton']
      exact ⟨c, by linear_combination -h1⟩
    rw [RingHom.mem_ker, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
    rw [pow_succ]
    exact mul_dvd_mul_left _ h2

private lemma zsmul_eq_zsmul_of_sub_mem [Algebra 𝓞 (ZMod p)] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {M : Type v} [AddCommGroup M] {n : ℕ} (hM : ∀ x : M, (p ^ n : ℤ) • x = 0)
    {m m' : ℤ} (h : (m : 𝓞) - (m' : 𝓞) ∈ Ideal.span {((p : 𝓞) ^ n)}) (x : M) :
    m • x = m' • x := by
  have hd : (p : 𝓞) ^ n ∣ ((m - m' : ℤ) : 𝓞) := by
    push_cast
    exact Ideal.mem_span_singleton.mp h
  obtain ⟨t, ht⟩ := pow_dvd_of_pow_dvd_intCast hp hker n (m - m') hd
  have hx : ((p : ℤ) ^ n) • x = 0 := by exact_mod_cast hM x
  have h0 : (m - m') • x = 0 := by
    rw [ht, mul_comm, mul_smul, hx, smul_zero]
  rwa [sub_smul, sub_eq_zero] at h0

end WEK0

open WEK0 in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (M : Type v) [AddCommGroup M] (n : ℕ) (hM : ∀ x : M, (p ^ n : ℤ) • x = 0) :
    ∃ inst : Module 𝓞 M,
      (∀ (m : ℤ) (x : M), @HSMul.hSMul 𝓞 M M (@instHSMul 𝓞 M inst.toSMul) (m : 𝓞) x = m • x) ∧
      (∀ a : 𝓞, ∃ m : ℤ, ∀ x : M, @HSMul.hSMul 𝓞 M M (@instHSMul 𝓞 M inst.toSMul) a x = m • x) := by
  classical
  choose lift hlift using fun a : 𝓞 => WEK0.exists_sub_intCast_mem_span_pow hker n a
  let I : Ideal 𝓞 := Ideal.span {((p : 𝓞) ^ n)}
  have hl : ∀ a : 𝓞, a - (lift a : 𝓞) ∈ I := hlift
  have key : ∀ {m m' : ℤ}, (m : 𝓞) - (m' : 𝓞) ∈ I → ∀ x : M, m • x = m' • x :=
    fun h x => WEK0.zsmul_eq_zsmul_of_sub_mem hp hker hM h x
  letI S : SMul 𝓞 M := ⟨fun a x => lift a • x⟩
  let inst : Module 𝓞 M := Module.ofMinimalAxioms
    (fun a x y => by
      show lift a • (x + y) = lift a • x + lift a • y
      exact smul_add _ _ _)
    (fun a b x => by
      show lift (a + b) • x = lift a • x + lift b • x
      rw [← add_smul]
      refine key ?_ x
      have e : ((lift (a + b) : ℤ) : 𝓞) - ((lift a + lift b : ℤ) : 𝓞) =
          -((a + b) - lift (a + b)) + (a - lift a) + (b - lift b) := by
        push_cast; ring
      rw [e]
      exact I.add_mem (I.add_mem (I.neg_mem (hl _)) (hl a)) (hl b))
    (fun a b x => by
      show lift (a * b) • x = lift a • (lift b • x)
      rw [← mul_smul]
      refine key ?_ x
      have e : ((lift (a * b) : ℤ) : 𝓞) - ((lift a * lift b : ℤ) : 𝓞) =
          -((a * b) - lift (a * b)) + a * (b - lift b) + (lift b : 𝓞) * (a - lift a) := by
        push_cast; ring
      rw [e]
      exact I.add_mem (I.add_mem (I.neg_mem (hl _)) (I.mul_mem_left _ (hl b)))
        (I.mul_mem_left _ (hl a)))
    (fun x => by
      show lift 1 • x = x
      refine (key (m' := 1) ?_ x).trans (one_smul ℤ x)
      have e : ((lift 1 : ℤ) : 𝓞) - ((1 : ℤ) : 𝓞) = -(1 - lift 1) := by
        push_cast; ring
      rw [e]
      exact I.neg_mem (hl 1))
  refine ⟨inst, fun m x => ?_, fun a => ⟨lift a, fun x => rfl⟩⟩
  show lift (m : 𝓞) • x = m • x
  refine key ?_ x
  have e : ((lift (m : 𝓞) : ℤ) : 𝓞) - ((m : ℤ) : 𝓞) = -((m : 𝓞) - lift (m : 𝓞)) := by
    ring
  rw [e]
  exact I.neg_mem (hl _)

end S_Deformation_exists_module_forall_exists_intCast_smul_eq_of_pow_smul_eq_zero
end P2MW
export P2MW.S_Deformation_exists_module_forall_exists_intCast_smul_eq_of_pow_smul_eq_zero (solution)
