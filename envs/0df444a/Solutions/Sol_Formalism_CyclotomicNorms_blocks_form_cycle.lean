-- Prove2me | solution 1 for Formalism.CyclotomicNorms.blocks_form_cycle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:53.108993+00:00
-- url     : https://prove2.me/submissions/2d1a9db6-4aeb-4aff-bd1c-af118b059f95

import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Jordan
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Finset
open Formalism Formalism.CyclotomicNorms
namespace Formalism.CyclotomicNorms
theorem _root_.solution : BlocksCycle := by
  unfold BlocksCycle
  intro G Ω _ _ _ _ B m p g₀ hsize hdisj hcover hinv hp hlt hcyc hsupp
  have hpow : ∀ (i : ℕ) (y : Ω), ((MulAction.toPerm g₀ : Equiv.Perm Ω) ^ i) y = g₀ ^ i • y := by
    intro i
    induction i with
    | zero => intro y; simp
    | succ i ih => intro y; simp [pow_succ, mul_smul, ih]
  have hord : orderOf (MulAction.toPerm g₀ : Equiv.Perm Ω) = p := by
    rw [hcyc.orderOf, hsupp]
  have hfix : ∀ y : Ω, g₀ ^ p • y = y := by
    intro y
    have h1 := pow_orderOf_eq_one (MulAction.toPerm g₀ : Equiv.Perm Ω)
    rw [hord] at h1
    rw [← hpow]
    simp [h1]
  obtain ⟨φ, hφdef⟩ : ∃ φ : Finset Ω → Finset Ω, ∀ s, φ s = s.image (fun x => g₀ • x) :=
    ⟨fun s => s.image (fun x => g₀ • x), fun _ => rfl⟩
  have hφ : ∀ (i : ℕ) (s : Finset Ω), φ^[i] s = s.image (fun x => g₀ ^ i • x) := by
    intro i
    induction i with
    | zero => intro s; simp
    | succ i ih =>
      intro s
      rw [Function.iterate_succ_apply', ih, hφdef, Finset.image_image]
      congr 1
      funext y
      simp only [Function.comp_apply, pow_succ', mul_smul]
  have hφB : ∀ (i : ℕ), ∀ s ∈ B, φ^[i] s ∈ B := by
    intro i s hs
    rw [hφ]
    exact hinv (g₀ ^ i) s hs
  have hper : ∀ s : Finset Ω, φ^[p] s = s := by
    intro s
    rw [hφ]
    simp [hfix]
  have hp2 := hp.two_le
  obtain ⟨x, hx⟩ : (MulAction.toPerm g₀ : Equiv.Perm Ω).support.Nonempty := by
    rw [← Finset.card_pos, hsupp]
    omega
  obtain ⟨b, hbB, hxb⟩ := hcover x
  have hcard : Fintype.card Ω = B.card * m := by
    have hU : B.biUnion (fun c => c) = Finset.univ := by
      ext y
      simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
      obtain ⟨c, hc, hyc⟩ := hcover y
      exact ⟨c, hc, hyc⟩
    rw [← Finset.card_univ, ← hU, Finset.card_biUnion (fun c hc c' hc' hne => hdisj c hc c' hc' hne)]
    exact Finset.sum_const_nat hsize
  have hmp : Function.minimalPeriod φ b ∣ p :=
    Function.IsPeriodicPt.minimalPeriod_dvd (hper b)
  rcases (Nat.dvd_prime hp).1 hmp with h1 | hpp
  · left
    have hfixb : φ b = b := Function.minimalPeriod_eq_one_iff_isFixedPt.1 h1
    have hsub : (MulAction.toPerm g₀ : Equiv.Perm Ω).support ⊆ b := by
      intro y hy
      obtain ⟨i, hi⟩ := hcyc.exists_pow_eq (Equiv.Perm.mem_support.1 hx) (Equiv.Perm.mem_support.1 hy)
      have hib : φ^[i] b = b := Function.iterate_fixed hfixb i
      rw [← hi, hpow, ← hib, hφ]
      exact Finset.mem_image_of_mem _ hxb
    have hpm : p ≤ m := by
      rw [← hsupp, ← hsize b hbB]
      exact Finset.card_le_card hsub
    have hk1 : 1 ≤ B.card := Finset.card_pos.2 ⟨b, hbB⟩
    by_contra hne
    have hk2 : 2 ≤ B.card := by omega
    have h2 := Nat.mul_le_mul hk2 hpm
    linarith
  · right
    have hinj : Set.InjOn (fun n => φ^[n] b) (Finset.range p : Set ℕ) := by
      rw [Finset.coe_range, ← hpp]
      exact Function.iterate_injOn_Iio_minimalPeriod
    have hkp : p ≤ B.card := by
      have h1 : ((Finset.range p).image (fun n => φ^[n] b)) ⊆ B := by
        intro c hc
        obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hc
        exact hφB n b hbB
      have h2 := Finset.card_le_card h1
      rwa [Finset.card_image_of_injOn hinj, Finset.card_range] at h2
    have hm1 : 1 ≤ m := by
      rw [← hsize b hbB]
      exact Finset.card_pos.2 ⟨x, hxb⟩
    have hm : m = 1 := by
      by_contra hne
      have hm2 : 2 ≤ m := by omega
      have h3 := Nat.mul_le_mul hkp hm2
      linarith
    rw [hcard, hm, mul_one]
end Formalism.CyclotomicNorms
