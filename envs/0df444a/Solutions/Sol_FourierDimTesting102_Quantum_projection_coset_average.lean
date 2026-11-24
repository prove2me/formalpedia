-- Prove2me | solution 1 for FourierDimTesting102.Quantum.projection_coset_average
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T13:17:35.406491+00:00
-- url     : https://prove2.me/submissions/f68c4235-8755-46a7-bd4f-cb2ce13dae9e

import Definitions.Def_FourierDimTesting102_Quantum_Model

namespace FourierDimTesting102.Quantum

open QAlgorithms

open Classical in
theorem pc_sum_chi {n : ℕ} (U : Submodule (ZMod 2) (V n)) (z : V n) :
    ∑ s ∈ Finset.univ.filter (fun s => s ∈ U), chi s z
      = if z ∈ perp U then ((Finset.univ.filter (fun s => s ∈ U)).card : ℝ) else 0 := by
  have hchi : ∀ s : V n, (s ⬝ᵥ z = 0 → chi s z = 1) ∧ (s ⬝ᵥ z ≠ 0 → chi s z = -1) := by
    intro s
    have h1 : (1 : ZMod 2).val = 1 := rfl
    constructor
    · intro h; simp [chi, h]
    · intro h
      have : s ⬝ᵥ z = 1 := by
        rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) (s ⬝ᵥ z) with h' | h'
        · exact absurd h' h
        · exact h'
      simp [chi, this, h1]
  by_cases hz : z ∈ perp U
  · rw [if_pos hz]
    rw [Finset.sum_congr rfl (g := fun _ => (1:ℝ))]
    · simp
    · intro s hs
      have hsU : s ∈ U := by simpa using hs
      exact (hchi s).1 (hz s hsU)
  · rw [if_neg hz]
    have : ∃ s0 ∈ U, s0 ⬝ᵥ z ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hz (fun u hu => hcon u hu)
    obtain ⟨s0, hs0, hne⟩ := this
    have hs0chi : chi s0 z = -1 := (hchi s0).2 hne
    have hshift : ∑ s ∈ Finset.univ.filter (fun s => s ∈ U), chi (s0 + s) z
        = ∑ s ∈ Finset.univ.filter (fun s => s ∈ U), chi s z := by
      refine Finset.sum_equiv (Equiv.addLeft s0) ?_ ?_
      · intro s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_addLeft]
        exact ⟨fun h => U.add_mem hs0 h, fun h => by simpa using U.sub_mem h hs0⟩
      · intro s _; rfl
    have hneg : ∑ s ∈ Finset.univ.filter (fun s => s ∈ U), chi (s0 + s) z
        = -∑ s ∈ Finset.univ.filter (fun s => s ∈ U), chi s z := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [chi_add_left, hs0chi]; ring
    exact self_eq_neg.mp (hshift.symm.trans hneg)

open Classical in
theorem pc_card {n : ℕ} (U : Submodule (ZMod 2) (V n)) :
    ((Finset.univ.filter (fun s => s ∈ U)).card : ℝ) *
      ((Finset.univ.filter (fun h => h ∈ perp U)).card : ℝ) = 2 ^ n := by
  have h1 : ∑ z : V n, ∑ s ∈ Finset.univ.filter (fun s => s ∈ U), chi s z
      = ((Finset.univ.filter (fun s => s ∈ U)).card : ℝ) *
        ((Finset.univ.filter (fun h => h ∈ perp U)).card : ℝ) := by
    simp_rw [pc_sum_chi]
    rw [← Finset.sum_filter]
    simp [mul_comm]
  have h2 : ∑ z : V n, ∑ s ∈ Finset.univ.filter (fun s => s ∈ U), chi s z = 2 ^ n := by
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single (0 : V n)]
    · simp [chi]
    · intro s _ hs; exact sum_chi_eq_zero hs
    · intro h; exact absurd (by simp) h
  rw [← h1, h2]

open Classical in
theorem projection_coset_average_aux {n : ℕ} (U : Submodule (ZMod 2) (V n)) (f : BoolFn n)
    (x : V n) : proj U f x = cosetAverage U f x := by
  have hc := pc_card U
  have hpos : ((Finset.univ.filter (fun h => h ∈ perp U)).card : ℝ) ≠ 0 := by
    intro h; rw [h, mul_zero] at hc; exact (pow_ne_zero n (by norm_num : (2:ℝ) ≠ 0)) hc.symm
  have step0 : proj U f x = ((2:ℝ) ^ n)⁻¹ * ∑ y : V n, toSign f y *
      ∑ s ∈ Finset.univ.filter (fun s => s ∈ U), chi s (x + y) := by
    have e : ∀ s : V n, coeff f s * chi s x
        = ((2:ℝ) ^ n)⁻¹ * ∑ y : V n, toSign f y * (chi s (x + y)) := by
      intro s
      simp only [coeff, boolFourier, Finset.sum_mul, Finset.mul_sum, chi_add_right]
      refine Finset.sum_congr rfl fun y _ => ?_
      show _ = _
      simp only [chi]
      ring
    simp only [proj, e, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  have step1 : proj U f x = ((2:ℝ) ^ n)⁻¹ * ∑ y : V n, toSign f y *
      (if x + y ∈ perp U then ((Finset.univ.filter (fun s => s ∈ U)).card : ℝ) else 0) := by
    rw [step0]; simp_rw [pc_sum_chi]
  rw [step1, cosetAverage]
  have hre : ∑ y : V n, toSign f y *
      (if x + y ∈ perp U then ((Finset.univ.filter (fun s => s ∈ U)).card : ℝ) else 0)
      = ((Finset.univ.filter (fun s => s ∈ U)).card : ℝ) *
        ∑ h ∈ Finset.univ.filter (fun h => h ∈ perp U), toSign f (x + h) := by
    rw [← Equiv.sum_comp (Equiv.addLeft x)]
    have hxx : ∀ h : V n, x + (x + h) = h := by
      intro h; ext i
      simp only [Pi.add_apply]
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    simp only [Equiv.coe_addLeft, hxx]
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs <;> ring
  rw [hre, ← hc]
  have h2 : ((Finset.univ.filter (fun s => s ∈ U)).card : ℝ) ≠ 0 := by
    intro h; rw [h, zero_mul] at hc; exact (pow_ne_zero n (by norm_num : (2:ℝ) ≠ 0)) hc.symm
  field_simp

end FourierDimTesting102.Quantum

theorem solution {n : ℕ} (U : Submodule (ZMod 2) (FourierDimTesting102.Quantum.V n))
    (f : FourierDimTesting102.Quantum.BoolFn n) (x : FourierDimTesting102.Quantum.V n) :
    FourierDimTesting102.Quantum.proj U f x = FourierDimTesting102.Quantum.cosetAverage U f x :=
  FourierDimTesting102.Quantum.projection_coset_average_aux U f x
