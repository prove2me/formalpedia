-- Prove2me | solution 1 for FourierDimTesting102.Quantum.Supplement.fourier_support_iff_periodic
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:50:58.188951+00:00
-- url     : https://prove2.me/submissions/4d33eca6-3d68-4a53-8e2f-eb9b80b92b87

import Mathlib
import Definitions.Def_FourierDimTesting102_Quantum_Model

open QAlgorithms FourierDimTesting102.Quantum

lemma fdt_coeff_eq {n : ℕ} (f : BoolFn n) (s : V n) :
    coeff f s = ((2 : ℝ) ^ n)⁻¹ * ∑ y : V n, toSign f y * chi s y := by
  simp [coeff, boolFourier, chi]

lemma fdt_sum_chi {n : ℕ} (t : V n) :
    ∑ s : V n, chi t s = if t = 0 then (2 : ℝ) ^ n else 0 := by
  split_ifs with ht
  · subst ht; simp [chi, Fintype.card_fun, ZMod.card]
  · exact sum_chi_eq_zero ht

lemma fdt_add_eq_zero {n : ℕ} (y x : V n) : y + x = 0 ↔ y = x := by
  constructor
  · intro h; funext i
    have := congrFun h i
    simp at this
    have h2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact h2 _ _ this
  · intro h; subst h; funext i
    have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
    exact h2 (y i)

lemma fdt_inversion {n : ℕ} (f : BoolFn n) (x : V n) :
    toSign f x = ∑ s : V n, coeff f s * chi s x := by
  simp_rw [fdt_coeff_eq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ y : V n, ∑ s : V n, ((2 : ℝ) ^ n)⁻¹ * (toSign f y * chi s y) * chi s x
      = ((2 : ℝ) ^ n)⁻¹ * toSign f y * (if y + x = 0 then (2 : ℝ) ^ n else 0) := by
    intro y
    rw [← fdt_sum_chi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [chi_comm (y + x) s, chi_add_right]; ring
  simp_rw [this, fdt_add_eq_zero]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp

lemma signOf_inj {a b : Bool} (h : signOf a = signOf b) : a = b := by
  cases a <;> cases b <;> simp [signOf] at h ⊢ <;> norm_num at h

theorem solution {n : ℕ} (U : Submodule (ZMod 2) (V n)) (f : BoolFn n) :
    f ∈ CU U ↔ ∀ h ∈ perp U, ∀ x : V n, f (x + h) = f x := by
  constructor
  · intro hf h hh x
    apply signOf_inj
    show toSign f (x + h) = toSign f x
    rw [fdt_inversion f (x + h), fdt_inversion f x]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : coeff f s = 0
    · simp [hs]
    · have hsU : s ∈ U := hf hs
      have hsh : s ⬝ᵥ h = 0 := hh s hsU
      rw [chi_add_right]
      have : chi s h = 1 := by simp [chi, hsh]
      rw [this, mul_one]
  · intro hper s hs
    by_contra hsU
    obtain ⟨φ, hφs, hφU⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hsU inferInstance
    let h : V n := fun i => φ (fun j => if i = j then 1 else 0)
    have hφ : ∀ v : V n, φ v = v ⬝ᵥ h := by
      intro v
      rw [LinearMap.pi_apply_eq_sum_univ φ v]
      simp [dotProduct, h, smul_eq_mul]
    have hh : h ∈ perp U := by
      intro u hu
      rw [← hφ]
      have : φ u ∈ U.map φ := Submodule.mem_map_of_mem hu
      rw [hφU] at this
      simpa using this
    have hsh : s ⬝ᵥ h = 1 := by
      rw [← hφ]
      have h2 : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
      exact h2 _ hφs
    have hchi : chi s h = -1 := by
      rw [chi, hsh]; simp [ZMod.val_one]
    apply hs
    rw [fdt_coeff_eq]
    have hshift : ∑ y : V n, toSign f (y + h) * chi s (y + h) = ∑ y : V n, toSign f y * chi s y :=
      Equiv.sum_comp (Equiv.addRight h) (fun y => toSign f y * chi s y)
    have hneg : ∑ y : V n, toSign f (y + h) * chi s (y + h) = -∑ y : V n, toSign f y * chi s y := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [chi_add_right, hchi]
      simp only [toSign, hper h hh y]
      ring
    have : ∑ y : V n, toSign f y * chi s y = 0 := by linarith
    rw [this, mul_zero]
