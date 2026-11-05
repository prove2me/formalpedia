-- Prove2me | solution 1 for FVRPricing.DecayBalancing.lemma_10_scale_invariance
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T22:40:31.470423+00:00
-- url     : https://prove2.me/submissions/78f26ca0-4596-4b78-b82d-fa2b7940d262

import Mathlib
import Definitions.Def_FVRPricing_DecayBalancing_Policies

open MeasureTheory ProbabilityTheory FVRPricing.DecayBalancing

lemma fvr10_expDensity_eq (r : ℝ) (hr : 0 < r) (s : ℝ) :
    expDensity r s = r⁻¹ * expDensity 1 (r⁻¹ * s) := by
  unfold expDensity
  have h : (0 ≤ r⁻¹ * s ↔ 0 ≤ s) := by
    constructor
    · intro h; exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hr)).mp h
    · intro h; exact mul_nonneg (inv_pos.mpr hr).le h
  by_cases hs : 0 ≤ s
  · rw [if_pos hs, if_pos (h.mpr hs)]
    congr 2
    field_simp
  · rw [if_neg hs, if_neg (fun h' => hs (h.mp h'))]
    simp

lemma fvr10_Fbar_eq (r : ℝ) (hr : 0 < r) (p : ℝ) :
    Fbar (expDensity r) p = Fbar (expDensity 1) ((1 / r) * p) := by
  unfold Fbar
  have : (fun s => expDensity r s) = fun s => r⁻¹ * expDensity 1 (r⁻¹ * s) := by
    funext s; exact fvr10_expDensity_eq r hr s
  rw [this, integral_const_mul, integral_comp_mul_left_Ioi (fun t => expDensity 1 t) p
    (inv_pos.mpr hr), smul_eq_mul, ← mul_assoc, inv_inv, inv_mul_cancel₀ hr.ne', one_mul,
    one_div]

lemma fvr10_pathRevenue (r α : ℝ) (hr : 0 < r) (π : ℕ → ℝ → ℝ → ℝ) (x : ℕ) (a b lam : ℝ)
    (e : Fin x → ℝ) :
    pathRevenue (expDensity r) α π π x a b lam e =
      ENNReal.ofReal r * pathRevenue (expDensity 1) α (fun x a b => (1 / r) * π x a b)
        (fun x a b => (1 / r) * π x a b) x a b lam e := by
  have hsd : ∀ k, saleTime (expDensity r) π x a b lam e k =
      saleTime (expDensity 1) (fun x a b => (1 / r) * π x a b) x a b lam e k := by
    intro k
    unfold saleTime stageDuration
    simp_rw [fvr10_Fbar_eq r hr]
  unfold pathRevenue
  split_ifs with hl
  · simp
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hsd, mul_left_comm, ← ENNReal.ofReal_mul hr.le]
    congr 3
    field_simp

lemma fvr10_Jpi (r α : ℝ) (hr : 0 < r) (π : ℕ → ℝ → ℝ → ℝ) (x : ℕ) (a b : ℝ) :
    Jpi (expDensity r) α π x a b =
      ENNReal.ofReal r * Jpi (expDensity 1) α (fun x a b => (1 / r) * π x a b) x a b := by
  unfold Jpi
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr (fun lam => ?_)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr (fun e => ?_)
  exact fvr10_pathRevenue r α hr π x a b lam e

theorem solution (π : ℕ → ℝ → ℝ → ℝ) (hπ : IsPolicy π)
    (α r : ℝ) (hα : 0 < α) (hr : 0 < r) (x : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Jpi (expDensity r) α π x a b =
      ENNReal.ofReal r * Jpi (expDensity 1) α (fun x a b => (1 / r) * π x a b) x a b ∧
    Jstar (expDensity r) α x a b = ENNReal.ofReal r * Jstar (expDensity 1) α x a b := by
  refine ⟨fvr10_Jpi r α hr π x a b, ?_⟩
  unfold Jstar
  have key : (⨆ (π : ℕ → ℝ → ℝ → ℝ) (_ : IsPolicy π),
      Jpi (expDensity 1) α (fun x a b => (1 / r) * π x a b) x a b) =
      ⨆ (π : ℕ → ℝ → ℝ → ℝ) (_ : IsPolicy π), Jpi (expDensity 1) α π x a b := by
    apply le_antisymm
    · refine iSup₂_le (fun σ hσ => ?_)
      have hσ' : IsPolicy (fun x a b => (1 / r) * σ x a b) := by
        refine ⟨fun n => ((hσ.1 n).const_mul _), fun n a b => ?_⟩
        exact mul_nonneg (by positivity) (hσ.2 n a b)
      exact le_iSup₂ (f := fun (π : ℕ → ℝ → ℝ → ℝ) (_ : IsPolicy π) =>
        Jpi (expDensity 1) α π x a b) _ hσ'
    · refine iSup₂_le (fun σ hσ => ?_)
      have hσ' : IsPolicy (fun x a b => r * σ x a b) := by
        refine ⟨fun n => ((hσ.1 n).const_mul _), fun n a b => ?_⟩
        exact mul_nonneg hr.le (hσ.2 n a b)
      have := le_iSup₂ (f := fun (π : ℕ → ℝ → ℝ → ℝ) (_ : IsPolicy π) =>
        Jpi (expDensity 1) α (fun x a b => (1 / r) * π x a b) x a b) _ hσ'
      have heq : (fun x a b => (1 / r) * (r * σ x a b)) = σ := by
        funext x a b; field_simp
      rw [heq] at this
      exact this
  rw [← key, ENNReal.mul_iSup]
  refine iSup_congr (fun σ => ?_)
  rw [ENNReal.mul_iSup]
  exact iSup_congr (fun _ => fvr10_Jpi r α hr σ x a b)
