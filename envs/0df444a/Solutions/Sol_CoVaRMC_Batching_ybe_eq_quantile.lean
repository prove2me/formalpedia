-- Prove2me | solution 1 for CoVaRMC.Batching.ybe_eq_quantile
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T22:23:58.612401+00:00
-- url     : https://prove2.me/submissions/8234501a-7627-4ed0-9ca6-015997c7e021

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaRYBEAux

/-- For a tuple `w` and its sorted rearrangement, at least `j + 1` entries are `≤ y`
iff the `j`-th smallest entry is `≤ y`. -/
lemma card_le_iff {k : ℕ} (w : Fin k → ℝ) (j : Fin k) (y : ℝ) :
    (j : ℕ) + 1 ≤ (Finset.univ.filter fun i => w i ≤ y).card ↔ w (Tuple.sort w j) ≤ y := by
  set σ := Tuple.sort w
  have hmono : Monotone (w ∘ σ) := Tuple.monotone_sort w
  constructor
  · intro hcard
    by_contra hlt
    push Not at hlt
    have hsub : (Finset.univ.filter fun i => w i ≤ y) ⊆ (Finset.Iio j).image σ := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [Finset.mem_image]
      refine ⟨σ.symm i, ?_, by simp⟩
      rw [Finset.mem_Iio]
      by_contra hge
      push Not at hge
      have := hmono hge
      simp only [Function.comp, Equiv.apply_symm_apply] at this
      linarith
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ σ.injective, Fin.card_Iio] at this
    omega
  · intro hj
    have hsub : (Finset.Iic j).image σ ⊆ (Finset.univ.filter fun i => w i ≤ y) := by
      intro i hi
      rw [Finset.mem_image] at hi
      obtain ⟨l, hl, rfl⟩ := hi
      rw [Finset.mem_Iic] at hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hmono hl).trans hj
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ σ.injective, Fin.card_Iic] at this
    omega

end CoVaRYBEAux

open CoVaRMC.Batching in
theorem solution {Ω : Type*} (S : ℕ × ℕ → Ω → ℝ × ℝ) (α β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (k m : ℕ) (hk : 0 < k) (ω : Ω) :
    YBE S α β k m ω = sInf {y : ℝ | β ≤ FkHat S α k m y ω} := by
  set w : Fin k → ℝ := fun i => Yhat S α m i ω with hw
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : 0 < ⌈β * k⌉₊ := Nat.ceil_pos.mpr (mul_pos hβ.1 hkR)
  have hle : ⌈β * k⌉₊ ≤ k := Nat.ceil_le.mpr (by nlinarith [hβ.2])
  have hr : ((rankIdx β k hk : Fin k) : ℕ) = ⌈β * k⌉₊ - 1 := by
    simp only [rankIdx]; omega
  have hset : {y : ℝ | β ≤ FkHat S α k m y ω} =
      Set.Ici (w (Tuple.sort w (rankIdx β k hk))) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_Ici, FkHat, empCDF]
    rw [← CoVaRYBEAux.card_le_iff w (rankIdx β k hk) y, hr]
    rw [show β ≤ (k : ℝ)⁻¹ * ((Finset.univ.filter fun i => w i ≤ y).card : ℝ) ↔
        β * k ≤ ((Finset.univ.filter fun i => w i ≤ y).card : ℝ) by
      rw [inv_mul_eq_div, le_div_iff₀ hkR]]
    rw [← Nat.ceil_le]
    omega
  rw [hset, csInf_Ici]
  simp only [YBE, dif_pos hk, ImpactInvesting.Portfolio.orderStat]
  rfl
