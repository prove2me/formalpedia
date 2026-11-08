-- Prove2me | solution 1 for BlockchainTFM.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:52:53.738576+00:00
-- url     : https://prove2.me/submissions/8e0b6a85-7947-497c-8669-8bcc82875245

import Mathlib
import Definitions.Def_BlockchainTFM_Model
import Definitions.Def_BlockchainTFM_Decomposition
import Definitions.Def_BlockchainTFM_Mechanism3

open MeasureTheory

namespace Aux_BTFM_l2

lemma split3 {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    ∑ j, f j = ∑ j ∈ Finset.Iio i, f j + f i + ∑ j ∈ Finset.Ioi i, f j := by
  have hu : (Finset.univ : Finset (Fin n)) = Finset.Iio i ∪ ({i} ∪ Finset.Ioi i) := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_Iio, Finset.mem_singleton,
      Finset.mem_Ioi, true_iff]
    rcases lt_trichotomy j i with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  rw [hu, Finset.sum_union, Finset.sum_union, Finset.sum_singleton]
  · ring
  · rw [Finset.disjoint_left]; intro j h1 h2
    simp only [Finset.mem_singleton, Finset.mem_Ioi] at h1 h2
    rw [h1] at h2; exact lt_irrefl _ h2
  · rw [Finset.disjoint_left]; intro j h1 h2
    simp only [Finset.mem_Iio, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ioi] at h1 h2
    rcases h2 with h2 | h2
    · rw [h2] at h1; exact lt_irrefl _ h1
    · exact lt_asymm h1 h2

lemma pairsum {n : ℕ} (a : Fin n → ℝ) :
    ∑ i, ∑ j ∈ Finset.Ioi i, a i * a j = ((∑ i, a i) ^ 2 - ∑ i, a i ^ 2) / 2 := by
  have h1 : (∑ i, a i) ^ 2 = ∑ i, ∑ j, a i * a j := by rw [sq, Finset.sum_mul_sum]
  have h2 : ∑ i, ∑ j, a i * a j = ∑ i, ∑ j ∈ Finset.Iio i, a i * a j + ∑ i, a i ^ 2
      + ∑ i, ∑ j ∈ Finset.Ioi i, a i * a j := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [split3 (fun j => a i * a j) i, sq]
  have h3 : ∑ i, ∑ j ∈ Finset.Iio i, a i * a j = ∑ i, ∑ j ∈ Finset.Ioi i, a i * a j := by
    rw [Finset.sum_comm' (s' := fun j => Finset.Ioi j) (t' := Finset.univ)]
    · apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro i _; ring
    · intro x y
      simp only [Finset.mem_univ, Finset.mem_Iio, Finset.mem_Ioi, true_and, and_true]
  rw [h1, h2, h3]
  ring

end Aux_BTFM_l2

open BlockchainTFM Aux_BTFM_l2 in
theorem solution {n : ℕ} (hn : 2 ≤ n) (V₀ : Measure ℝ) [IsProbabilityMeasure V₀]
    (hV₀ : V₀ (Set.Icc 0 1) = 1) (hc : 0 < crho V₀) (h : ℝ) (hh : 0 ≤ h) :
    IsAdmissible V₀ (theta (n := n) h (crho V₀)) (minerRev h (crho V₀)) := by
  set c := crho V₀ with hcdef
  refine ⟨fun i b _ => ?_, fun i x _ => ?_⟩
  · -- algebraic identity
    set a : Fin n → ℝ := fun j => b j ^ 2 with ha
    have hupd : ∀ j, (Function.update b i 0 j) ^ 2 = if j = i then 0 else a j := by
      intro j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj, hj, ha]
    have hs1 : ∑ j, (Function.update b i 0 j) ^ 2 = ∑ j, a j - a i := by
      simp only [hupd]
      have : ∀ j, (if j = i then (0 : ℝ) else a j) = a j - if j = i then a j else 0 := by
        intro j; split_ifs <;> simp
      simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hs2 : ∑ j, ((Function.update b i 0 j) ^ 2) ^ 2 = ∑ j, a j ^ 2 - a i ^ 2 := by
      simp only [hupd]
      have : ∀ j, (if j = i then (0 : ℝ) else a j) ^ 2 = a j ^ 2 - if j = i then a j ^ 2 else 0 := by
        intro j; split_ifs <;> simp
      simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hP : ∀ v : Fin n → ℝ, ∑ i, ∑ j ∈ Finset.Ioi i, v i ^ 2 * v j ^ 2
        = ((∑ i, v i ^ 2) ^ 2 - ∑ i, (v i ^ 2) ^ 2) / 2 := fun v => pairsum (fun j => v j ^ 2)
    have hSi : ∑ j ∈ Finset.univ.erase i, b j ^ 2 = ∑ j, a j - a i := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      simp [ha]
    unfold minerRev theta
    rw [hP b, hP (Function.update b i 0), hs1, hs2, hSi]
    simp only [ha]
    ring
  · -- integrability and zero mean
    haveI : ∀ _ : Fin n, IsProbabilityMeasure V₀ := fun _ => inferInstance
    have hae : ∀ᵐ t ∂V₀, t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [ae_iff]
      have : V₀ (Set.Icc (0 : ℝ) 1)ᶜ = 0 := (prob_compl_eq_zero_iff measurableSet_Icc).2 hV₀
      exact measure_mono_null (fun t ht => ht) this
    have hsq : Integrable (fun t : ℝ => t ^ 2) V₀ := by
      apply Integrable.of_mem_Icc 0 1 (by fun_prop)
      filter_upwards [hae] with t ht
      exact ⟨sq_nonneg t, by nlinarith [ht.1, ht.2]⟩
    have hint : ∀ j : Fin n, Integrable (fun b : Fin n → ℝ => b j ^ 2) (Measure.pi fun _ => V₀) :=
      fun j => integrable_comp_eval (μ := fun _ : Fin n => V₀) (i := j) (f := fun t : ℝ => t ^ 2) hsq
    have hval : ∀ j : Fin n, ∫ b, b j ^ 2 ∂(Measure.pi fun _ : Fin n => V₀) = c := by
      intro j
      rw [integral_comp_eval (μ := fun _ : Fin n => V₀) (i := j) (f := fun t : ℝ => t ^ 2) (by fun_prop)]
      rfl
    have hfun : (fun b : Fin n → ℝ => theta h c (Function.update b i x) i)
        = fun b => (-(1 / 2) * h * x ^ 2 / (c * ((n : ℝ) - 1))) *
            ∑ j ∈ Finset.univ.erase i, b j ^ 2 + (1 / 2) * h * x ^ 2 := by
      funext b
      unfold theta
      rw [Function.update_self]
      have : ∑ j ∈ Finset.univ.erase i, (Function.update b i x j) ^ 2
          = ∑ j ∈ Finset.univ.erase i, b j ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [this]
      ring
    have hI : Integrable (fun b : Fin n → ℝ => ∑ j ∈ Finset.univ.erase i, b j ^ 2)
        (Measure.pi fun _ => V₀) := integrable_finsetSum _ (fun j _ => hint j)
    rw [hfun]
    refine ⟨(hI.const_mul _).add (integrable_const _), ?_⟩
    rw [integral_add (hI.const_mul _) (integrable_const _), integral_const_mul,
      integral_finsetSum _ (fun j _ => hint j), integral_const, probReal_univ, one_smul]
    rw [Finset.sum_congr rfl (fun j _ => hval j), Finset.sum_const, Finset.card_erase_of_mem
      (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    have hc0 := hc.ne'
    have hn0 := hn1.ne'
    have key : (-(1 / 2) * h * x ^ 2 / (c * ((n : ℝ) - 1))) * (((n : ℝ) - 1) * c)
        = -(1 / 2) * h * x ^ 2 := by
      field_simp
    linarith
