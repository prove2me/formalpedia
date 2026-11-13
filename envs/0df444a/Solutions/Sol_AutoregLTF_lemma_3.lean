-- Prove2me | solution 1 for AutoregLTF.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:28:00.588886+00:00
-- url     : https://prove2.me/submissions/248fb4d1-0dee-4a83-9135-b65d46e4ac77

import Mathlib
import Definitions.Def_QAlgorithms_Defs_PACSampleComplexity
import Definitions.Def_AutoregLTF_prompt
import Theorems.Thm_AutoregLTF_lemma_2
import Theorems.Thm_AutoregLTF_eq_44

section
set_option autoImplicit false
namespace AutoregLTF.Dev.Lemma3
open AutoregLTF

lemma geom_Icc (m : ℕ) : ∑ j ∈ Finset.Icc 1 m, (2 : ℤ) ^ (j - 1) = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp [pow_succ]
    ring

lemma enc_bound (m : ℕ) (lab : ℕ → ℕ → Bool) (j : ℕ) :
    0 ≤ enc m lab j ∧ enc m lab j ≤ 2 ^ m - 1 := by
  unfold enc
  constructor
  · exact Finset.sum_nonneg (fun k _ => by positivity)
  · rw [← geom_Icc m]
    refine Finset.sum_le_sum (fun k _ => ?_)
    have : ((lab j k).toNat : ℤ) ≤ 1 := by cases lab j k <;> simp
    have h2 : (0 : ℤ) < 2 ^ (k - 1) := by positivity
    nlinarith

lemma realize (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : p m + 1 ≤ d) (T : ℕ)
    (hT : (m + 3) * p m ≤ T) (lab : ℕ → ℕ → Bool) :
    ∃ w : Fin d → ℚ, ∀ i ∈ Finset.Icc 1 m, ∀ s ∈ Finset.Icc 1 m,
      ltf d T w (prompt m d T i s) = lab i s := by
  obtain ⟨B, hB, a, ha⟩ := lemma_2 m hm (enc m lab) (fun j _ => enc_bound m lab j)
  refine ⟨wOf d (p m) B a, fun i hi s hs => ?_⟩
  obtain ⟨h1, h2, h3⟩ := eq_44 m hm lab d hd T hT B hB a ha i hi s hs
  exact h1.trans (h2.trans h3)

end AutoregLTF.Dev.Lemma3

namespace AutoregLTF
open AutoregLTF.Dev.Lemma3 in
theorem chk_lemma_3 (m : ℕ) (hm : 2 ≤ m) (d : ℕ) (hd : p m + 1 ≤ d) (T : ℕ)
    (hT : (m + 3) * p m ≤ T) :
    (∀ i ∈ Finset.Icc 1 m, ∀ s ∈ Finset.Icc 1 m, ∀ i' ∈ Finset.Icc 1 m, ∀ s' ∈ Finset.Icc 1 m,
      prompt m d T i s = prompt m d T i' s' → i = i' ∧ s = s') ∧
    QAlgorithms.Learning.ShattersSet (cls d T)
      ((Finset.Icc 1 m ×ˢ Finset.Icc 1 m).image (fun q => prompt m d T q.1 q.2)) := by
  constructor
  · intro i hi s hs i' hi' s' hs' h
    by_contra hne
    obtain ⟨w, hw⟩ := realize m hm d hd T hT (fun a b => decide (a = i' ∧ b = s'))
    have e1 := hw i hi s hs
    have e2 := hw i' hi' s' hs'
    rw [h] at e1
    rw [e1] at e2
    have : ¬ (i = i' ∧ s = s') := hne
    simp [this] at e2
  · have hmem : ∀ x : Fin d → Bool, x ∈ (Finset.Icc 1 m ×ˢ Finset.Icc 1 m).image
        (fun q => prompt m d T q.1 q.2) ↔
        ∃ i ∈ Finset.Icc 1 m, ∃ s ∈ Finset.Icc 1 m, prompt m d T i s = x := by
      intro x
      simp only [Finset.mem_image, Finset.mem_product, Prod.exists]
      constructor
      · rintro ⟨i, s, ⟨h1, h2⟩, h3⟩; exact ⟨i, h1, s, h2, h3⟩
      · rintro ⟨i, h1, s, h2, h3⟩; exact ⟨i, s, ⟨h1, h2⟩, h3⟩
    generalize (Finset.Icc 1 m ×ˢ Finset.Icc 1 m).image (fun q => prompt m d T q.1 q.2) = S at hmem ⊢
    intro y
    let y' : (Fin d → Bool) → Bool := fun x =>
      @dite _ (x ∈ S) (Classical.propDecidable _) (fun h => y ⟨x, h⟩) (fun _ => false)
    obtain ⟨w, hw⟩ := realize m hm d hd T hT (fun a b => y' (prompt m d T a b))
    refine ⟨ltf d T w, ⟨w, rfl⟩, fun x => ?_⟩
    obtain ⟨x, hx⟩ := x
    obtain ⟨i, hi, s, hs, rfl⟩ := (hmem x).mp hx
    rw [hw i hi s hs]
    simp only [y']
    rw [dif_pos hx]
end AutoregLTF
end

theorem solution : type_of% @AutoregLTF.chk_lemma_3 := @AutoregLTF.chk_lemma_3
