-- Prove2me | solution 1 for AutoregLTF.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:28:01.299241+00:00
-- url     : https://prove2.me/submissions/8fcce053-456f-41ee-b29d-f71acf3b1604

import Mathlib
import Definitions.Def_QAlgorithms_Defs_PACSampleComplexity
import Definitions.Def_AutoregLTF_ltf
import Theorems.Thm_AutoregLTF_lemma_3
import Theorems.Thm_AutoregLTF_theorem_1_counting
import Theorems.Thm_AutoregLTF_eq_46

section
set_option autoImplicit false
namespace AutoregLTF.Dev.Theorem1
open AutoregLTF

lemma card_le_vc (d T m : ℕ) (hm : 2 ≤ m) (hd : p m + 1 ≤ d) (hT : (m + 3) * p m ≤ T) :
    ((m ^ 2 : ℕ) : ℕ∞) ≤ QAlgorithms.Learning.vcDimSet (cls d T) := by
  obtain ⟨hinj, hsh⟩ := lemma_3 m hm d hd T hT
  have hcard : ((Finset.Icc 1 m ×ˢ Finset.Icc 1 m).image
      (fun q => prompt m d T q.1 q.2)).card = m ^ 2 := by
    rw [Finset.card_image_of_injOn, Finset.card_product]
    · simp [sq]
    · rintro ⟨i, s⟩ hq ⟨i', s'⟩ hq' h
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hq hq'
      have := hinj i hq.1 s hq.2 i' hq'.1 s' hq'.2 h
      simp [this.1, this.2]
  unfold QAlgorithms.Learning.vcDimSet
  rw [← hcard]
  exact le_iSup₂ (f := fun (s : Finset (Fin d → Bool)) (_ : QAlgorithms.Learning.ShattersSet (cls d T) s) =>
    (s.card : ℕ∞)) _ hsh

end AutoregLTF.Dev.Theorem1

namespace AutoregLTF
open AutoregLTF.Dev.Theorem1 in
theorem chk_theorem_1 (d T : ℕ) (hd : 1 ≤ d) (hT : d ^ 2 ≤ T) :
    ((d ^ 2 : ℕ) : ℕ∞) ≤ 3024 ^ 2 * QAlgorithms.Learning.vcDimSet (cls d T) := by
  obtain ⟨h2, h1, h3, h4⟩ := theorem_1_counting d T hd hT
  set m := max 1 ((d - 1) / 378 - 2) with hmdef
  have hm1 : 1 ≤ m := le_max_left _ _
  have hvc : ((m ^ 2 : ℕ) : ℕ∞) ≤ QAlgorithms.Learning.vcDimSet (cls d T) := by
    by_cases hm : 2 ≤ m
    · obtain ⟨a1, a2, a3⟩ := h2 hm
      have hdp : p m + 1 ≤ d := by omega
      have hTp : (m + 3) * p m ≤ T := by
        have : d ^ 2 ≤ T := hT
        omega
      exact card_le_vc d T m hm hdp hTp
    · have : m = 1 := by omega
      have e := (eq_46 d T hd (by nlinarith)).2.2
      rw [this]
      simpa using e
  calc ((d ^ 2 : ℕ) : ℕ∞) ≤ ((3024 ^ 2 * m ^ 2 : ℕ) : ℕ∞) := by
        exact_mod_cast (by nlinarith [h4] : d ^ 2 ≤ 3024 ^ 2 * m ^ 2)
    _ = 3024 ^ 2 * ((m ^ 2 : ℕ) : ℕ∞) := by push_cast; ring
    _ ≤ 3024 ^ 2 * QAlgorithms.Learning.vcDimSet (cls d T) := by gcongr
end AutoregLTF
end

theorem solution : type_of% @AutoregLTF.chk_theorem_1 := @AutoregLTF.chk_theorem_1
