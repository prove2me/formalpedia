-- Prove2me | solution 1 for Freiman.lower_bridge_word_states
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:24:23.725111+00:00
-- url     : https://prove2.me/submissions/930ee0f2-e2c1-4c56-8d1e-6a043f270d89

import Theorems.Thm_Freiman_lower_initial_family_normalization
import Theorems.Thm_Freiman_lower_parameter_extension
import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib
noncomputable section
open Freiman
namespace OtherBridgeWords
private abbrev badWord : List ℕ+ := [3,1,3,1,3]
private abbrev NoBad (w : List ℕ+) : Prop := ¬ badWord.IsInfix w
private theorem period_noBad (t : List ℕ+) : NoBad (lowerPeriod++t) ↔ NoBad t := by
  simp [NoBad, badWord, lowerPeriod, List.infix_cons_iff]
private theorem stemA_noBad (t : List ℕ+) : NoBad ([3,2,1,1]++t) ↔ NoBad t := by
  simp [NoBad, badWord, List.infix_cons_iff]
private theorem stemB_noBad (t : List ℕ+) : NoBad ([4,3,2,2]++t) ↔ NoBad t := by
  simp [NoBad, badWord, List.infix_cons_iff]
private theorem repeat_succ (n : ℕ) :
    lowerRepeat lowerPeriod (n+1) = lowerPeriod ++ lowerRepeat lowerPeriod n := by
  simp [lowerRepeat, List.replicate_succ]
private theorem repeat_noBad (n : ℕ) (t : List ℕ+) (ht : NoBad t) :
    NoBad (lowerRepeat lowerPeriod n ++ t) := by
  induction n with
  | zero => simpa [lowerRepeat] using ht
  | succ n ih => rw [repeat_succ, List.append_assoc, period_noBad]; exact ih
private theorem reverse_noBad (u : List ℕ+) (hu : NoBad u) : NoBad u.reverse := by
  intro hh
  have hr : badWord.reverse.IsInfix u.reverse := by simpa [badWord] using hh
  exact hu (List.reverse_infix.mp hr)
private theorem separator_noBad (u v : List ℕ+) (hu : NoBad u) (hv : NoBad v) :
    NoBad (u++[4]++v) := by
  intro hh
  have hh' : badWord.IsInfix (u++(4::v)) := by simpa [List.append_assoc] using hh
  rcases List.infix_append_iff_ne_nil.mp hh' with hx | hx | ⟨a,b,ha,hb,heq,hs,hp⟩
  · exact hu hx
  · have hx' : badWord.IsInfix v := by simpa [badWord, List.infix_cons_iff] using hx
    exact hv hx'
  · cases b with
    | nil => exact hb rfl
    | cons x xs =>
      have hx : x = 4 := (List.cons_prefix_cons.mp hp).1
      subst x
      have hfour : (4:ℕ+) ∈ badWord := by rw [heq]; simp
      norm_num [badWord] at hfour
end OtherBridgeWords


namespace OtherBridgeWords
private abbrev Digits (w : List ℕ+) : Prop := ∀ a ∈ w, (a:ℕ) ≤ 3
private theorem digits_append (u v : List ℕ+) (hu : Digits u) (hv : Digits v) : Digits (u++v) := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hu a ha
  · exact hv a ha
private theorem repeat_digits (n : ℕ) : Digits (lowerRepeat lowerPeriod n) := by
  induction n with
  | zero => simp [lowerRepeat, Digits]
  | succ n ih => rw [repeat_succ]; exact digits_append _ _ (by decide) ih
private theorem core_parameter : lowerParameterBox ([3,2,1,1,3],[4,3,2,2]) := by
  norm_num [lowerParameterBox, lowerRatio, lowerCD, List.foldl]
private theorem core_mem : ([3,2,1,1,3],[4,3,2,2]) ∈ lowerCores := by
  simp [lowerCores, lowerBaseCores]
private theorem stem_factor (n : ℕ) (a : List ℕ+) (ha : Digits a) :
    ∃ t, ([3,2,1,1]++lowerRepeat lowerPeriod n++(3::a)) = [3,2,1,1,3]++t ∧ Digits t := by
  cases n with
  | zero => exact ⟨a, rfl, ha⟩
  | succ n =>
    refine ⟨[1,3,1,2,1]++lowerRepeat lowerPeriod n++(3::a), ?_, ?_⟩
    · rw [repeat_succ]; simp [lowerPeriod, List.append_assoc]
    · exact digits_append _ _ (digits_append _ _ (by decide) (repeat_digits n))
        (by intro b hb; rcases List.mem_cons.mp hb with rfl | hb; norm_num; exact ha b hb)
private theorem basic_pair (n : ℕ) (a b : List ℕ+) (ha : Digits a) (hb : Digits b)
    (hna : NoBad (3::a)) (hnb : NoBad b) :
    lowerAdmissible ([3,2,1,1]++lowerRepeat lowerPeriod n++(3::a),
      [4,3,2,2]++lowerRepeat lowerPeriod n++b) ∧
    lowerParameterBox ([3,2,1,1]++lowerRepeat lowerPeriod n++(3::a),
      [4,3,2,2]++lowerRepeat lowerPeriod n++b) := by
  obtain ⟨t, ht, htd⟩ := stem_factor n a ha
  have he : lowerExtends ([3,2,1,1,3],[4,3,2,2])
      ([3,2,1,1]++lowerRepeat lowerPeriod n++(3::a),[4,3,2,2]++lowerRepeat lowerPeriod n++b) := by
    refine ⟨t, lowerRepeat lowerPeriod n++b, ?_, htd, digits_append _ _ (repeat_digits n) hb⟩
    simp only [Prod.mk.injEq]
    exact ⟨ht, List.append_assoc ..⟩
  have hleft : NoBad ([3,2,1,1]++lowerRepeat lowerPeriod n++(3::a)) := by
    rw [List.append_assoc, stemA_noBad]; exact repeat_noBad n _ hna
  have hright : NoBad ([4,3,2,2]++lowerRepeat lowerPeriod n++b) := by
    rw [List.append_assoc, stemB_noBad]; exact repeat_noBad n _ hnb
  exact ⟨⟨⟨_,core_mem,he⟩,separator_noBad _ _ (reverse_noBad _ hleft) hright⟩,
    Freiman.lower_parameter_extension _ _ core_parameter he⟩
private theorem core_swap_mem (c : LowerPair) (hc : c ∈ lowerCores) : c.swap ∈ lowerCores := by
  simp only [lowerCores, List.mem_append, List.mem_map] at hc ⊢
  rcases hc with hc | ⟨p,hp,rfl⟩
  · exact Or.inr ⟨c,hc,rfl⟩
  · exact Or.inl (by simpa using hp)
private theorem admissible_swap (p : LowerPair) (hp : lowerAdmissible p) : lowerAdmissible p.swap := by
  obtain ⟨⟨c,hc,u,v,he,hu,hv⟩,hn⟩ := hp
  refine ⟨⟨c.swap, core_swap_mem _ hc, v,u,?_,hv,hu⟩,?_⟩
  · simpa using congrArg Prod.swap he
  · have hbad : NoBad (p.1.reverse++[4]++p.2) := hn
    have hh := reverse_noBad _ hbad
    simpa [NoBad, badWord, List.reverse_append, List.append_assoc] using hh
private theorem pair_swap (p : LowerPair) (hp : lowerAdmissible p ∧ lowerParameterBox p) :
    lowerAdmissible p.swap ∧ lowerParameterBox p.swap := by
  exact ⟨admissible_swap _ hp.1, hp.2.2.2.1,hp.2.2.2.2,hp.2.1,hp.2.2.1⟩
end OtherBridgeWords

namespace OtherBridgeWords
private theorem family_A (n : ℕ) : ∀ d ∈ lowerBridgeLabels .A n,
    lowerAdmissible (lowerPhysicalAdd (lowerFamilyPair .A n 0 0) d) ∧
      lowerParameterBox (lowerPhysicalAdd (lowerFamilyPair .A n 0 0) d) := by
  have hnorm : lowerNormalize (lowerFamilyPair .A n 0 0) = (lowerFamilyPair .A n 0 0).swap := by
    simpa using Freiman.lower_initial_family_normalization LowerInitialFamily.A n 0 0 (by decide)
  intro d hd
  by_cases hn : n = 0
  · simp only [lowerBridgeLabels, if_pos hn, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · simp only [lowerPhysicalAdd, hnorm]
      simpa [lowerFamilyPair, List.append_assoc] using
        pair_swap _ (basic_pair n [1, 3, 1, 2, 1, 3, 3] [3, 1, 2, 1, 3, 3] (by decide) (by decide) (by decide) (by decide))
    · simp only [lowerPhysicalAdd, hnorm]
      simpa [lowerFamilyPair, List.append_assoc] using
        pair_swap _ (basic_pair n [1, 3, 1, 2, 1, 3, 3, 3, 3] [3, 1, 2, 1, 3, 3, 3, 3] (by decide) (by decide) (by decide) (by decide))
    · simp only [lowerPhysicalAdd, hnorm]
      simpa [lowerFamilyPair, List.append_assoc] using
        pair_swap _ (basic_pair n [1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 2] [3, 1, 2, 1, 3, 1, 3, 1, 2, 2] (by decide) (by decide) (by decide) (by decide))
    · simp only [lowerPhysicalAdd, hnorm]
      simpa [lowerFamilyPair, List.append_assoc] using
        pair_swap _ (basic_pair n [1, 3, 1, 2, 1, 3, 3, 3] [3, 1, 2, 1, 3, 3, 3] (by decide) (by decide) (by decide) (by decide))
    · simp only [lowerPhysicalAdd, hnorm]
      simpa [lowerFamilyPair, List.append_assoc] using
        pair_swap _ (basic_pair n [1, 3, 1, 2, 1, 3] [3, 1, 2, 1, 3] (by decide) (by decide) (by decide) (by decide))
  · simp only [lowerBridgeLabels, if_neg hn, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · simp only [lowerPhysicalAdd, hnorm]
      simpa [lowerFamilyPair, List.append_assoc] using
        pair_swap _ (basic_pair n [1, 3, 1, 2, 1, 3, 3] [3, 1, 2, 1, 3, 3] (by decide) (by decide) (by decide) (by decide))
    · simp only [lowerPhysicalAdd, hnorm]
      simpa [lowerFamilyPair, List.append_assoc] using
        pair_swap _ (basic_pair n [1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 2] [3, 1, 2, 1, 3, 1, 3, 1, 2, 1] (by decide) (by decide) (by decide) (by decide))
    · simp only [lowerPhysicalAdd, hnorm]
      simpa [lowerFamilyPair, List.append_assoc] using
        pair_swap _ (basic_pair n [1, 3, 1, 2, 1, 3, 3, 3] [3, 1, 2, 1, 3, 3, 3] (by decide) (by decide) (by decide) (by decide))
    · simp only [lowerPhysicalAdd, hnorm]
      simpa [lowerFamilyPair, List.append_assoc] using
        pair_swap _ (basic_pair n [1, 3, 1, 2, 1, 3] [3, 1, 2, 1, 3] (by decide) (by decide) (by decide) (by decide))
private theorem family_B (n : ℕ) : ∀ d ∈ lowerBridgeLabels .B n,
    lowerAdmissible (lowerPhysicalAdd (lowerFamilyPair .B n 0 0) d) ∧
      lowerParameterBox (lowerPhysicalAdd (lowerFamilyPair .B n 0 0) d) := by
  have hnorm : lowerNormalize (lowerFamilyPair .B n 0 0) = lowerFamilyPair .B n 0 0 := by
    simpa using Freiman.lower_initial_family_normalization LowerInitialFamily.B n 0 0 (by decide)
  intro d hd
  simp only [lowerBridgeLabels, List.mem_singleton] at hd
  subst d
  simp only [lowerPhysicalAdd, hnorm]
  simpa [lowerFamilyPair, List.append_assoc] using
    basic_pair n [1,3,1,2,1,3] [3,1,3,1,2] (by decide) (by decide) (by decide) (by decide)
end OtherBridgeWords

theorem solution (c : LowerBridgeCase) (n : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (hf : lowerBridgeFamily c ≠ .C) : ∀ d ∈ lowerBridgeLabels (lowerBridgeFamily c) n, lowerAdmissible (lowerPhysicalAdd (lowerFamilyPair (lowerBridgeFamily c) n 0 0) d) ∧ lowerParameterBox (lowerPhysicalAdd (lowerFamilyPair (lowerBridgeFamily c) n 0 0) d) := by
  cases c with
  | aZero => exact OtherBridgeWords.family_A n
  | aPos => exact OtherBridgeWords.family_A n
  | bZero => exact OtherBridgeWords.family_B n
  | bPos => exact OtherBridgeWords.family_B n
  | cZero => exact False.elim (hf rfl)
  | cPos => exact False.elim (hf rfl)
#print axioms solution

example : (∀ (c : LowerBridgeCase) (n : ℕ) (hc : lowerBridgeZero c = decide (n=0)) (hf : lowerBridgeFamily c ≠ .C) ,  ∀ d ∈ lowerBridgeLabels (lowerBridgeFamily c) n, lowerAdmissible (lowerPhysicalAdd (lowerFamilyPair (lowerBridgeFamily c) n 0 0) d) ∧ lowerParameterBox (lowerPhysicalAdd (lowerFamilyPair (lowerBridgeFamily c) n 0 0) d)) := @solution
