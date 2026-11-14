-- Prove2me | solution 1 for GenCountSampleLLL.insertion_input_row_stochastic
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:59:51.805416+00:00
-- url     : https://prove2.me/submissions/90ca6aaa-77e8-4b74-a7bf-5b22de1f5310

import Definitions.Def_GenCountSampleLLL_insertionChain
noncomputable section
open scoped Classical BigOperators ENNReal
open GenCountSampleLLL

private theorem DTi_last_eq_erase (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (hT : T ∈ I.twoTrees D a) :
    I.DTi D a T (I.ell D a T) = D.erase a := by
  have htree : I.IsTwoTree D a T := (Finset.mem_filter.mp hT).2
  have hsub : I.N2Dc D T ⊆ D := by
    intro b hb
    simp only [Inst.N2Dc, Finset.mem_union, Finset.mem_filter] at hb
    rcases hb with ht | ⟨hd, _⟩
    · exact htree.1 ht
    · exact hd
  have ha : a ∈ I.N2Dc D T := Finset.mem_union_left _ htree.2.1
  unfold Inst.DTi Inst.ell Inst.bList Inst.DT
  simp only [List.take_length, Finset.sort_toFinset]
  ext b
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_erase]
  constructor
  · rintro (⟨hb, hnot⟩ | ⟨hne, hb⟩)
    · exact ⟨fun he => hnot (he ▸ ha), hb⟩
    · exact ⟨hne, hsub hb⟩
  · rintro ⟨hne, hb⟩
    by_cases ht : b ∈ I.N2Dc D T
    · exact Or.inr ⟨hne, ht⟩
    · exact Or.inl ⟨hb, ht⟩

private theorem list_entries_valid (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (ω : I.ExpSpace) (T : Finset (Fin I.m)) (z : I.Assign)
    (he : (T,z) ∈ I.Llist D a ω) : T ∈ I.twoTrees D a ∧ z ∈ I.labelsE D a T := by
  unfold Inst.Llist at he
  obtain ⟨S, hS, heq⟩ := Finset.mem_image.mp he
  have hST : S = T := congrArg Prod.fst heq
  subst S
  have hz : I.sigT D T ω = z := congrArg Prod.snd heq
  have ht := (Finset.mem_filter.mp hS).1
  have hET := (Finset.mem_filter.mp hS).2
  refine ⟨ht, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩⟩
  · simpa [hz] using hET
  · rw [← hz]
    funext v
    by_cases hv : v ∈ I.UT D T <;> simp [Inst.sigT, Inst.restr, hv]

private theorem reset_layer_valid (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (ha : a ∈ D) (σ : I.Assign) (hσ : σ ∈ I.Good (D.erase a))
    (ω : I.ExpSpace) (T : Finset (Fin I.m)) (z : I.Assign)
    (he : (T,z) ∈ I.Llist D a ω) :
    (⟨[], Inst.Base.lay T z (I.ell D a T) σ⟩ : I.St) ∈ I.states D.card D a := by
  obtain ⟨hT,hz⟩ := list_entries_valid I D a ω T z he
  have hD : 0 < D.card := Finset.card_pos.mpr ⟨a,ha⟩
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hD)
  rw [hk, Inst.states]
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_biUnion.mpr
  refine ⟨T, hT, Finset.mem_biUnion.mpr ⟨z, hz, ?_⟩⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨I.ell D a T, Finset.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨σ, ?_, rfl⟩
  rwa [DTi_last_eq_erase I D a T hT]

private theorem dirac_sum_state (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (s : I.St) (hs : s ∈ I.states D.card D a) :
    (∑ Y : I.S D a, I.dirac s Y.1) = 1 := by
  let s' : I.S D a := ⟨s,hs⟩
  have heq (Y : I.S D a) : (Y.1 = s) ↔ Y = s' := by
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  simp only [Inst.dirac, heq]
  simp

private theorem iRule_reset_row_sum (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (ha : a ∈ D) (σ : I.Assign) (hσ : σ ∈ I.Good (D.erase a)) :
    (∑ Y : I.S D a, I.iRule D a σ Rule.reset Y.1) = 1 := by
  have hinput : (⟨[], Inst.Base.inp σ⟩ : I.St) ∈ I.states D.card D a := by
    have hD : 0 < D.card := Finset.card_pos.mpr ⟨a,ha⟩
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hD)
    rw [hk, Inst.states]
    simp [hσ]
  have hpoint (ω : I.ExpSpace) :
      (∑ Y : I.S D a,
        if I.Llist D a ω = ∅ then I.dirac ⟨[], Inst.Base.inp σ⟩ Y.1
        else ∑ e ∈ I.Llist D a ω,
          I.dirac ⟨[], Inst.Base.lay e.1 e.2 (I.ell D a e.1) σ⟩ Y.1 /
            ((I.Llist D a ω).card : ℝ)) = 1 := by
    by_cases hL : I.Llist D a ω = ∅
    · simp only [hL, if_true]
      exact dirac_sum_state I D a _ hinput
    · simp only [hL, if_false]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_div]
      have hs (e : Finset (Fin I.m) × I.Assign) (he : e ∈ I.Llist D a ω) :
          (∑ Y : I.S D a,
            I.dirac ⟨[], Inst.Base.lay e.1 e.2 (I.ell D a e.1) σ⟩ Y.1) = 1 := by
        apply dirac_sum_state
        exact reset_layer_valid I D a ha σ hσ ω e.1 e.2 (by simpa using he)
      have hcard : ((I.Llist D a ω).card : ℝ) ≠ 0 := by
        exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hL)
      calc
        _ = (∑ _e ∈ I.Llist D a ω, (1 : ℝ)) / (I.Llist D a ω).card := by
          congr 1
          apply Finset.sum_congr rfl
          intro e he
          exact hs e he
        _ = _ := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
          exact div_self hcard
  simp only [Inst.iRule, Inst.expL]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hpoint, mul_one]
  rw [← ENNReal.toReal_sum (by intro ω hω; exact I.expLaw.apply_ne_top ω)]
  have htotal := I.expLaw.tsum_coe
  rw [tsum_fintype] at htotal
  rw [htotal]
  simp

private theorem iRule_reset_nonnegative (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (σ : I.Assign) (Y : I.St) : 0 ≤ I.iRule D a σ Rule.reset Y := by
  simp only [Inst.iRule, Inst.expL]
  apply Finset.sum_nonneg
  intro ω hω
  apply mul_nonneg ENNReal.toReal_nonneg
  by_cases hL : I.Llist D a ω = ∅
  · simp [hL, Inst.dirac]
    split_ifs <;> norm_num
  · simp only [hL, if_false]
    apply Finset.sum_nonneg
    intro e he
    apply div_nonneg _ (Nat.cast_nonneg _)
    simp [Inst.dirac]
    split_ifs <;> norm_num

private theorem iRule_reset_stochastic (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (ha : a ∈ D) (σ : I.Assign) (hσ : σ ∈ I.Good (D.erase a)) :
    (∀ Y : I.S D a, 0 ≤ I.iRule D a σ Rule.reset Y.1) ∧
      (∑ Y : I.S D a, I.iRule D a σ Rule.reset Y.1) = 1 := by
  exact ⟨fun Y => iRule_reset_nonnegative I D a σ Y.1, iRule_reset_row_sum I D a ha σ hσ⟩

private theorem singleton_twoTree (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m) (ha : a ∈ D) :
    ({a} : Finset (Fin I.m)) ∈ I.twoTrees D a := by
  unfold Inst.twoTrees Inst.IsTwoTree
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.singleton_subset_iff, ha, true_and,
    Finset.mem_singleton, forall_eq]
  constructor
  · exact I.G.loopless.irrefl a
  · letI : Nonempty ({a} : Finset (Fin I.m)) := ⟨⟨a, by simp⟩⟩
    letI : Subsingleton ({a} : Finset (Fin I.m)) := ⟨by
      intro u v
      apply Subtype.ext
      have hu : u.1 = a := Finset.mem_singleton.mp u.2
      have hv : v.1 = a := Finset.mem_singleton.mp v.2
      exact hu.trans hv.symm⟩
    exact SimpleGraph.Connected.of_subsingleton

private theorem singleton_tree_assignment_valid (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (σ : I.Assign) (hσ : σ ∈ I.Good (D.erase a)) (hbad : I.bad a σ) :
    σ ∈ I.Estar D a {a} := by
  have hs : ∀ b ∈ D.erase a, ¬ I.bad b σ := (Finset.mem_filter.mp hσ).2
  have hF : I.F1 D a {a} ⊆ D.erase a := by
    intro b hb
    simp only [Inst.F1, Finset.mem_filter, Inst.Fset, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_singleton] at hb
    exact Finset.mem_erase.mpr ⟨fun h => hb.1.2 (Or.inl h), hb.1.1⟩
  have hDT : I.DT D {a} ⊆ D.erase a := by
    intro b hb
    simp only [Inst.DT, Finset.mem_sdiff] at hb
    apply Finset.mem_erase.mpr
    refine ⟨?_, hb.1⟩
    intro he
    apply hb.2
    exact Finset.mem_union_left _ (Finset.mem_singleton.mpr he)
  apply Finset.mem_inter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    constructor
    · simpa using hbad
    · intro b hb
      exact hs b (hF hb)
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro b hb
    exact hs b (hDT hb)

private theorem input_forward_target_valid (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (ha : a ∈ D) (σ : I.Assign) (hσ : σ ∈ I.Good (D.erase a)) :
    (if I.bad a σ then (⟨[], Inst.Base.tree {a} σ⟩ : I.St)
      else ⟨[], Inst.Base.out σ⟩) ∈ I.states D.card D a := by
  have hD : 0 < D.card := Finset.card_pos.mpr ⟨a,ha⟩
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hD)
  by_cases hbad : I.bad a σ
  · simp only [hbad, if_true]
    rw [hk, Inst.states]
    apply Finset.mem_union.mpr; left
    apply Finset.mem_union.mpr; left
    apply Finset.mem_union.mpr; right
    apply Finset.mem_biUnion.mpr
    refine ⟨{a}, singleton_twoTree I D a ha, ?_⟩
    exact Finset.mem_image.mpr ⟨σ, singleton_tree_assignment_valid I D a σ hσ hbad, rfl⟩
  · simp only [hbad, if_false]
    have hgood : σ ∈ I.Good D := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro b hb
      by_cases hba : b = a
      · simpa [hba] using hbad
      · exact (Finset.mem_filter.mp hσ).2 b (Finset.mem_erase.mpr ⟨hba,hb⟩)
    rw [hk, Inst.states]
    apply Finset.mem_union.mpr; left
    apply Finset.mem_union.mpr; left
    apply Finset.mem_union.mpr; left
    apply Finset.mem_union.mpr; right
    exact Finset.mem_image.mpr ⟨σ, hgood, rfl⟩

private theorem iRule_stochastic (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (ha : a ∈ D) (σ : I.Assign) (hσ : σ ∈ I.Good (D.erase a)) (r : Rule) :
    (∀ Y : I.S D a, 0 ≤ I.iRule D a σ r Y.1) ∧
      (∑ Y : I.S D a, I.iRule D a σ r Y.1) = 1 := by
  have hinput : (⟨[], Inst.Base.inp σ⟩ : I.St) ∈ I.states D.card D a := by
    have hD : 0 < D.card := Finset.card_pos.mpr ⟨a,ha⟩
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hD)
    rw [hk, Inst.states]
    simp [hσ]
  cases r with
  | reset => exact iRule_reset_stochastic I D a ha σ hσ
  | bwd =>
    constructor
    · intro Y
      simp [Inst.iRule, Inst.dirac]
      split_ifs <;> norm_num
    · simpa [Inst.iRule] using dirac_sum_state I D a _ hinput
  | fwd =>
    have hv := input_forward_target_valid I D a ha σ hσ
    constructor
    · intro Y
      by_cases hb : I.bad a σ <;> simp [Inst.iRule, Inst.dirac, hb] <;> split_ifs <;> norm_num
    · by_cases hb : I.bad a σ
      · simp only [hb, if_true] at hv
        simpa [Inst.iRule, hb] using dirac_sum_state I D a _ hv
      · simp only [hb, if_false] at hv
        simpa [Inst.iRule, hb] using dirac_sum_state I D a _ hv

theorem solution (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (ha : a ∈ D) (σ : I.Assign) (hσ : σ ∈ I.Good (D.erase a))
    (X : I.S D a) (hX : X.1 = ⟨[], Inst.Base.inp σ⟩) :
    (∀ Y : I.S D a, 0 ≤ I.Pker D a X Y) ∧
      (∑ Y : I.S D a, I.Pker D a X Y) = 1 := by
  have hf := iRule_stochastic I D a ha σ hσ Rule.fwd
  have hb := iRule_stochastic I D a ha σ hσ Rule.bwd
  have hr := iRule_stochastic I D a ha σ hσ Rule.reset
  constructor
  · intro Y
    have hfY := hf.1 Y
    have hbY := hb.1 Y
    have hrY := hr.1 Y
    simp only [Inst.Pker, hX, Inst.stepRule, Inst.baseRule]
    split_ifs <;> positivity
  · simp only [Inst.Pker, hX, Inst.stepRule, Inst.baseRule]
    rw [Finset.sum_add_distrib]
    simp_rw [← Finset.mul_sum]
    simp_rw [Finset.sum_add_distrib]
    rw [hf.2, hb.2, hr.2]
    simp
    norm_num

