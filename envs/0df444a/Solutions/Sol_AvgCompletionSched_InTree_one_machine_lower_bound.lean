-- Prove2me | solution 1 for AvgCompletionSched.InTree.one_machine_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T16:11:11.512756+00:00
-- url     : https://prove2.me/submissions/84c50240-1d50-4ce0-9941-69f96c6fb965

import Mathlib
import Definitions.Def_AvgCompletionSched_InTree_Model

open MeasureTheory

namespace AvgCompletionSched.InTree

variable {n : ℕ}

/-- Packing bound: jobs completing by time `t` have total length at most `m t`. -/
lemma pack {I : Instance n} {m : ℕ} (N : Schedule I m) (t : ℝ) (ht : 0 ≤ t) :
    ∑ k ∈ Finset.univ.filter (fun k => N.C k ≤ t), I.p k ≤ m * t := by
  rw [← Finset.sum_fiberwise (Finset.univ.filter (fun k => N.C k ≤ t)) N.M]
  have hmach : ∀ μ : Fin m,
      ∑ k ∈ (Finset.univ.filter (fun k => N.C k ≤ t)).filter (fun k => N.M k = μ), I.p k ≤ t := by
    intro μ
    set T := (Finset.univ.filter (fun k => N.C k ≤ t)).filter (fun k => N.M k = μ) with hT
    have hdisj : Set.PairwiseDisjoint (↑T) (fun k => Set.Ico (N.S k) (N.S k + I.p k)) := by
      intro a ha b hb hab
      simp only [hT, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
      rw [Function.onFun, Set.disjoint_left]
      intro x hxa hxb
      rcases N.noOverlap a b (ha.2.trans hb.2.symm) hab with h | h
      · linarith [hxa.2, hxb.1]
      · linarith [hxa.1, hxb.2]
    have hsub : (⋃ k ∈ T, Set.Ico (N.S k) (N.S k + I.p k)) ⊆ Set.Icc 0 t := by
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨k, hk, hx⟩ := hx
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have h1 := N.nonneg k
      have h2 : N.S k + I.p k ≤ t := hk.1
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hvol := measure_mono (μ := (volume : Measure ℝ)) hsub
    rw [measure_biUnion_finset hdisj (fun k _ => measurableSet_Ico)] at hvol
    simp only [Real.volume_Ico, Real.volume_Icc, add_sub_cancel_left, sub_zero] at hvol
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => (I.p_pos k).le)] at hvol
    exact (ENNReal.ofReal_le_ofReal_iff ht).1 hvol
  calc ∑ μ : Fin m, ∑ k ∈ (Finset.univ.filter (fun k => N.C k ≤ t)).filter
          (fun k => N.M k = μ), I.p k
      ≤ ∑ _μ : Fin m, t := Finset.sum_le_sum (fun μ _ => hmach μ)
    _ = m * t := by simp

/-- Strict "earlier" relation: by completion time, ties broken by index. -/
def before {I : Instance n} {m : ℕ} (N : Schedule I m) (k j : Fin n) : Prop :=
  N.C k < N.C j ∨ (N.C k = N.C j ∧ k < j)

lemma before_trans {I : Instance n} {m : ℕ} (N : Schedule I m) {a b c : Fin n}
    (h1 : before N a b) (h2 : before N b c) : before N a c := by
  unfold before at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · left; linarith
  · left; linarith
  · left; linarith
  · right; exact ⟨h1.trans h2, h1'.trans h2'⟩

lemma before_irrefl {I : Instance n} {m : ℕ} (N : Schedule I m) (a : Fin n) :
    ¬ before N a a := by
  unfold before; rintro (h | ⟨_, h⟩) <;> exact lt_irrefl _ h

lemma before_total {I : Instance n} {m : ℕ} (N : Schedule I m) {a b : Fin n} (hab : a ≠ b) :
    before N a b ∨ before N b a := by
  unfold before
  rcases lt_trichotomy (N.C a) (N.C b) with h | h | h
  · left; left; exact h
  · rcases lt_or_gt_of_ne hab with h' | h'
    · left; right; exact ⟨h, h'⟩
    · right; right; exact ⟨h.symm, h'⟩
  · right; left; exact h

open Classical in
noncomputable def rankN {I : Instance n} {m : ℕ} (N : Schedule I m) (j : Fin n) : ℕ :=
  (Finset.univ.filter (fun k => before N k j)).card

lemma rankN_lt {I : Instance n} {m : ℕ} (N : Schedule I m) (j : Fin n) : rankN N j < n := by
  classical
  unfold rankN
  have : (Finset.univ.filter (fun k => before N k j)) ⊂ Finset.univ := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ _, fun h => ?_⟩
    have hj : j ∈ Finset.univ.filter (fun k => before N k j) := by rw [h]; exact Finset.mem_univ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact before_irrefl N j hj
  have := Finset.card_lt_card this
  simpa using this

lemma rankN_strict {I : Instance n} {m : ℕ} (N : Schedule I m) {a b : Fin n}
    (h : before N a b) : rankN N a < rankN N b := by
  classical
  unfold rankN
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.2 ⟨?_, fun he => ?_⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact before_trans N hk h
  · have ha : a ∈ Finset.univ.filter (fun k => before N k b) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h
    rw [← he] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact before_irrefl N a ha

noncomputable def rankF {I : Instance n} {m : ℕ} (N : Schedule I m) (j : Fin n) : Fin n :=
  ⟨rankN N j, rankN_lt N j⟩

lemma rankF_inj {I : Instance n} {m : ℕ} (N : Schedule I m) : Function.Injective (rankF N) := by
  intro a b h
  by_contra hab
  have h' : rankN N a = rankN N b := congrArg Fin.val h
  rcases before_total N hab with h1 | h1
  · exact absurd h' (rankN_strict N h1).ne
  · exact absurd h' (rankN_strict N h1).ne'

theorem one_machine_lower_bound {n : ℕ} (I : Instance n) (m : ℕ) (hm : 1 ≤ m)
    (π : Fin n ≃ Fin n) (hπ : IsOptimalOneMachine I π) (N : Schedule I m) :
    oneMachineWct I π / (m : ℝ) ≤ N.wct := by
  have hbij : Function.Bijective (rankF N) :=
    (Finite.injective_iff_bijective).1 (rankF_inj N)
  set e := Equiv.ofBijective (rankF N) hbij with he
  set σ := e.symm with hσ
  have hσs : ∀ j, σ.symm j = rankF N j := by intro j; simp [hσ, he]
  -- σ obeys precedence
  have hobey : ObeysPrecedence I σ := by
    intro i j hij
    rw [hσs, hσs]
    have hp := I.p_pos i
    have hpj := I.p_pos j
    have h1 := N.precedence i j hij
    have hb : before N i j := by
      left; unfold Schedule.C; linarith
    exact rankN_strict N hb
  -- one-machine completion times are at most m * C_j
  have hC : ∀ j, oneMachineC I σ j ≤ m * N.C j := by
    intro j
    unfold oneMachineC
    have hre : ∑ k ∈ Finset.univ.filter (fun k => k ≤ σ.symm j), I.p (σ k) =
        ∑ k ∈ Finset.univ.filter (fun k => σ.symm k ≤ σ.symm j), I.p k := by
      apply Finset.sum_equiv σ
      · intro i; simp
      · intro i _; rfl
    rw [hre]
    have hsub : Finset.univ.filter (fun k => σ.symm k ≤ σ.symm j) ⊆
        Finset.univ.filter (fun k => N.C k ≤ N.C j) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      by_contra hlt
      rw [not_le] at hlt
      have hb : before N j k := Or.inl hlt
      have := rankN_strict N hb
      rw [hσs, hσs] at hk
      exact absurd hk (not_le.2 this)
    have hCj : 0 ≤ N.C j := by
      unfold Schedule.C; linarith [N.nonneg j, I.p_pos j]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => (I.p_pos k).le)).trans (pack N (N.C j) hCj)
  have hle : oneMachineWct I π ≤ oneMachineWct I σ := hπ.2 σ hobey
  have hσle : oneMachineWct I σ ≤ m * N.wct := by
    unfold oneMachineWct Schedule.wct
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have := mul_le_mul_of_nonneg_left (hC j) (I.w_pos j).le
    linarith
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_le_iff₀ hm']
  linarith

end AvgCompletionSched.InTree

open AvgCompletionSched.InTree

theorem solution {n : ℕ} (I : Instance n) (m : ℕ) (hm : 1 ≤ m)
    (π : Fin n ≃ Fin n) (hπ : IsOptimalOneMachine I π) (N : Schedule I m) :
    oneMachineWct I π / (m : ℝ) ≤ N.wct := by
  exact one_machine_lower_bound I m hm π hπ N
