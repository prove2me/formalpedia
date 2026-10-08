-- Prove2me | solution 1 for FlowJobShop.SPT.mft_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:00:50.042982+00:00
-- url     : https://prove2.me/submissions/e503fb66-b20e-41b8-bd68-20c845f32cdc

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobShop_SPT_MeanFlowTime
import Definitions.Def_FlowJobShop_SPT_ListSchedule

open JobShopLTAS.Core


namespace FlowJobShop.SPT

open MeasureTheory

lemma wlb_disjoint_sum {ι : Type*} (O : Finset ι) (s p : ι → ℝ) (F : ℝ) (hF0 : 0 ≤ F)
    (hp : ∀ o ∈ O, 0 < p o) (h0 : ∀ o ∈ O, 0 ≤ s o) (hF : ∀ o ∈ O, s o + p o ≤ F)
    (hd : ∀ o ∈ O, ∀ o' ∈ O, o ≠ o' → s o + p o ≤ s o' ∨ s o' + p o' ≤ s o) :
    ∑ o ∈ O, p o ≤ F := by
  classical
  have hdis : (↑O : Set ι).PairwiseDisjoint (fun o => Set.Ico (s o) (s o + p o)) := by
    intro o ho o' ho' hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_Ico] at hx hx'
    rcases hd o ho o' ho' hne with h | h <;> linarith [hx.1, hx.2, hx'.1, hx'.2]
  have h1 : volume (⋃ o ∈ O, Set.Ico (s o) (s o + p o)) = ∑ o ∈ O, ENNReal.ofReal (p o) := by
    rw [measure_biUnion_finset hdis (fun o _ => measurableSet_Ico)]
    apply Finset.sum_congr rfl
    intro o _
    simp
  have h2 : volume (⋃ o ∈ O, Set.Ico (s o) (s o + p o)) ≤ volume (Set.Icc (0:ℝ) F) := by
    apply measure_mono
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_Ico] at hx
    obtain ⟨o, ho, h1, h2⟩ := hx
    simp only [Set.mem_Icc]
    constructor
    · linarith [h0 o ho]
    · linarith [hF o ho, hp o ho]
  rw [h1, Real.volume_Icc, sub_zero] at h2
  rw [← ENNReal.ofReal_sum_of_nonneg (fun o ho => (hp o ho).le)] at h2
  exact (ENNReal.ofReal_le_ofReal_iff hF0).1 h2


lemma fin_ge {m n : ℕ} (inst : Instance m n) (s : inst.Op → ℝ) (j : Fin n) (i : Fin (inst.μ j)) :
    s ⟨j, i⟩ + inst.p j i ≤ finishTime inst s j := by
  unfold finishTime
  rw [Finset.le_fold_max]
  exact Or.inr ⟨i, Finset.mem_univ _, le_rfl⟩

lemma fin_nonneg {m n : ℕ} (inst : Instance m n) (s : inst.Op → ℝ) (j : Fin n) :
    0 ≤ finishTime inst s j := by
  unfold finishTime
  rw [Finset.le_fold_max]
  exact Or.inl le_rfl

theorem wlb_core {m n : ℕ} (inst : Instance m n) (τ : inst.Op → ℝ)
    (hτ : IsPaperFeasibleSchedule inst τ) (ρ : Fin n ≃ Fin n)
    (hρ : Monotone fun k => finishTime inst τ (ρ k)) (k : Fin n) :
    ∑ j ∈ Finset.Iic k, inst.jobLength (ρ j) ≤ (m : ℝ) * finishTime inst τ (ρ k) := by
  classical
  set F := finishTime inst τ (ρ k) with hFdef
  have hF0 : 0 ≤ F := fin_nonneg inst τ _
  set J : Finset (Fin n) := (Finset.Iic k).map ρ.toEmbedding with hJ
  have e1 : ∑ j ∈ Finset.Iic k, inst.jobLength (ρ j) = ∑ j ∈ J, inst.jobLength j := by
    rw [hJ, Finset.sum_map]; rfl
  set O : Finset inst.Op := J.sigma (fun j => (Finset.univ : Finset (Fin (inst.μ j)))) with hO
  have e2 : ∑ j ∈ J, inst.jobLength j = ∑ o ∈ O, inst.proc o := by
    rw [hO, Finset.sum_sigma]; rfl
  have e3 : ∑ o ∈ O, inst.proc o = ∑ t : Fin m, ∑ o ∈ O with inst.mach o = t, inst.proc o :=
    (Finset.sum_fiberwise O inst.mach inst.proc).symm
  have hmem : ∀ o ∈ O, o.1 ∈ J := by
    intro o ho; rw [hO, Finset.mem_sigma] at ho; exact ho.1
  have hle : ∀ o ∈ O, τ o + inst.proc o ≤ F := by
    intro o ho
    have h1 := hmem o ho
    rw [hJ, Finset.mem_map] at h1
    obtain ⟨j', hj', hj'e⟩ := h1
    have : finishTime inst τ o.1 ≤ F := by
      rw [← hj'e]
      exact hρ (by simpa using hj')
    exact le_trans (fin_ge inst τ o.1 o.2) this
  have e4 : ∀ t : Fin m, ∑ o ∈ O with inst.mach o = t, inst.proc o ≤ F := by
    intro t
    rw [← Finset.sum_filter_of_ne (p := fun o => 0 < inst.proc o)]
    · apply wlb_disjoint_sum _ τ inst.proc F hF0
      · intro o ho; simp at ho; exact ho.2
      · intro o _; exact hτ.start_nonneg o
      · intro o ho; simp only [Finset.mem_filter] at ho; exact hle o ho.1.1
      · intro o ho o' ho' hne
        simp only [Finset.mem_filter] at ho ho'
        exact hτ.machine_disjoint o o' hne (ho.1.2.trans ho'.1.2.symm) ho.2 ho'.2
    · intro o ho hne
      have : 0 ≤ inst.proc o := inst.p_nonneg _ _
      exact lt_of_le_of_ne this (Ne.symm hne)
  rw [e1, e2, e3]
  calc _ ≤ ∑ t : Fin m, F := Finset.sum_le_sum (fun t _ => e4 t)
    _ = _ := by simp


theorem spl_core {n : ℕ} (L : Fin n → ℝ) (σ : Fin n ≃ Fin n)
    (hσ : Monotone fun k => L (σ k)) (ρ : Fin n ≃ Fin n) (k : Fin n) :
    ∑ j ∈ Finset.Iic k, L (σ j) ≤ ∑ j ∈ Finset.Iic k, L (ρ j) := by
  classical
  set a : Fin n → ℝ := fun i => L (σ i) with ha
  have hL : ∀ x, L x = a (σ.symm x) := by intro x; simp [ha]
  have h2 : ∑ j ∈ Finset.Iic k, L (ρ j) = ∑ j ∈ (Finset.Iic k).map (ρ.trans σ.symm).toEmbedding, a j := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro j _
    simp [hL]
  rw [h2]
  set I := Finset.Iic k with hI
  set T := I.map (ρ.trans σ.symm).toEmbedding with hT
  have hc : T.card = I.card := by simp [hT]
  have hc2 : (T \ I).card = (I \ T).card := Finset.card_sdiff_comm hc
  have e1 : ∑ j ∈ T, a j = ∑ j ∈ T \ I, a j + ∑ j ∈ T ∩ I, a j := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter T I), Finset.sdiff_union_inter]
  have e2 : ∑ j ∈ I, a j = ∑ j ∈ I \ T, a j + ∑ j ∈ T ∩ I, a j := by
    rw [Finset.inter_comm, ← Finset.sum_union (Finset.disjoint_sdiff_inter I T), Finset.sdiff_union_inter]
  have b1 : ∑ j ∈ I \ T, a j ≤ (I \ T).card • a k := by
    apply Finset.sum_le_card_nsmul
    intro x hx
    have : x ≤ k := by simpa [hI] using (Finset.mem_sdiff.1 hx).1
    exact hσ this
  have b2 : (T \ I).card • a k ≤ ∑ j ∈ T \ I, a j := by
    apply Finset.card_nsmul_le_sum
    intro x hx
    have : ¬ x ≤ k := by simpa [hI] using (Finset.mem_sdiff.1 hx).2
    exact hσ (le_of_lt (not_le.1 this))
  rw [hc2] at b2
  linarith


theorem mlb_core {m n : ℕ} (inst : Instance m n) (σ : Fin n ≃ Fin n)
    (hσ : IsSPTOrder inst σ) (τ : inst.Op → ℝ) (hτ : IsPaperFeasibleSchedule inst τ) :
    (∑ k : Fin n, ∑ j ∈ Finset.Iic k, inst.jobLength (σ j)) / n ≤
      (m : ℝ) * meanFlowTime inst τ := by
  classical
  set ρ := Tuple.sort (fun j => finishTime inst τ j) with hρ
  have hmono : Monotone fun k => finishTime inst τ (ρ k) := Tuple.monotone_sort (fun j => finishTime inst τ j)
  have key : ∀ k, ∑ j ∈ Finset.Iic k, inst.jobLength (σ j) ≤ (m : ℝ) * finishTime inst τ (ρ k) :=
    fun k => (spl_core inst.jobLength σ hσ ρ k).trans (wlb_core inst τ hτ ρ hmono k)
  have h1 : (∑ k : Fin n, ∑ j ∈ Finset.Iic k, inst.jobLength (σ j)) ≤ (m : ℝ) * ∑ j, finishTime inst τ j := by
    calc _ ≤ ∑ k : Fin n, (m : ℝ) * finishTime inst τ (ρ k) := Finset.sum_le_sum (fun k _ => key k)
      _ = (m : ℝ) * ∑ k : Fin n, finishTime inst τ (ρ k) := by rw [Finset.mul_sum]
      _ = _ := by rw [Equiv.sum_comp ρ (fun j => finishTime inst τ j)]
  unfold meanFlowTime
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right h1 (Nat.cast_nonneg n)

end FlowJobShop.SPT

open FlowJobShop.SPT


theorem solution {m n : ℕ} (inst : Instance m n) (hm : 0 < m) (σ : Fin n ≃ Fin n)
    (hσ : IsSPTOrder inst σ) (τ : inst.Op → ℝ) (hτ : IsPaperFeasibleSchedule inst τ) :
    (∑ k : Fin n, ∑ j ∈ Finset.Iic k, inst.jobLength (σ j)) / n ≤
      (m : ℝ) * meanFlowTime inst τ := by
  exact mlb_core inst σ hσ τ hτ
