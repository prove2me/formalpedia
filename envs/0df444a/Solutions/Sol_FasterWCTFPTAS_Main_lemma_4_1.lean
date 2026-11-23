-- Prove2me | solution 1 for FasterWCTFPTAS.Main.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:42:23.653558+00:00
-- url     : https://prove2.me/submissions/e3576746-961b-4eec-a3df-4587ac37db2c

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_DP

set_option autoImplicit false

open FasterWCTFPTAS.Main
open Finset

namespace Lemma41Aux

lemma firstJobs_succ {n : ℕ} (i : Fin n) :
    firstJobs n (i.val + 1) = insert i (firstJobs n i.val) := by
  ext j
  simp only [firstJobs, mem_insert, mem_filter, mem_univ, true_and]
  constructor
  · intro hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
    · exact Or.inr hlt
    · exact Or.inl (Fin.ext heq)
  · rintro (rfl | hlt)
    · exact Nat.lt_succ_self j.val
    · exact Nat.lt_succ_of_lt hlt

lemma not_mem_firstJobs_self {n : ℕ} (i : Fin n) :
    i ∉ firstJobs n i.val := by
  simp [firstJobs]

lemma piVec_congr {m n : ℕ} (p : Fin n → ℝ) (k : ℕ) {σ₁ σ₂ : Fin n → Fin m}
    (h : ∀ j ∈ firstJobs n k, σ₁ j = σ₂ j) :
    piVec m p k σ₁ = piVec m p k σ₂ := by
  ext c
  unfold piVec
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j
  simp only [mem_filter]
  exact ⟨fun ⟨hj, hs⟩ => ⟨hj, (h j hj).symm.trans hs⟩,
         fun ⟨hj, hs⟩ => ⟨hj, (h j hj).trans hs⟩⟩

lemma theta_congr {m n : ℕ} (p w : Fin n → ℝ) (k : ℕ) {σ₁ σ₂ : Fin n → Fin m}
    (h : ∀ j ∈ firstJobs n k, σ₁ j = σ₂ j) :
    theta m p w k σ₁ = theta m p w k σ₂ := by
  unfold theta costIdxOn
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext l
  simp only [mem_filter]
  constructor
  · rintro ⟨hl, hsl, hle⟩
    exact ⟨hl, by rw [← h l hl, ← h j hj]; exact hsl, hle⟩
  · rintro ⟨hl, hsl, hle⟩
    exact ⟨hl, by rw [h l hl, h j hj]; exact hsl, hle⟩

lemma piVec_nonneg {m n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) (k : ℕ) (σ : Fin n → Fin m)
    (c : Fin (m - 1)) : 0 ≤ piVec m p k σ c :=
  Finset.sum_nonneg fun j _ => le_of_lt (hp j)

lemma sum_abs_piVec {m n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) (k : ℕ) (σ : Fin n → Fin m) :
    ∑ c : Fin (m - 1), |piVec m p k σ c| = ∑ c : Fin (m - 1), piVec m p k σ c :=
  Finset.sum_congr rfl fun c _ => abs_of_nonneg (piVec_nonneg p hp k σ c)

lemma load_last_eq {m' n : ℕ} (p : Fin n → ℝ) (k : ℕ) (σ : Fin n → Fin (m' + 1)) :
    ∑ j ∈ (firstJobs n k).filter (fun j => σ j = Fin.last m'), p j =
      T p k - ∑ c : Fin m', piVec (m' + 1) p k σ c := by
  have hpart :
      T p k = ∑ l : Fin (m' + 1), ∑ j ∈ (firstJobs n k).filter (fun j => σ j = l), p j := by
    unfold T firstJobs
    symm
    exact Finset.sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) p
  rw [Fin.sum_univ_castSucc] at hpart
  have hcoord : ∀ c : Fin m',
      ∑ j ∈ (firstJobs n k).filter (fun j => σ j = Fin.castSucc c), p j =
        piVec (m' + 1) p k σ c := fun _ => rfl
  simp_rw [hcoord] at hpart
  linarith

lemma piVec_succ_step {m' n : ℕ} (p : Fin n → ℝ) (i : Fin n) (σ : Fin n → Fin (m' + 1)) :
    piVec (m' + 1) p (i.val + 1) σ =
      if h : (σ i).val < m' then
        piVec (m' + 1) p i.val σ + Pi.single ⟨(σ i).val, h⟩ (p i)
      else
        piVec (m' + 1) p i.val σ := by
  have hi_not : i ∉ firstJobs n i.val := not_mem_firstJobs_self i
  ext c
  change ∑ j ∈ (firstJobs n (i.val + 1)).filter (fun j => σ j = Fin.castSucc c), p j = _
  rw [firstJobs_succ, Finset.filter_insert]
  split_ifs with h1 h2 h2
  · simp only [Pi.add_apply]
    rw [Finset.sum_insert (fun hm => hi_not (Finset.mem_of_mem_filter _ hm))]
    have hc_eq : (⟨(σ i).val, h2⟩ : Fin m') = c := by
      apply Fin.ext
      dsimp
      exact congrArg Fin.val h1
    rw [hc_eq, Pi.single_eq_same]
    change p i + piVec (m' + 1) p i.val σ c = piVec (m' + 1) p i.val σ c + p i
    ring
  · exfalso
    apply h2
    rw [h1]
    exact c.isLt
  · simp only [Pi.add_apply]
    have hc_ne : c ≠ ⟨(σ i).val, h2⟩ := by
      intro heq
      apply h1
      apply Fin.ext
      dsimp
      exact (congrArg Fin.val heq).symm
    rw [Pi.single_eq_of_ne hc_ne, add_zero]
    rfl
  · rfl

lemma theta_succ_step {m' n : ℕ} (p w : Fin n → ℝ) (i : Fin n) (σ : Fin n → Fin (m' + 1)) :
    theta (m' + 1) p w (i.val + 1) σ =
      theta (m' + 1) p w i.val σ +
        w i * ((∑ l ∈ (firstJobs n i.val).filter (fun l => σ l = σ i), p l) + p i) := by
  have hi_not : i ∉ firstJobs n i.val := not_mem_firstJobs_self i
  unfold theta costIdxOn
  rw [firstJobs_succ, Finset.sum_insert hi_not]
  have hprev :
      ∑ j ∈ firstJobs n i.val,
          w j * ∑ l ∈ (insert i (firstJobs n i.val)).filter (fun l => σ l = σ j ∧ l ≤ j), p l =
        ∑ j ∈ firstJobs n i.val,
          w j * ∑ l ∈ (firstJobs n i.val).filter (fun l => σ l = σ j ∧ l ≤ j), p l := by
    refine Finset.sum_congr rfl fun j hj => ?_
    congr 1
    have hj_lt : j.val < i.val := (mem_filter.mp hj).2
    have hi_not_le : ¬ (i ≤ j) := not_le_of_gt hj_lt
    rw [Finset.filter_insert]
    simp [hi_not_le]
  rw [hprev]
  have hlast :
      (insert i (firstJobs n i.val)).filter (fun l => σ l = σ i ∧ l ≤ i) =
        insert i ((firstJobs n i.val).filter (fun l => σ l = σ i)) := by
    ext l
    simp only [mem_filter, mem_insert, firstJobs, mem_univ, true_and]
    constructor
    · rintro ⟨rfl | hlt, hs, _⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hlt, hs⟩
    · rintro (rfl | ⟨hlt, hs⟩)
      · exact ⟨Or.inl rfl, rfl, le_rfl⟩
      · exact ⟨Or.inr hlt, hs, le_of_lt hlt⟩
  rw [hlast, Finset.sum_insert (fun hm => hi_not (Finset.mem_of_mem_filter _ hm))]
  ring

end Lemma41Aux

theorem solution {m n : ℕ} (_hm : 2 ≤ m) (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (_hw : ∀ j, 0 ≤ w j)
    (_hsort : Sorted p w) (i : Fin n) :
    DP m p w (i.val + 1) = recur m p w i (DP m p w i.val) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  ext x
  constructor
  · rintro ⟨σ, rfl⟩
    unfold recur pairOf
    rw [Lemma41Aux.piVec_succ_step, Lemma41Aux.theta_succ_step]
    by_cases hlt : (σ i).val < m'
    · left
      let k0 : Fin m' := ⟨(σ i).val, hlt⟩
      refine ⟨pairOf (m' + 1) p w i.val σ, ⟨σ, rfl⟩, k0, ?_⟩
      simp only [hlt, ↓reduceDIte, pairOf]
      rfl
    · right
      refine ⟨pairOf (m' + 1) p w i.val σ, ⟨σ, rfl⟩, ?_⟩
      simp only [hlt, ↓reduceDIte, pairOf]
      have hsi : σ i = Fin.last m' := by
        apply Fin.ext
        change (σ i).val = m'
        have := (σ i).isLt
        omega
      rw [hsi, Lemma41Aux.load_last_eq, Lemma41Aux.sum_abs_piVec p hp]
      rfl
  · rintro (⟨y, ⟨σ, rfl⟩, k, rfl⟩ | ⟨y, ⟨σ, rfl⟩, rfl⟩)
    · let σ' : Fin n → Fin (m' + 1) := Function.update σ i (coordMachine k)
      have hagree : ∀ j ∈ firstJobs n i.val, σ' j = σ j := by
        intro j hj
        have hj_ne : j ≠ i := fun heq => Lemma41Aux.not_mem_firstJobs_self i (heq ▸ hj)
        exact Function.update_of_ne hj_ne _ _
      refine ⟨σ', ?_⟩
      unfold pairOf
      rw [Lemma41Aux.piVec_succ_step, Lemma41Aux.theta_succ_step]
      have hsi : σ' i = coordMachine k := Function.update_self i (coordMachine k) σ
      have hlt : (σ' i).val < m' := by
        rw [hsi]
        exact k.isLt
      simp only [hlt, ↓reduceDIte]
      have hk_eq : (⟨(σ' i).val, hlt⟩ : Fin m') = k := by
        apply Fin.ext
        dsimp
        exact congrArg Fin.val hsi
      rw [hk_eq, Lemma41Aux.piVec_congr p i.val hagree, Lemma41Aux.theta_congr p w i.val hagree]
      congr 2
      rw [hsi]
      have hload_congr :
          (firstJobs n i.val).filter (fun l => σ' l = coordMachine k) =
            (firstJobs n i.val).filter (fun l => σ l = coordMachine k) := by
        ext l
        simp only [mem_filter]
        exact ⟨fun ⟨hl, hs⟩ => ⟨hl, (hagree l hl).symm.trans hs⟩,
               fun ⟨hl, hs⟩ => ⟨hl, (hagree l hl).trans hs⟩⟩
      rw [hload_congr]
      rfl
    · let σ' : Fin n → Fin (m' + 1) := Function.update σ i (Fin.last m')
      have hagree : ∀ j ∈ firstJobs n i.val, σ' j = σ j := by
        intro j hj
        have hj_ne : j ≠ i := fun heq => Lemma41Aux.not_mem_firstJobs_self i (heq ▸ hj)
        exact Function.update_of_ne hj_ne _ _
      refine ⟨σ', ?_⟩
      unfold pairOf
      rw [Lemma41Aux.piVec_succ_step, Lemma41Aux.theta_succ_step]
      have hsi : σ' i = Fin.last m' := Function.update_self i (Fin.last m') σ
      have hlt : ¬ (σ' i).val < m' := by
        rw [hsi]
        simp
      simp only [hlt, ↓reduceDIte]
      rw [Lemma41Aux.piVec_congr p i.val hagree, Lemma41Aux.theta_congr p w i.val hagree]
      congr 2
      rw [hsi]
      have hload_congr :
          (firstJobs n i.val).filter (fun l => σ' l = Fin.last m') =
            (firstJobs n i.val).filter (fun l => σ l = Fin.last m') := by
        ext l
        simp only [mem_filter]
        exact ⟨fun ⟨hl, hs⟩ => ⟨hl, (hagree l hl).symm.trans hs⟩,
               fun ⟨hl, hs⟩ => ⟨hl, (hagree l hl).trans hs⟩⟩
      rw [hload_congr, Lemma41Aux.load_last_eq, Lemma41Aux.sum_abs_piVec p hp]
      rfl
