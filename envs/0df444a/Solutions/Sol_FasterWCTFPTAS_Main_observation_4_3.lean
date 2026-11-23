-- Prove2me | solution 1 for FasterWCTFPTAS.Main.observation_4_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:42:24.86334+00:00
-- url     : https://prove2.me/submissions/e15c7e2c-2321-4899-9c42-b6331bfdd6a4

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_DP
import Theorems.Thm_FasterWCTFPTAS_Main_lemma_4_1

set_option autoImplicit false

open FasterWCTFPTAS.Main
open Finset

namespace Obs43Aux

lemma recur_mono {m n : ℕ} (p w : Fin n → ℝ) (i : Fin n) {A B : Set (Pt m)} (hAB : A ⊆ B) :
    recur m p w i A ⊆ recur m p w i B := by
  rintro x (⟨y, hy, k, rfl⟩ | ⟨y, hy, rfl⟩)
  · exact Or.inl ⟨y, hAB hy, k, rfl⟩
  · exact Or.inr ⟨y, hAB hy, rfl⟩

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

lemma sum_abs_piVec {m n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) (k : ℕ) (σ : Fin n → Fin m) :
    ∑ c : Fin (m - 1), |piVec m p k σ c| = ∑ c : Fin (m - 1), piVec m p k σ c :=
  Finset.sum_congr rfl fun c _ =>
    abs_of_nonneg (Finset.sum_nonneg fun j _ => le_of_lt (hp j))

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

lemma pairOf_update_mem_recur {m n : ℕ} (hm : 2 ≤ m) (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j)
    (i : Fin n) {DPt : Set (Pt m)} {σ₀ : Fin n → Fin m} (hmem : pairOf m p w i.val σ₀ ∈ DPt)
    (mach : Fin m) :
    pairOf m p w (i.val + 1) (Function.update σ₀ i mach) ∈ recur m p w i DPt := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hagree : ∀ j ∈ firstJobs n i.val, Function.update σ₀ i mach j = σ₀ j := by
    intro j hj
    have hj_ne : j ≠ i := fun heq => not_mem_firstJobs_self i (heq ▸ hj)
    exact Function.update_of_ne hj_ne _ _
  have hsi : Function.update σ₀ i mach i = mach := Function.update_self i mach σ₀
  unfold recur pairOf
  rw [piVec_succ_step, theta_succ_step, piVec_congr p i.val hagree, theta_congr p w i.val hagree]
  by_cases hlt : (Function.update σ₀ i mach i).val < m'
  · left
    let k0 : Fin m' := ⟨(Function.update σ₀ i mach i).val, hlt⟩
    refine ⟨pairOf (m' + 1) p w i.val σ₀, hmem, k0, ?_⟩
    simp only [hlt, ↓reduceDIte, pairOf]
    have hmach : Function.update σ₀ i mach i = @coordMachine (m' + 1) k0 := Fin.ext rfl
    have hload_congr :
        (firstJobs n i.val).filter (fun l => Function.update σ₀ i mach l = Function.update σ₀ i mach i) =
          (firstJobs n i.val).filter (fun l => σ₀ l = @coordMachine (m' + 1) k0) := by
      ext l
      simp only [mem_filter]
      exact ⟨fun ⟨hl, hs⟩ => ⟨hl, (hagree l hl).symm.trans (hs.trans hmach)⟩,
             fun ⟨hl, hs⟩ => ⟨hl, (hagree l hl).trans (hs.trans hmach.symm)⟩⟩
    rw [hload_congr]
    rfl
  · right
    refine ⟨pairOf (m' + 1) p w i.val σ₀, hmem, ?_⟩
    simp only [hlt, ↓reduceDIte, pairOf]
    have hlast : Function.update σ₀ i mach i = Fin.last m' := by
      apply Fin.ext
      change (Function.update σ₀ i mach i).val = m'
      have := (Function.update σ₀ i mach i).isLt
      omega
    have hload_congr :
        (firstJobs n i.val).filter (fun l => Function.update σ₀ i mach l = Function.update σ₀ i mach i) =
          (firstJobs n i.val).filter (fun l => σ₀ l = Fin.last m') := by
      ext l
      simp only [mem_filter, hlast]
      exact ⟨fun ⟨hl, hs⟩ => ⟨hl, (hagree l hl).symm.trans hs⟩,
             fun ⟨hl, hs⟩ => ⟨hl, (hagree l hl).trans hs⟩⟩
    rw [hload_congr, load_last_eq, sum_abs_piVec p hp]
    rfl

lemma combine_shift {n m : ℕ} (i : Fin n) (τ σ' : Fin n → Fin m) (mach : Fin m) :
    combine (i.val + 1) (Function.update τ i mach) σ' =
      combine i.val τ (Function.update σ' i mach) := by
  ext j
  unfold combine
  by_cases hj1 : j.val < i.val
  · have hj2 : j.val < i.val + 1 := Nat.lt_succ_of_lt hj1
    have hj_ne : j ≠ i := fun h => by subst h; omega
    simp [hj1, hj2, hj_ne]
  · by_cases hj2 : j.val < i.val + 1
    · have hjeq : j = i := Fin.ext (by omega)
      subst hjeq
      simp
    · have hj_ne : j ≠ i := fun h => by subst h; omega
      simp [hj1, hj2, hj_ne]

end Obs43Aux

theorem solution {m n : ℕ} (hm : 2 ≤ m) (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (hsort : Sorted p w) (i : Fin n) (δ : ℝ) (_hδ : 0 ≤ δ) (DPt : Set (Pt m))
    (hrep : IsRepSet m p w i.val δ DPt (DP m p w i.val)) :
    IsRepSet m p w (i.val + 1) δ (recur m p w i DPt) (DP m p w (i.val + 1)) := by
  refine ⟨?_, fun σ' σ _ => ?_⟩
  · rw [FasterWCTFPTAS.Main.lemma_4_1 hm p w hp hw hsort i]
    exact Obs43Aux.recur_mono p w i hrep.1
  · let σ'_ext : Fin n → Fin m := Function.update σ' i (σ i)
    obtain ⟨σt₀, hmem₀, hcost₀⟩ := hrep.2 σ'_ext σ ⟨σ, rfl⟩
    let σt : Fin n → Fin m := Function.update σt₀ i (σ i)
    refine ⟨σt, Obs43Aux.pairOf_update_mem_recur hm p w hp i hmem₀ (σ i), ?_⟩
    have hc1 : combine (i.val + 1) σt σ' = combine i.val σt₀ σ'_ext :=
      Obs43Aux.combine_shift i σt₀ σ' (σ i)
    have hc2 : combine (i.val + 1) σ σ' = combine i.val σ σ'_ext := by
      have hupd : Function.update σ i (σ i) = σ := Function.update_eq_self i σ
      simpa [hupd] using Obs43Aux.combine_shift i σ σ' (σ i)
    rw [hc1, hc2]
    exact hcost₀
