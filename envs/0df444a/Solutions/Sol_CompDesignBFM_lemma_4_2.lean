-- Prove2me | solution 1 for CompDesignBFM.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:50:27.015957+00:00
-- url     : https://prove2.me/submissions/a6c566fb-b142-424e-9974-f4c110970843

import Mathlib
import Definitions.Def_CompDesignBFM_Mechanism
import Definitions.Def_CompDesignBFM_util
import Definitions.Def_CompDesignBFM_singletonMech
import Definitions.Def_CompDesignBFM_M
import Definitions.Def_CompDesignBFM_IsGood

open CompDesignBFM

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (hB : 0 < B) (rho : Fin n → ℕ)
    (hrho : Function.Injective rho) :
    IsGood B (singletonMech v B rho) ∧
      (v ∅ = 0 → ∀ c : Fin n → ℝ, (∀ i, 0 ≤ c i) →
        v ((singletonMech v B rho).alloc c) = M v B c) := by
  classical
  -- the winning predicate
  let W : (Fin n → ℝ) → Fin n → Prop := fun b i =>
    b i ≤ B ∧ ∀ j, b j ≤ B → v {j} < v {i} ∨ (v {j} = v {i} ∧ rho i ≤ rho j)
  have hmem : ∀ b i, i ∈ (singletonMech v B rho).alloc b ↔ W b i := by
    intro b i
    simp [singletonMech, W]
  have hpay : ∀ b i, (singletonMech v B rho).pay b i = if W b i then B else 0 := by
    intro b i
    simp [singletonMech, W]
  have huniq : ∀ b i j, W b i → W b j → i = j := by
    intro b i j hi hj
    have h1 := hi.2 j hj.1
    have h2 := hj.2 i hi.1
    apply hrho
    rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
    · exact absurd h1 (not_lt.2 h2.le)
    · exact absurd h1 (by rw [h2]; exact lt_irrefl _)
    · exact absurd h2 (by rw [h1]; exact lt_irrefl _)
    · exact le_antisymm h1' h2'
  have hcard : ∀ b, ((singletonMech v B rho).alloc b).card ≤ 1 := by
    intro b
    apply Finset.card_le_one.2
    intro i hi j hj
    exact huniq b i j ((hmem b i).1 hi) ((hmem b j).1 hj)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- truthful
    intro i t z b ht hz hb
    have hu1 : ∀ b', i ∈ (singletonMech v B rho).alloc b' →
        util (singletonMech v B rho) i t b' = B - t := by
      intro b' h
      unfold util; rw [if_pos h, hpay, if_pos ((hmem b' i).1 h)]
    have hu0 : ∀ b', i ∉ (singletonMech v B rho).alloc b' →
        util (singletonMech v B rho) i t b' = 0 := by
      intro b' h
      unfold util; rw [if_neg h, hpay, if_neg (fun hw => h ((hmem b' i).2 hw))]
    by_cases hwz : i ∈ (singletonMech v B rho).alloc (Function.update b i z)
    · rw [hu1 _ hwz]
      by_cases htB : t ≤ B
      · have hwt : i ∈ (singletonMech v B rho).alloc (Function.update b i t) := by
          rw [hmem]
          have hw := (hmem _ _).1 hwz
          refine ⟨by simpa using htB, ?_⟩
          intro j hj
          by_cases hji : j = i
          · subst hji; right; exact ⟨rfl, le_rfl⟩
          · have hj' : Function.update b i z j ≤ B := by simpa [Function.update_of_ne hji] using hj
            have := hw.2 j hj'
            exact this
        rw [hu1 _ hwt]
      · push Not at htB
        rw [hu0 _ (fun h => absurd ((hmem _ _).1 h).1 (by simpa using not_le.2 htB))]
        linarith
    · rw [hu0 _ hwz]
      by_cases hwt : i ∈ (singletonMech v B rho).alloc (Function.update b i t)
      · rw [hu1 _ hwt]
        have := ((hmem _ _).1 hwt).1
        simp at this
        linarith
      · rw [hu0 _ hwt]
  · -- IR
    intro b hb i hi
    have hw := (hmem b i).1 hi
    rw [hpay, if_pos hw]; exact hw.1
  · -- pays winners only
    intro b hb i
    refine ⟨?_, ?_⟩
    · rw [hpay]; split_ifs <;> linarith
    · intro hi
      rw [hpay, if_neg (fun hw => hi ((hmem b i).2 hw))]
  · -- budget feasible
    intro b hb
    have : ∑ i ∈ (singletonMech v B rho).alloc b, (singletonMech v B rho).pay b i =
        ((singletonMech v B rho).alloc b).card * B := by
      rw [Finset.sum_congr rfl (g := fun _ => B)]
      · simp
      · intro i hi
        rw [hpay, if_pos ((hmem b i).1 hi)]
    rw [this]
    have h1 := hcard b
    have : (((singletonMech v B rho).alloc b).card : ℝ) ≤ 1 := by exact_mod_cast h1
    nlinarith
  · -- value
    intro hv0 c hc
    unfold M
    by_cases hne : (Finset.univ.filter fun i : Fin n => c i ≤ B).Nonempty
    · rw [dif_pos hne]
      obtain ⟨i0, hi0mem, hi0⟩ := Finset.exists_mem_eq_sup' hne (fun i => v {i})
      -- among maximisers choose the one of least priority
      have hne2 : (Finset.univ.filter fun i : Fin n =>
          c i ≤ B ∧ v {i} = (Finset.univ.filter fun i : Fin n => c i ≤ B).sup' hne fun i => v {i}).Nonempty :=
        ⟨i0, by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi0mem ⊢
                exact ⟨hi0mem, hi0.symm⟩⟩
      obtain ⟨i1, hi1mem, hi1min⟩ := Finset.exists_min_image _ rho hne2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi1mem
      have hWi1 : W c i1 := by
        refine ⟨hi1mem.1, ?_⟩
        intro j hj
        have hjle : v {j} ≤ v {i1} := by
          rw [hi1mem.2]
          exact Finset.le_sup' (fun i => v {i}) (by simpa using hj)
        rcases hjle.lt_or_eq with h | h
        · left; exact h
        · right
          refine ⟨h, hi1min j ?_⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hj, by rw [h]; exact hi1mem.2⟩
      have hall : (singletonMech v B rho).alloc c = {i1} := by
        apply Finset.eq_singleton_iff_unique_mem.2
        exact ⟨(hmem c i1).2 hWi1, fun j hj => huniq c j i1 ((hmem c j).1 hj) hWi1⟩
      rw [hall]
      simpa using hi1mem.2
    · rw [dif_neg hne]
      have : (singletonMech v B rho).alloc c = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro i hi
        exact hne ⟨i, by simpa using ((hmem c i).1 hi).1⟩
      rw [this]; exact hv0
