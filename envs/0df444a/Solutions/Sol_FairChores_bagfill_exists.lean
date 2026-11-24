-- Prove2me | solution 1 for FairChores.bagfill_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:27:29.319819+00:00
-- url     : https://prove2.me/submissions/eadc75b9-3600-49f9-b45e-593a88b203cb

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresBagLemma
import Definitions.Def_RequestProject_ChoresBagFilling
import Theorems.Thm_FairChores_wtSum_eq_price_sum
import Theorems.Thm_FairChores_equal_share_le_of_le_nsmul
import Theorems.Thm_FairChores_equal_share_le_three_halves
import Theorems.Thm_FairChores_PreAlloc_bundle_subset
import Theorems.Thm_FairChores_PreAlloc_outs_subset
import Theorems.Thm_FairChores_bag_lemma
import Theorems.Thm_FairChores_cbarSum_empty
import Theorems.Thm_FairChores_cbarSum_le_wtSum
import Theorems.Thm_FairChores_single_le_cbarSum
import Theorems.Thm_FairChores_wtSum_nonneg
import Theorems.Thm_FairChores_wtSum_sdiff
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {c : Fin n → T → ℝ} {p : T → ℝ} {mu : Fin n → ℝ}
omit [Fintype T]
namespace FairChores
theorem _root_.solution (hc : ∀ i t, 0 ≤ c i t) (hp : ∀ t, 0 ≤ p t) (hmu : ∀ i, 0 < mu i) :
    ∀ (k : ℕ) (A : Finset (Fin n)) (R : Finset T), A.card = k → A.Nonempty →
      (∀ i ∈ A, Inv c p mu i A.card R) →
      ∃ P : PreAlloc T n, P.Splits p A R ∧
        ∀ i ∈ A, cbarSum (c i) p (P.bundle i) + P.share i ≤ 2 * mu i := by
  classical
  intro k
  induction k with
  | zero =>
    intro A R hcard hA _
    exact absurd hcard (by simpa using Finset.card_ne_zero_of_mem hA.choose_spec)
  | succ k ih =>
    intro A R hcard hA hinv
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- a single active agent: it takes all the remaining chores
      subst hk0
      obtain ⟨i0, hi0⟩ := Finset.card_eq_one.mp hcard
      refine ⟨⟨fun j => if j = i0 then R else ∅, ∅, fun _ => 0⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro i hi
        have : i ≠ i0 := by rintro rfl; exact hi (by simp [hi0])
        simp [this]
      · intro i _; rfl
      · intro i; exact le_rfl
      · intro i j hij
        by_cases hi : i = i0 <;> by_cases hj : j = i0 <;> simp [hi, hj]
        exact absurd (hi.trans hj.symm) hij
      · intro i; simp
      · simp only [Finset.empty_union]
        ext s
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨j, hj⟩
          by_cases hji : j = i0
          · simpa [hji] using hj
          · simp [hji] at hj
        · intro hs; exact ⟨i0, by simp [hs]⟩
      · simp
      · intro i hi
        have hii0 : i = i0 := by simpa [hi0] using hi
        subst hii0
        have hmi := hmu i
        have hcw : cbarSum (c i) p R ≤ wtSum (c i) p (mu i) R := cbarSum_le_wtSum R
        rcases hinv i hi with h | ⟨h, -⟩ <;> rw [hcard] at h <;> push_cast at h <;> simp <;>
          linarith
    · -- at least two active agents: one round of bag-filling
      have hcardpos : 0 < A.card := by omega
      rcases bag_lemma hc hp hmu hA R with hexp | ⟨B, hBR, hBne, i, hiA, hiB, hother⟩
      · -- all remaining chores are very expensive: outsource them and share the bill
        refine ⟨⟨fun _ => ∅, R, fun j => if j ∈ A then (∑ t ∈ R, p t) / A.card else 0⟩,
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · intro i _; rfl
        · intro i hi; simp [hi]
        · intro i
          by_cases hi : i ∈ A
          · have h1 : (0:ℝ) ≤ ∑ t ∈ R, p t := Finset.sum_nonneg fun t _ => hp t
            have h2 : (0:ℝ) < A.card := by exact_mod_cast hcardpos
            simp only [hi, if_true]
            positivity
          · simp [hi]
        · intro i j _; simp
        · intro i; simp
        · simp
        · rw [Finset.sum_ite_mem]
          simp only [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
          field_simp
        · intro j hjA
          have hexpj : ∀ t ∈ R, mu j < cbar (c j) p t := fun t ht =>
            lt_of_le_of_lt (by linarith [hmu j]) (hexp j hjA t ht)
          have hwt : wtSum (c j) p (mu j) R = ∑ t ∈ R, p t := wtSum_eq_price_sum hexpj
          simp only [hjA, if_true, cbarSum_empty, zero_add]
          have hmuj := hmu j
          rcases hinv j hjA with h | ⟨h, -⟩ <;> rw [hwt] at h
          · have := equal_share_le_of_le_nsmul (W := ∑ t ∈ R, p t) (m := mu j) hcardpos h
            linarith
          · have hk2 : 2 ≤ A.card := by omega
            have := equal_share_le_three_halves (W := ∑ t ∈ R, p t) (m := mu j) hk2
              (le_of_lt hmuj) (by linarith)
            linarith
      · -- the bag `B` goes to agent `i`; recurse on the remaining agents and chores
        set A' := A.erase i with hA'
        set R' := R \ B with hR'
        have hcardA' : A'.card = k := by
          rw [hA', Finset.card_erase_of_mem hiA, hcard]
          omega
        have hA'ne : A'.Nonempty := by
          rw [← Finset.card_pos, hcardA']; omega
        have hinv' : ∀ j ∈ A', Inv c p mu j A'.card R' := by
          intro j hjA'
          have hjA : j ∈ A := Finset.mem_of_mem_erase hjA'
          have hji : j ≠ i := Finset.ne_of_mem_erase hjA'
          have hsplitw : wtSum (c j) p (mu j) R
              = wtSum (c j) p (mu j) R' + wtSum (c j) p (mu j) B := wtSum_sdiff hBR
          have hwB : cbarSum (c j) p B ≤ wtSum (c j) p (mu j) B := cbarSum_le_wtSum B
          have hwR' : (0:ℝ) ≤ wtSum (c j) p (mu j) R' := wtSum_nonneg (hc j) hp _
          have hcardcast : (A'.card : ℝ) = (A.card : ℝ) - 1 := by
            rw [hcardA', hcard]; push_cast; ring
          rcases hinv j hjA with hI1 | ⟨hI2, hI2exp⟩
          · rcases hother j hjA hji with hbig | hfar
            · left
              rw [hcardcast]
              have : wtSum (c j) p (mu j) R' ≤ wtSum (c j) p (mu j) R - mu j := by
                rw [hsplitw]; linarith
              have hcardA : (A.card : ℝ) = (k:ℝ) + 1 := by rw [hcard]; push_cast; ring
              rw [hcardA] at hI1 ⊢
              nlinarith
            · right
              refine ⟨?_, hfar⟩
              have hle : wtSum (c j) p (mu j) R' ≤ wtSum (c j) p (mu j) R := by
                rw [hsplitw]
                have : (0:ℝ) ≤ wtSum (c j) p (mu j) B := wtSum_nonneg (hc j) hp _
                linarith
              rw [hcardcast]
              have hcardA : (A.card : ℝ) = (k:ℝ) + 1 := by rw [hcard]; push_cast; ring
              rw [hcardA] at hI1
              rw [hcardA]
              nlinarith
          · -- the agent was already in the violated state: `B` is costly for it
            obtain ⟨t, htB⟩ := hBne
            have hbig : mu j ≤ cbarSum (c j) p B := by
              have h1 : mu j < cbar (c j) p t := hI2exp t (hBR htB)
              have h2 : cbar (c j) p t ≤ cbarSum (c j) p B :=
                single_le_cbarSum (hc j) hp htB
              linarith
            right
            refine ⟨?_, fun s hs => hI2exp s (Finset.mem_sdiff.mp hs).1⟩
            have hcardA : (A.card : ℝ) = (k:ℝ) + 1 := by rw [hcard]; push_cast; ring
            rw [hcardA] at hI2
            rw [hcardcast, hcardA]
            have : wtSum (c j) p (mu j) R' ≤ wtSum (c j) p (mu j) R - mu j := by
              rw [hsplitw]; linarith
            nlinarith
        obtain ⟨P', hP', hcost'⟩ := ih A' R' hcardA' hA'ne hinv'
        have hbi : P'.bundle i = ∅ := hP'.1 i (by simp [hA'])
        have hsi : P'.share i = 0 := hP'.2.1 i (by simp [hA'])
        have hbsub : ∀ j, P'.bundle j ⊆ R' := fun j => PreAlloc.bundle_subset hP' j
        have hosub : P'.outs ⊆ R' := PreAlloc.outs_subset hP'
        have hdisjB : ∀ j, Disjoint B (P'.bundle j) := by
          intro j
          refine Finset.disjoint_left.mpr fun s hs hs' => ?_
          have := hbsub j hs'
          rw [hR'] at this
          exact (Finset.mem_sdiff.mp this).2 hs
        have hdisjBo : Disjoint P'.outs B := by
          refine Finset.disjoint_left.mpr fun s hs hs' => ?_
          have := hosub hs
          rw [hR'] at this
          exact (Finset.mem_sdiff.mp this).2 hs'
        refine ⟨⟨Function.update P'.bundle i B, P'.outs, Function.update P'.share i 0⟩,
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · intro j hj
          have hji : j ≠ i := by rintro rfl; exact hj hiA
          dsimp only
          rw [Function.update_of_ne hji]
          exact hP'.1 j (fun h => hj (Finset.mem_of_mem_erase h))
        · intro j hj
          have hji : j ≠ i := by rintro rfl; exact hj hiA
          dsimp only
          rw [Function.update_of_ne hji]
          exact hP'.2.1 j (fun h => hj (Finset.mem_of_mem_erase h))
        · intro j
          dsimp only
          by_cases hji : j = i
          · subst hji; simp
          · rw [Function.update_of_ne hji]; exact hP'.2.2.1 j
        · intro j l hjl
          dsimp only
          by_cases hji : j = i
          · subst hji
            rw [Function.update_self, Function.update_of_ne (Ne.symm hjl)]
            exact hdisjB l
          · by_cases hli : l = i
            · subst hli
              rw [Function.update_self, Function.update_of_ne hji]
              exact (hdisjB j).symm
            · rw [Function.update_of_ne hji, Function.update_of_ne hli]
              exact hP'.2.2.2.1 j l hjl
        · intro j
          dsimp only
          by_cases hji : j = i
          · subst hji; rw [Function.update_self]; exact hdisjBo
          · rw [Function.update_of_ne hji]; exact hP'.2.2.2.2.1 j
        · dsimp only
          have hbU : Finset.univ.biUnion (Function.update P'.bundle i B)
              = B ∪ Finset.univ.biUnion P'.bundle := by
            ext s
            simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨j, hj⟩
              by_cases hji : j = i
              · subst hji; rw [Function.update_self] at hj; exact Or.inl hj
              · rw [Function.update_of_ne hji] at hj; exact Or.inr ⟨j, hj⟩
            · rintro (h | ⟨j, hj⟩)
              · exact ⟨i, by rwa [Function.update_self]⟩
              · by_cases hji : j = i
                · subst hji; rw [hbi] at hj; exact absurd hj (Finset.notMem_empty s)
                · exact ⟨j, by rwa [Function.update_of_ne hji]⟩
          rw [hbU]
          have hassoc : P'.outs ∪ (B ∪ Finset.univ.biUnion P'.bundle)
              = (P'.outs ∪ Finset.univ.biUnion P'.bundle) ∪ B := by
            ext s
            simp only [Finset.mem_union]
            tauto
          rw [hassoc, hP'.2.2.2.2.2.1, hR']
          exact Finset.sdiff_union_of_subset hBR
        · dsimp only
          rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
          have := hP'.2.2.2.2.2.2
          have hsum : ∑ x ∈ Finset.univ, P'.share x = (∑ x ∈ Finset.univ \ {i}, P'.share x) + P'.share i := by
            rw [← Finset.erase_eq, add_comm, Finset.add_sum_erase _ _ (Finset.mem_univ i)]
          rw [hsum, hsi] at this
          simpa using this
        · intro j hjA
          dsimp only
          by_cases hji : j = i
          · subst hji
            rw [Function.update_self, Function.update_self]
            linarith
          · rw [Function.update_of_ne hji, Function.update_of_ne hji]
            exact hcost' j (Finset.mem_erase.mpr ⟨hji, hjA⟩)
end FairChores
