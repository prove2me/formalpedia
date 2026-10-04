-- Prove2me | solution 1 for Erdos20.erdos_rado_bound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T03:32:28.192137+00:00
-- url     : https://prove2.me/submissions/b4d70539-1401-467c-ab67-e3de9e956a88

import Mathlib
import Definitions.Def_Erdos20_defs

namespace Erdos20Aux

open Finset

variable {α : Type*} [DecidableEq α]

/-- A `k`-sunflower inside a finite family of finite sets. -/
def HasSunflower (F : Finset (Finset α)) (k : ℕ) : Prop :=
  ∃ G ⊆ F, G.card = k ∧ ∃ K : Finset α, ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K

omit [DecidableEq α] in
/-- A pairwise disjoint subfamily of maximal cardinality. -/
lemma exists_max_disjoint (F : Finset (Finset α)) :
    ∃ D ⊆ F, (D : Set (Finset α)).PairwiseDisjoint id ∧
      ∀ D' ⊆ F, (D' : Set (Finset α)).PairwiseDisjoint id → D'.card ≤ D.card := by
  classical
  let P := F.powerset.filter (fun D : Finset (Finset α) => (D : Set (Finset α)).PairwiseDisjoint id)
  have hne : P.Nonempty := ⟨∅, by simp [P]⟩
  obtain ⟨D, hD, hmax⟩ := Finset.exists_max_image P Finset.card hne
  simp only [P, Finset.mem_filter, Finset.mem_powerset] at hD
  refine ⟨D, hD.1, hD.2, fun D' h1 h2 => hmax D' ?_⟩
  simp [P, h1, h2]

/-- The Erdős–Rado Δ-system lemma: a family of more than `(k-1)^n n!` sets of size `n`
contains a `k`-sunflower. -/
theorem delta_system (k : ℕ) : ∀ n : ℕ, ∀ F : Finset (Finset α),
    (∀ A ∈ F, A.card = n) → (k - 1) ^ n * n.factorial < F.card → HasSunflower F k := by
  intro n
  induction n with
  | zero =>
    intro F hF hcard
    exfalso
    have hsub : F ⊆ {∅} := by
      intro A hA
      have := hF A hA
      simp [Finset.card_eq_zero.mp this]
    have h1 : F.card ≤ 1 := by simpa using Finset.card_le_card hsub
    have h2 : 1 < F.card := by simpa using hcard
    omega
  | succ n ih =>
    intro F hF hcard
    obtain ⟨D, hDF, hDdisj, hDmax⟩ := exists_max_disjoint F
    by_cases hk : k ≤ D.card
    · -- many pairwise disjoint sets: a sunflower with empty kernel
      obtain ⟨G, hGD, hGk⟩ := Finset.exists_subset_card_eq hk
      refine ⟨G, hGD.trans hDF, hGk, ∅, ?_⟩
      intro A hA B hB hAB
      have := hDdisj (hGD hA) (hGD hB) hAB
      exact Finset.disjoint_iff_inter_eq_empty.mp this
    · push Not at hk
      set U := D.biUnion id with hU
      have hUcard : U.card ≤ (k - 1) * (n + 1) := by
        calc U.card ≤ ∑ A ∈ D, (id A).card := Finset.card_biUnion_le
          _ = ∑ A ∈ D, (n + 1) := Finset.sum_congr rfl (fun A hA => hF A (hDF hA))
          _ = D.card * (n + 1) := by simp
          _ ≤ (k - 1) * (n + 1) := Nat.mul_le_mul_right _ (by omega)
      -- every member meets `U`
      have hmeet : ∀ A ∈ F, ∃ x, x ∈ U ∧ x ∈ A := by
        intro A hA
        by_contra hno
        push Not at hno
        have hAD : A ∉ D := by
          intro hAD
          have hAne : A.Nonempty := by
            rw [← Finset.card_pos, hF A hA]; omega
          obtain ⟨x, hx⟩ := hAne
          exact hno x (Finset.mem_biUnion.mpr ⟨A, hAD, hx⟩) hx
        have hdisj : (↑(insert A D) : Set (Finset α)).PairwiseDisjoint id := by
          rw [Finset.coe_insert]
          refine hDdisj.insert fun B hB _ => ?_
          change Disjoint A B
          rw [Finset.disjoint_left]
          intro y hyA hyB
          exact hno y (Finset.mem_biUnion.mpr ⟨B, hB, hyB⟩) hyA
        have := hDmax (insert A D) (Finset.insert_subset hA hDF) hdisj
        rw [Finset.card_insert_of_notMem hAD] at this
        omega
      have hcover : F ⊆ U.biUnion (fun x => F.filter (fun A => x ∈ A)) := by
        intro A hA
        obtain ⟨x, hxU, hxA⟩ := hmeet A hA
        exact Finset.mem_biUnion.mpr ⟨x, hxU, Finset.mem_filter.mpr ⟨hA, hxA⟩⟩
      -- pigeonhole: some point of `U` lies in many members
      obtain ⟨x, hxU, hxbig⟩ : ∃ x ∈ U,
          (k - 1) ^ n * n.factorial < (F.filter (fun A => x ∈ A)).card := by
        by_contra hno
        push Not at hno
        have h1 : F.card ≤ ∑ x ∈ U, (F.filter (fun A => x ∈ A)).card :=
          (Finset.card_le_card hcover).trans Finset.card_biUnion_le
        have h2 : ∑ x ∈ U, (F.filter (fun A => x ∈ A)).card ≤
            ∑ x ∈ U, (k - 1) ^ n * n.factorial := Finset.sum_le_sum hno
        rw [Finset.sum_const, smul_eq_mul] at h2
        have h3 : U.card * ((k - 1) ^ n * n.factorial) ≤
            (k - 1) * (n + 1) * ((k - 1) ^ n * n.factorial) :=
          Nat.mul_le_mul_right _ hUcard
        have h4 : (k - 1) * (n + 1) * ((k - 1) ^ n * n.factorial) =
            (k - 1) ^ (n + 1) * (n + 1).factorial := by
          rw [Nat.factorial_succ, pow_succ]; ring
        have h5 : F.card ≤ (k - 1) ^ (n + 1) * (n + 1).factorial :=
          h1.trans (h2.trans (h3.trans h4.le))
        exact Nat.lt_irrefl _ (lt_of_lt_of_le hcard h5)
      -- delete `x` and apply induction
      set Fx := F.filter (fun A => x ∈ A) with hFx
      set F' := Fx.image (fun A => A.erase x) with hF'
      have hinj : Set.InjOn (fun A : Finset α => A.erase x) Fx := by
        intro A hA B hB hAB
        have hxA : x ∈ A := (Finset.mem_filter.mp hA).2
        have hxB : x ∈ B := (Finset.mem_filter.mp hB).2
        have := congrArg (insert x) hAB
        simpa [Finset.insert_erase hxA, Finset.insert_erase hxB] using this
      have hF'card : F'.card = Fx.card := Finset.card_image_of_injOn hinj
      have hF'mem : ∀ B ∈ F', B.card = n := by
        intro B hB
        obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
        have hxA : x ∈ A := (Finset.mem_filter.mp hA).2
        rw [Finset.card_erase_of_mem hxA, hF A (Finset.mem_filter.mp hA).1]
        rfl
      have hF'notmem : ∀ B ∈ F', x ∉ B := by
        intro B hB
        obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
        exact Finset.notMem_erase x A
      obtain ⟨G', hG'F', hG'k, K', hK'⟩ := ih F' hF'mem (by rw [hF'card]; exact hxbig)
      refine ⟨G'.image (insert x), ?_, ?_, insert x K', ?_⟩
      · intro A hA
        obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
        obtain ⟨A0, hA0, rfl⟩ := Finset.mem_image.mp (hG'F' hB)
        have hxA : x ∈ A0 := (Finset.mem_filter.mp hA0).2
        rw [Finset.insert_erase hxA]
        exact (Finset.mem_filter.mp hA0).1
      · rw [Finset.card_image_of_injOn, hG'k]
        intro B1 hB1 B2 hB2 h
        have hx1 : x ∉ B1 := hF'notmem B1 (hG'F' hB1)
        have hx2 : x ∉ B2 := hF'notmem B2 (hG'F' hB2)
        have := congrArg (fun C => C.erase x) h
        simpa [Finset.erase_insert hx1, Finset.erase_insert hx2] using this
      · intro A hA B hB hAB
        obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
        obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hB
        have hne : A' ≠ B' := fun h => hAB (by rw [h])
        have hy := hK' A' hA' B' hB' hne
        ext y
        have hy' := Finset.ext_iff.mp hy y
        simp only [Finset.mem_inter, Finset.mem_insert] at hy' ⊢
        tauto

end Erdos20Aux

/-- The Erdős–Rado bound `f(n, k) ≤ (k-1)^n n! + 1`. -/
theorem solution :
    ∀ n k, n > 0 → 2 ≤ k → Erdos20.f n k ≤ (k - 1) ^ n * n.factorial + 1 := by
  intro n k hn hk
  classical
  unfold Erdos20.f
  apply Nat.sInf_le
  intro α F hFm
  obtain ⟨hF, hm⟩ := hFm
  have hFpos : 0 < F.ncard := by omega
  have hFfin : F.Finite := Set.finite_of_ncard_pos hFpos
  have hAfin : ∀ A ∈ F, A.Finite := fun A hA =>
    Set.finite_of_ncard_pos (by rw [hF A hA]; exact hn)
  let toF : Set α → Finset α := fun A => if h : A.Finite then h.toFinset else ∅
  have htoF : ∀ A, A.Finite → (toF A : Set α) = A := by
    intro A h
    simp [toF, h]
  let F' : Finset (Finset α) := hFfin.toFinset.image toF
  have hinj : Set.InjOn toF F := fun A hA B hB h => by
    rw [← htoF A (hAfin A hA), ← htoF B (hAfin B hB), h]
  have hF'card : F'.card = F.ncard := by
    rw [Finset.card_image_of_injOn (by simpa using hinj), Set.ncard_eq_toFinset_card F hFfin]
  have hmem : ∀ B ∈ F', B.card = n := by
    intro B hB
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
    have hA' : A ∈ F := hFfin.mem_toFinset.mp hA
    have := hF A hA'
    rw [← htoF A (hAfin A hA'), Set.ncard_coe_finset] at this
    exact this
  obtain ⟨G', hG'F', hG'k, K', hK'⟩ :=
    Erdos20Aux.delta_system k n F' hmem (by rw [hF'card]; omega)
  refine ⟨(fun B : Finset α => (B : Set α)) '' (G' : Set (Finset α)), ?_, ?_, ?_⟩
  · rintro _ ⟨B, hB, rfl⟩
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp (hG'F' hB)
    have hA' : A ∈ F := hFfin.mem_toFinset.mp hA
    show ((toF A : Finset α) : Set α) ∈ F
    rw [htoF A (hAfin A hA')]
    exact hA'
  · rw [Set.ncard_image_of_injective _ Finset.coe_injective, Set.ncard_coe_finset, hG'k]
  · refine ⟨(K' : Set α), ?_⟩
    unfold Erdos20.IsSunflowerWithKernel
    rintro _ ⟨B1, hB1, rfl⟩ _ ⟨B2, hB2, rfl⟩ hne
    have : B1 ≠ B2 := fun h => hne (by rw [h])
    rw [← Finset.coe_inter, hK' B1 hB1 B2 hB2 this]
