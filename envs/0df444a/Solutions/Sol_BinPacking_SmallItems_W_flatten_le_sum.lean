-- Prove2me | solution 1 for BinPacking.SmallItems.W_flatten_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:43:24.68756+00:00
-- url     : https://prove2.me/submissions/4005019f-1704-456e-8f65-d17298c325ba

import Mathlib
import Definitions.Def_BinPacking_SmallItems_Model
import Definitions.Def_BinPacking_SmallItems_Weight

namespace BinPacking.SmallItems

lemma aux_wfl_card (L : List ℝ) (r : ℝ) :
    Fintype.card {i : Fin L.length // L.get i = r} = L.count r := by
  rw [Fintype.card_subtype]
  have h1 : (Finset.univ.val.map L.get).count r =
      (Finset.univ.filter (fun i : Fin L.length => L.get i = r)).card := by
    rw [Multiset.count_map]
    simp only [Finset.card, Finset.filter_val]
    congr 1
    apply Multiset.filter_congr
    intro x _
    exact eq_comm
  rw [← h1, Fin.univ_val_map, List.ofFn_get, Multiset.coe_count]

lemma aux_wfl_equiv {α β : Type} [Fintype α] [Fintype β] (f : α → ℝ) (g : β → ℝ)
    (h : ∀ r, Fintype.card {a // f a = r} = Fintype.card {b // g b = r}) :
    ∃ e : α ≃ β, ∀ a, g (e a) = f a :=
  ⟨Equiv.ofFiberEquiv (fun r => Fintype.equivOfCardEq (h r)),
    fun a => Equiv.ofFiberEquiv_map _ a⟩

lemma aux_wfl_card_eq_sum {α : Type} [Fintype α] (f : α → ℝ) (r : ℝ) :
    Fintype.card {a // f a = r} = ∑ a, if f a = r then 1 else 0 := by
  rw [Fintype.card_subtype, Finset.card_filter]

/-- symmetric version of `w2` -/
noncomputable def aux_wfl_w2s (x y : ℝ) : ℝ := if y ≤ x then w2 x y else w2 y x

lemma aux_wfl_w2s_comm (x y : ℝ) : aux_wfl_w2s x y = aux_wfl_w2s y x := by
  unfold aux_wfl_w2s
  by_cases h1 : y ≤ x <;> by_cases h2 : x ≤ y
  · have : x = y := le_antisymm h2 h1
    subst this; simp
  · simp [h1, h2]
  · simp [h1, h2]
  · exact absurd (le_of_lt (lt_of_not_ge h1)) h2

/-- symmetric cost of an involution -/
noncomputable def aux_wfl_C {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℝ)
    (σ : Equiv.Perm ι) : ℝ :=
  ∑ i, (if σ i = i then w1 (v i) else aux_wfl_w2s (v i) (v (σ i)) / 2)

lemma aux_wfl_C_reindex {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (v : β → ℝ) (σ : Equiv.Perm β) :
    aux_wfl_C (v ∘ e) ((e.trans σ).trans e.symm) = aux_wfl_C v σ := by
  unfold aux_wfl_C
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Equiv.trans_apply, Function.comp_apply, Equiv.apply_symm_apply]
  simp only [Equiv.symm_apply_eq]

lemma aux_wfl_C_sum {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (v : α → ℝ) (u : β → ℝ) (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    aux_wfl_C (Sum.elim v u) (Equiv.sumCongr σ τ) = aux_wfl_C v σ + aux_wfl_C u τ := by
  unfold aux_wfl_C
  rw [Fintype.sum_sum_type]
  simp

lemma aux_wfl_w12_eq (S : List ℝ) (hS : S.Pairwise (fun a b => b ≤ a))
    (σ : Equiv.Perm (Fin S.length)) (hσ : σ * σ = 1) :
    w12 S σ = aux_wfl_C S.get σ := by
  have hinv : ∀ i, σ (σ i) = i := by
    intro i
    have := congrArg (fun p : Equiv.Perm (Fin S.length) => p i) hσ
    simpa using this
  unfold w12 aux_wfl_C
  rw [Finset.sum_filter, Finset.sum_filter]
  -- split C into three parts
  have hsplit : ∀ i : Fin S.length,
      (if σ i = i then w1 (S.get i) else aux_wfl_w2s (S.get i) (S.get (σ i)) / 2) =
        (if σ i = i then w1 (S.get i) else 0) +
        (if i < σ i then aux_wfl_w2s (S.get i) (S.get (σ i)) / 2 else 0) +
        (if σ i < i then aux_wfl_w2s (S.get i) (S.get (σ i)) / 2 else 0) := by
    intro i
    rcases lt_trichotomy i (σ i) with h | h | h
    · have h1 : σ i ≠ i := ne_of_gt h
      have h2 : ¬ σ i < i := not_lt_of_gt h
      simp [h, h1, h2]
    · have h1 : ¬ i < σ i := by rw [← h]; exact lt_irrefl _
      simp [← h]
    · have h1 : σ i ≠ i := ne_of_lt h
      have h2 : ¬ i < σ i := not_lt_of_gt h
      simp [h, h1, h2]
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hre : (∑ i : Fin S.length,
      (if σ i < i then aux_wfl_w2s (S.get i) (S.get (σ i)) / 2 else 0)) =
      ∑ i : Fin S.length,
      (if i < σ i then aux_wfl_w2s (S.get i) (S.get (σ i)) / 2 else 0) := by
    rw [← Equiv.sum_comp σ]
    apply Finset.sum_congr rfl
    intro i _
    rw [hinv i, aux_wfl_w2s_comm]
  rw [hre, add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i < σ i
  · have hle : S.get (σ i) ≤ S.get i := hS.rel_get_of_lt h
    simp only [h, if_true, aux_wfl_w2s, hle]
    ring
  · simp [h]

lemma aux_wfl_sorted (L : List ℝ) : (sortDesc L).Pairwise (fun a b => b ≤ a) := by
  have := List.pairwise_mergeSort (le := fun a b : ℝ => decide (b ≤ a))
    (by intro a b c h1 h2; simp only [decide_eq_true_eq] at *; linarith)
    (by intro a b; simpa using le_total b a) L
  unfold sortDesc
  simpa using this

lemma aux_wfl_exists (X : List ℝ) :
    ∃ σ ∈ pairings (sortDesc X).length, W X = w12 (sortDesc X) σ := by
  unfold W
  exact Finset.exists_mem_eq_inf' _ _

lemma aux_wfl_inv {α β : Type} (e : α ≃ β) (τ : Equiv.Perm β) (hτ : τ * τ = 1) :
    ((e.trans τ).trans e.symm) * ((e.trans τ).trans e.symm) = 1 := by
  have hinv : ∀ b, τ (τ b) = b := by
    intro b
    have := congrArg (fun p : Equiv.Perm β => p b) hτ
    simpa using this
  ext a
  simp [hinv]

lemma aux_wfl_card_sum {α β : Type} [Fintype α] [Fintype β] (v : α → ℝ) (u : β → ℝ)
    (r : ℝ) : Fintype.card {x // Sum.elim v u x = r} =
      Fintype.card {a // v a = r} + Fintype.card {b // u b = r} := by
  rw [aux_wfl_card_eq_sum, aux_wfl_card_eq_sum, aux_wfl_card_eq_sum, Fintype.sum_sum_type]
  rfl

lemma aux_wfl_glue (S SA SB : List ℝ) (hS : S.Pairwise (fun a b => b ≤ a))
    (hSA : SA.Pairwise (fun a b => b ≤ a)) (hSB : SB.Pairwise (fun a b => b ≤ a))
    (hcount : ∀ r, S.count r = SA.count r + SB.count r)
    (σA : Equiv.Perm (Fin SA.length)) (hσA : σA * σA = 1)
    (σB : Equiv.Perm (Fin SB.length)) (hσB : σB * σB = 1) :
    ∃ σ : Equiv.Perm (Fin S.length), σ * σ = 1 ∧ w12 S σ = w12 SA σA + w12 SB σB := by
  obtain ⟨e, he⟩ := aux_wfl_equiv (S.get) (Sum.elim SA.get SB.get) (by
    intro r
    rw [aux_wfl_card_sum, aux_wfl_card, aux_wfl_card, aux_wfl_card, hcount])
  let τ : Equiv.Perm (Fin SA.length ⊕ Fin SB.length) := Equiv.sumCongr σA σB
  have hτinv : τ * τ = 1 := by
    show Equiv.sumCongr σA σB * Equiv.sumCongr σA σB = 1
    rw [Equiv.Perm.sumCongr_mul, hσA, hσB, Equiv.Perm.sumCongr_one]
  refine ⟨(e.trans τ).trans e.symm, aux_wfl_inv e τ hτinv, ?_⟩
  have hSget : S.get = (Sum.elim SA.get SB.get) ∘ e := by
    funext i; exact (he i).symm
  rw [aux_wfl_w12_eq S hS _ (aux_wfl_inv e τ hτinv),
    aux_wfl_w12_eq SA hSA σA hσA, aux_wfl_w12_eq SB hSB σB hσB, ← aux_wfl_C_sum]
  have := aux_wfl_C_reindex e (Sum.elim SA.get SB.get) τ
  rw [← hSget] at this
  exact this

lemma aux_wfl_append (A B : List ℝ) : W (A ++ B) ≤ W A + W B := by
  obtain ⟨σA, hσAm, hA⟩ := aux_wfl_exists A
  obtain ⟨σB, hσBm, hB⟩ := aux_wfl_exists B
  have hσA : σA * σA = 1 := by simpa [pairings] using hσAm
  have hσB : σB * σB = 1 := by simpa [pairings] using hσBm
  obtain ⟨σ, hσ, hval⟩ := aux_wfl_glue (sortDesc (A ++ B)) (sortDesc A) (sortDesc B)
    (aux_wfl_sorted _) (aux_wfl_sorted _) (aux_wfl_sorted _) (by
      intro r
      rw [sortDesc, sortDesc, sortDesc, (List.mergeSort_perm _ _).count_eq,
        (List.mergeSort_perm _ _).count_eq, (List.mergeSort_perm _ _).count_eq,
        List.count_append]) σA hσA σB hσB
  have hmem : σ ∈ pairings (sortDesc (A ++ B)).length := by simp [pairings, hσ]
  have hle : W (A ++ B) ≤ w12 (sortDesc (A ++ B)) σ := by
    unfold W
    exact Finset.inf'_le _ hmem
  rw [hA, hB, ← hval]
  exact hle

lemma aux_wfl_nil : W [] ≤ 0 := by
  obtain ⟨σ, _, h⟩ := aux_wfl_exists []
  rw [h]
  have : IsEmpty (Fin (sortDesc ([] : List ℝ)).length) := by
    simp [sortDesc]; infer_instance
  simp [w12, Finset.univ_eq_empty]

end BinPacking.SmallItems

open BinPacking.SmallItems

theorem solution (Xs : List (List ℝ)) (hL : IsList Xs.flatten) :
    W Xs.flatten ≤ (Xs.map W).sum := by
  clear hL
  induction Xs with
  | nil => simpa using aux_wfl_nil
  | cons X Xs ih =>
    rw [List.flatten_cons, List.map_cons, List.sum_cons]
    exact (aux_wfl_append X Xs.flatten).trans (by linarith)
