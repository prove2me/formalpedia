-- Prove2me | solution 1 for EvenCycleTuran.EvenCount.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-31T08:11:11.199736+00:00
-- url     : https://prove2.me/submissions/e6fa5480-b1ab-4c51-9bf3-6592f653e78a

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenCount_Setting

section

open Finset SimpleGraph
namespace EvenCycleTuran.EvenCount.Fresh

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def rectCount (A B : Finset V) : ℕ :=
  ∑ v ∈ A, ∑ w ∈ B, if G.Adj v w then 1 else 0

omit [Fintype V] [DecidableEq V] in
lemma rectCount_symm (A B : Finset V) : rectCount G A B = rectCount G B A := by
  unfold rectCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro v hv
  simp only [G.adj_comm]

lemma rectCount_add_compl_right (A B : Finset V) :
    rectCount G A B + rectCount G A (univ \ B) = rectCount G A univ := by
  unfold rectCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  exact Finset.sum_add_sum_compl B _

lemma rectCount_add_compl_left (A B : Finset V) :
    rectCount G A B + rectCount G (univ \ A) B = rectCount G univ B := by
  rw [rectCount_symm G A B, rectCount_symm G (univ \ A) B,
    rectCount_symm G univ B]
  exact rectCount_add_compl_right G B A

omit [DecidableEq V] in
lemma rectCount_univ_right (A : Finset V) :
    rectCount G A univ = ∑ v ∈ A, G.degree v := by
  unfold rectCount
  apply Finset.sum_congr rfl
  intro v hv
  simp [← G.card_neighborFinset_eq_degree v, SimpleGraph.neighborFinset]

omit [DecidableEq V] in
lemma rectCount_univ : rectCount G univ univ = 2 * G.edgeFinset.card := by
  rw [rectCount_univ_right, G.sum_degrees_eq_twice_card_edges]

lemma rectCount_partition (S : Finset V) :
    rectCount G univ univ = rectCount G (univ \ S) (univ \ S) +
      (∑ v ∈ S, G.degree v) + rectCount G S (univ \ S) := by
  have h₁ := rectCount_add_compl_left G S univ
  have h₂ := rectCount_add_compl_right G (univ \ S) S
  rw [rectCount_univ_right] at h₁
  rw [rectCount_symm G (univ \ S) S] at h₂
  omega

omit [Fintype V] [DecidableEq V] in
lemma rectCount_le_card_mul (A B : Finset V) :
    rectCount G A B ≤ A.card * B.card := by
  unfold rectCount
  calc
    _ ≤ ∑ _v ∈ A, ∑ _w ∈ B, 1 := by
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.sum_le_sum
      intro w hw
      split_ifs <;> omega
    _ = _ := by simp

end EvenCycleTuran.EvenCount.Fresh
end

section

open Finset SimpleGraph
namespace EvenCycleTuran.EvenCount.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
lemma rectCount_induce (C : Finset V) :
    rectCount G C C = 2 * (G.induce (C : Set V)).edgeFinset.card := by
  rw [← rectCount_univ (G.induce (C : Set V))]
  unfold rectCount
  change (∑ v ∈ C, ∑ w ∈ C, if G.Adj v w then 1 else 0) =
    ∑ v : C, ∑ w : C, if G.Adj v.1 w.1 then 1 else 0
  rw [← Finset.sum_coe_sort C (fun v => ∑ w ∈ C, if G.Adj v w then 1 else 0)]
  apply Finset.sum_congr rfl
  intro v hv
  exact (Finset.sum_coe_sort C (fun w => if G.Adj v.1 w then 1 else 0)).symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma free_induce (H : SimpleGraph ℕ) (h : H.Free G) (C : Set V) :
    H.Free (G.induce C) := by
  intro hc
  exact h (hc.trans ⟨SimpleGraph.Copy.induce G C⟩)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma cycle_free_induce (k : ℕ)
    (h : ∀ a : ℕ, k < a → (cycleGraph a).Free G) (C : Set V) :
    ∀ a : ℕ, k < a → (cycleGraph a).Free (G.induce C) := by
  intro a ha hc
  exact h a ha (hc.trans ⟨SimpleGraph.Copy.induce G C⟩)

lemma complement_card (S : Finset V) :
    Fintype.card ↥(↑(univ \ S) : Set V) = Fintype.card V - S.card := by
  change Fintype.card ↥(univ \ S) = _
  rw [Fintype.card_coe]
  simpa only [Finset.card_univ] using Finset.card_sdiff_of_subset (Finset.subset_univ S)

end EvenCycleTuran.EvenCount.Fresh
end

section

open Finset SimpleGraph
namespace EvenCycleTuran.EvenCount.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma rectCount_localized (S X : Finset V)
    (hloc : ∀ v ∈ S, ∀ w, G.Adj v w → w ∈ X) :
    rectCount G S (univ \ S) = rectCount G S (X \ S) := by
  unfold rectCount
  apply Finset.sum_congr rfl
  intro v hv
  symm
  apply Finset.sum_subset
  · intro w hw
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hw).2⟩
  · intro w hw hn
    have hnX : w ∉ X := by
      intro hx
      exact hn (Finset.mem_sdiff.mpr ⟨hx, (Finset.mem_sdiff.mp hw).2⟩)
    simp only [if_neg (fun ha => hnX (hloc v hv w ha))]

lemma localized_deletion_bound (S X : Finset V) (k : ℕ)
    (hSX : S ⊆ X) (hX : X.card ≤ k)
    (hdeg : ∀ v ∈ S, G.degree v ≤ S.card)
    (hloc : ∀ v ∈ S, ∀ w, G.Adj v w → w ∈ X) :
    2 * G.edgeFinset.card ≤
      2 * (G.induce (↑(univ \ S) : Set V)).edgeFinset.card + S.card * k := by
  have hsum : (∑ v ∈ S, G.degree v) ≤ S.card * S.card := by
    calc
      _ ≤ ∑ _v ∈ S, S.card := Finset.sum_le_sum hdeg
      _ = _ := by simp
  have hcross : rectCount G S (univ \ S) ≤ S.card * (X.card - S.card) := by
    rw [rectCount_localized G S X hloc]
    have h := rectCount_le_card_mul G S (X \ S)
    simpa only [Finset.card_sdiff_of_subset hSX] using h
  have hcard := Finset.card_le_card hSX
  have halg : S.card * S.card + S.card * (X.card - S.card) = S.card * X.card := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hcard]
  have hpart := rectCount_partition G S
  rw [rectCount_univ, rectCount_induce] at hpart
  have hmul := Nat.mul_le_mul_left S.card hX
  omega

end EvenCycleTuran.EvenCount.Fresh
end

section

open Finset SimpleGraph
namespace EvenCycleTuran.EvenCount.Fresh
universe u

theorem edge_bound_of_localization (k : ℕ)
    (hlocal : ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      (∃ v w, H.Adj v w) →
      (∀ a : ℕ, k < a → (cycleGraph a).Free H) →
      ∃ S X : Finset W, S.Nonempty ∧ S ⊆ X ∧ S.card < X.card ∧ X.card ≤ k ∧
        (∀ v ∈ S, H.degree v ≤ S.card) ∧
        (∀ v ∈ S, ∀ w, H.Adj v w → w ∈ X))
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hG : ∀ a : ℕ, k < a → (cycleGraph a).Free G) :
    2 * G.edgeFinset.card ≤ k * (Fintype.card V - 1) := by
  classical
  suffices h : ∀ N : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj], Fintype.card W = N →
      (∀ a : ℕ, k < a → (cycleGraph a).Free H) →
      2 * H.edgeFinset.card ≤ k * (N - 1) by
    exact h (Fintype.card V) V G rfl hG
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro W _ _ H _ hcard hfree
    by_cases he : ∃ v w, H.Adj v w
    · obtain ⟨S, X, hS, hSX, hSXcard, hX, hdeg, hloc⟩ := hlocal H he hfree
      have hd0 : 0 < S.card := S.card_pos.mpr hS
      have hdN : S.card < N := by
        have hxN := Finset.card_le_univ X
        omega
      have hc : Fintype.card ↥(↑(univ \ S) : Set W) = N - S.card := by
        rw [complement_card, hcard]
      have hlt : N - S.card < N := by omega
      have hh := ih (N - S.card) hlt ↥(↑(univ \ S) : Set W)
        (H.induce (↑(univ \ S) : Set W)) hc
        (cycle_free_induce H k hfree _)
      have hb := localized_deletion_bound H S X k hSX hX hdeg hloc
      have hid : N - S.card - 1 + S.card = N - 1 := by omega
      calc
        _ ≤ 2 * (H.induce (↑(univ \ S) : Set W)).edgeFinset.card + S.card * k := hb
        _ ≤ k * (N - S.card - 1) + S.card * k := Nat.add_le_add_right hh _
        _ = k * (N - 1) := by rw [Nat.mul_comm S.card k, ← Nat.mul_add, hid]
    · have hbot : H = ⊥ := by
        ext v w
        simp only [SimpleGraph.bot_adj, iff_false]
        exact fun hvw => he ⟨v, w, hvw⟩
      have hem : H.edgeFinset = ∅ := by
        ext e
        simp [hbot]
      rw [hem]
      simp

end EvenCycleTuran.EvenCount.Fresh
end

section
open Finset SimpleGraph
namespace EvenCycleTuran.EvenCount.Fresh
variable {V : Type*} (G : SimpleGraph V)

def PathArray {m : ℕ} (p : Fin m → V) : Prop :=
  Function.Injective p ∧ ∀ i j : Fin m, i.val + 1 = j.val → G.Adj (p i) (p j)

lemma PathArray.card_le [Fintype V] {m : ℕ} {p : Fin m → V}
    (hp : PathArray G p) : m ≤ Fintype.card V := by
  simpa using Fintype.card_le_of_injective p hp.1

def reversePrefix {m : ℕ} (i j : Fin m) : Fin m :=
  if h : j.val < i.val then ⟨i.val - 1 - j.val, by omega⟩ else j

lemma reversePrefix_val {m : ℕ} (i j : Fin m) :
    (reversePrefix i j).val = if j.val < i.val then i.val - 1 - j.val else j.val := by
  unfold reversePrefix
  split_ifs <;> rfl

lemma reversePrefix_involutive {m : ℕ} (i : Fin m) :
    Function.Involutive (reversePrefix i) := by
  intro j
  apply Fin.ext
  simp only [reversePrefix_val]
  split_ifs <;> omega

lemma reversePrefix_injective {m : ℕ} (i : Fin m) :
    Function.Injective (reversePrefix i) := (reversePrefix_involutive i).injective

lemma PathArray.rotate {m : ℕ} {p : Fin m → V} (hp : PathArray G p)
    (i : Fin m) (hi : 0 < i.val)
    (hc : G.Adj (p ⟨0, by omega⟩) (p i)) :
    PathArray G (p ∘ reversePrefix i) := by
  refine ⟨hp.1.comp (reversePrefix_injective i), ?_⟩
  intro a b hab
  change G.Adj (p (reversePrefix i a)) (p (reversePrefix i b))
  by_cases hb : b.val < i.val
  · exact (hp.2 (reversePrefix i b) (reversePrefix i a)
      (by simp only [reversePrefix_val]; split_ifs <;> omega)).symm
  by_cases ha : a.val < i.val
  · have he0 : reversePrefix i a = ⟨0, by omega⟩ := by
      apply Fin.ext
      simp only [reversePrefix_val]
      split_ifs
      omega
    have hei : reversePrefix i b = i := by
      apply Fin.ext
      simp only [reversePrefix_val]
      split_ifs
      omega
    rw [he0, hei]
    exact hc
  · apply hp.2
    simp only [reversePrefix_val]
    split_ifs
    omega

lemma PathArray.rotate_head {m : ℕ} {p : Fin m → V} (i : Fin m) (hi : 0 < i.val) :
    (p ∘ reversePrefix i) ⟨0, by omega⟩ = p ⟨i.val - 1, by omega⟩ := by
  change p (reversePrefix i ⟨0, by omega⟩) = _
  apply congrArg p
  apply Fin.ext
  simp only [reversePrefix_val]
  split_ifs
  omega

lemma reversePrefix_suffix {m : ℕ} (i j : Fin m) (hij : i.val ≤ j.val) :
    reversePrefix i j = j := by simp [reversePrefix, not_lt.mpr hij]

end EvenCycleTuran.EvenCount.Fresh
end

section
open Finset SimpleGraph
namespace EvenCycleTuran.EvenCount.Fresh

lemma cycle_adj_cases {m : ℕ} (u v : Fin m) (h : (cycleGraph m).Adj u v) :
    u.val + 1 = v.val ∨ v.val + 1 = u.val ∨
      (u.val = 0 ∧ v.val + 1 = m) ∨ (v.val = 0 ∧ u.val + 1 = m) := by
  rw [cycleGraph_adj'] at h
  rcases h with h | h
  · have he := Fin.intCast_val_sub_eq_sub_add_ite u v
    rw [h] at he
    split_ifs at he <;> omega
  · have he := Fin.intCast_val_sub_eq_sub_add_ite v u
    rw [h] at he
    split_ifs at he <;> omega

variable {V : Type*} {G : SimpleGraph V}
lemma PathArray.cycle_copy {m : ℕ} {p : Fin m → V} (hp : PathArray G p)
    (hm : 3 ≤ m) (hc : G.Adj (p ⟨m-1, by omega⟩) (p ⟨0, by omega⟩)) :
    cycleGraph m ⊑ G := by
  refine ⟨{ toHom := { toFun := p, map_rel' := ?_ }, injective' := hp.1 }⟩
  intro u v huv
  rcases cycle_adj_cases u v huv with h | h | ⟨hu,hv⟩ | ⟨hv,hu⟩
  · exact hp.2 u v h
  · exact (hp.2 v u h).symm
  · have eu : u = ⟨0, by omega⟩ := Fin.ext hu
    have ev : v = ⟨m-1, by omega⟩ := by
      apply Fin.ext
      change _ = m-1
      omega
    simpa only [eu, ev] using hc.symm
  · have ev : v = ⟨0, by omega⟩ := Fin.ext hv
    have eu : u = ⟨m-1, by omega⟩ := by
      apply Fin.ext
      change _ = m-1
      omega
    simpa only [eu, ev] using hc

lemma PathArray.prefix {m t : ℕ} {p : Fin m → V} (hp : PathArray G p) (ht : t ≤ m) :
    PathArray G (fun i : Fin t => p (Fin.castLE ht i)) := by
  refine ⟨hp.1.comp (Fin.castLE_injective ht), ?_⟩
  intro i j hij
  exact hp.2 _ _ hij

lemma PathArray.chord_bound {m k : ℕ} {p : Fin m → V} (hp : PathArray G p)
    (hk : 2 ≤ k) (hfree : ∀ a : ℕ, k < a → (cycleGraph a).Free G)
    (i : Fin m) (hi : 0 < i.val)
    (hc : G.Adj (p ⟨0, by omega⟩) (p i)) : i.val < k := by
  by_contra h
  have hm : i.val + 1 ≤ m := by omega
  have hp' := hp.prefix hm
  have hclose : G.Adj
      ((fun j : Fin (i.val+1) => p (Fin.castLE hm j)) ⟨i.val, by omega⟩)
      ((fun j : Fin (i.val+1) => p (Fin.castLE hm j)) ⟨0, by omega⟩) := by
    convert hc.symm using 1 <;> apply congrArg p <;> apply Fin.ext <;> rfl
  exact hfree (i.val+1) (by omega) (hp'.cycle_copy (by omega) (by simpa using hclose))

end EvenCycleTuran.EvenCount.Fresh
end

section
open Finset SimpleGraph
namespace EvenCycleTuran.EvenCount.Fresh
variable {V : Type*} {G : SimpleGraph V}

def prependArray {m : ℕ} (p : Fin m → V) (w : V) (j : Fin (m+1)) : V :=
  if h : j.val = 0 then w else p ⟨j.val-1, by omega⟩

lemma PathArray.prepend {m : ℕ} {p : Fin m → V} (hp : PathArray G p)
    (hm : 0 < m) (w : V) (hw : w ∉ Set.range p)
    (ha : G.Adj w (p ⟨0, hm⟩)) : PathArray G (prependArray p w) := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    unfold prependArray at hab
    split_ifs at hab with h1 h2 h2
    · exact Fin.ext (by omega)
    · exact False.elim (hw ⟨_, hab.symm⟩)
    · exact False.elim (hw ⟨_, hab⟩)
    · have he := congrArg Fin.val (hp.1 hab)
      change a.val - 1 = b.val - 1 at he
      exact Fin.ext (by omega)
  · intro a b hab
    have hb : b.val ≠ 0 := by omega
    by_cases h0 : a.val = 0
    · have he : (⟨b.val-1, by omega⟩ : Fin m) = ⟨0, hm⟩ := by
        apply Fin.ext
        change b.val - 1 = 0
        omega
      simpa only [prependArray, h0, hb, ↓reduceDIte, he] using ha
    · change G.Adj (prependArray p w a) (prependArray p w b)
      simp only [prependArray, h0, hb, ↓reduceDIte]
      apply hp.2
      change a.val - 1 + 1 = b.val - 1
      omega

lemma PathArray.neighbor_mem_range {m : ℕ} {p : Fin m → V} (hp : PathArray G p)
    (hm : 0 < m)
    (hmax : ∀ t (q : Fin t → V), PathArray G q → t ≤ m)
    {w : V} (hw : G.Adj (p ⟨0, hm⟩) w) : w ∈ Set.range p := by
  by_contra hn
  have he := hp.prepend hm w hn hw.symm
  have hbad := hmax (m+1) _ he
  omega

end EvenCycleTuran.EvenCount.Fresh
end

section
open Finset SimpleGraph
namespace EvenCycleTuran.EvenCount.Fresh
noncomputable section
variable {V : Type*} [DecidableEq V]

def prefixSet {m : ℕ} (p : Fin m → V) (k : ℕ) : Finset V :=
  Finset.univ.image (fun i : Fin (min k m) => p (Fin.castLE (min_le_right k m) i))

lemma mem_prefixSet {m k : ℕ} {p : Fin m → V} {v : V} :
    v ∈ prefixSet p k ↔ ∃ i : Fin m, i.val < k ∧ p i = v := by
  simp only [prefixSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨Fin.castLE (min_le_right k m) i, by change i.val < k; omega, hi⟩
  · rintro ⟨i, hi, hv⟩
    refine ⟨⟨i.val, by omega⟩, ?_⟩
    exact hv

lemma card_prefixSet {m : ℕ} {p : Fin m → V} (hp : Function.Injective p) (k : ℕ) :
    (prefixSet p k).card = min k m := by
  unfold prefixSet
  rw [Finset.card_image_of_injective _ (show Function.Injective (fun i : Fin (min k m) => p (Fin.castLE (min_le_right k m) i)) from hp.comp (Fin.castLE_injective _))]
  simp

end
end EvenCycleTuran.EvenCount.Fresh
end

section
open Finset SimpleGraph
namespace EvenCycleTuran.EvenCount.Fresh
noncomputable section
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
lemma neighbor_index_pos {m : ℕ} {p : Fin m → V} (hm : 0 < m)
    (i : Fin m) (hi : G.Adj (p ⟨0,hm⟩) (p i)) : 0 < i.val := by
  by_contra h
  have he : i = ⟨0,hm⟩ := by
    apply Fin.ext
    change i.val = 0
    omega
  rw [he] at hi
  exact G.irrefl hi

lemma rotated_neighbor_localized {m k : ℕ} {p : Fin m → V}
    (hp : PathArray G p) (hm : 0 < m) (hk : 2 ≤ k)
    (hfree : ∀ a : ℕ, k < a → (cycleGraph a).Free G)
    (hmax : ∀ t (q : Fin t → V), PathArray G q → t ≤ m)
    (i : Fin m) (hi : G.Adj (p ⟨0,hm⟩) (p i))
    {w : V} (hw : G.Adj (p ⟨i.val-1, by omega⟩) w) : w ∈ prefixSet p k := by
  have hip := neighbor_index_pos hm i hi
  have hik := hp.chord_bound hk hfree i hip hi
  have hr := PathArray.rotate G hp i hip hi
  have hh := PathArray.rotate_head (p := p) i hip
  have hw' : G.Adj ((p ∘ reversePrefix i) ⟨0,hm⟩) w := by rwa [hh]
  obtain ⟨j,hj⟩ := hr.neighbor_mem_range hm hmax hw'
  have hjadj : G.Adj ((p ∘ reversePrefix i) ⟨0,hm⟩)
      ((p ∘ reversePrefix i) j) := by rwa [hj]
  have hjp := neighbor_index_pos hm j hjadj
  have hjk := hr.chord_bound hk hfree j hjp hjadj
  apply mem_prefixSet.mpr
  refine ⟨reversePrefix i j, ?_, hj⟩
  simp only [reversePrefix_val]
  split_ifs <;> omega

end
end EvenCycleTuran.EvenCount.Fresh
end

section
open Finset SimpleGraph
namespace EvenCycleTuran.EvenCount.Fresh
noncomputable section
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def neighborIndices {m : ℕ} (p : Fin m → V) (hm : 0 < m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => G.Adj (p ⟨0,hm⟩) (p i))

def predVertex {m : ℕ} (p : Fin m → V) (_hm : 0 < m) (i : Fin m) : V :=
  p ⟨i.val - 1, by omega⟩

def predecessorSet {m : ℕ} (p : Fin m → V) (hm : 0 < m) : Finset V :=
  (neighborIndices (G := G) p hm).image (predVertex p hm)

omit [DecidableEq V] in
lemma mem_neighborIndices {m : ℕ} {p : Fin m → V} {hm : 0 < m} {i : Fin m} :
    i ∈ neighborIndices (G := G) p hm ↔ G.Adj (p ⟨0,hm⟩) (p i) := by
  simp [neighborIndices]

lemma card_predecessorSet {m : ℕ} {p : Fin m → V} (hm : 0 < m)
    (hp : PathArray G p) :
    (predecessorSet (G := G) p hm).card = (neighborIndices (G := G) p hm).card := by
  unfold predecessorSet
  apply Finset.card_image_iff.mpr
  intro i hi j hj he
  have hip := neighbor_index_pos hm i (mem_neighborIndices.mp hi)
  have hjp := neighbor_index_pos hm j (mem_neighborIndices.mp hj)
  have hh := congrArg Fin.val (hp.1 he)
  change i.val - 1 = j.val - 1 at hh
  exact Fin.ext (by omega)

lemma predecessor_subset_prefix {m k : ℕ} {p : Fin m → V}
    (hm : 0 < m) (hp : PathArray G p) (hk : 2 ≤ k)
    (hfree : ∀ a : ℕ, k < a → (cycleGraph a).Free G) :
    predecessorSet (G := G) p hm ⊆ prefixSet p k := by
  intro v hv
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
  have hip := neighbor_index_pos hm i (mem_neighborIndices.mp hi)
  have hik := hp.chord_bound hk hfree i hip (mem_neighborIndices.mp hi)
  apply mem_prefixSet.mpr
  refine ⟨⟨i.val-1,by omega⟩, ?_, rfl⟩
  change i.val-1 < k
  omega

lemma predecessor_card_lt_prefix {m k : ℕ} {p : Fin m → V}
    (hm : 0 < m) (hp : PathArray G p) (hk : 2 ≤ k)
    (hfree : ∀ a : ℕ, k < a → (cycleGraph a).Free G) :
    (predecessorSet (G := G) p hm).card < (prefixSet p k).card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨predecessor_subset_prefix hm hp hk hfree, ?_⟩
  intro he
  let j : Fin m := ⟨min k m - 1, by omega⟩
  have hj : p j ∈ prefixSet p k := mem_prefixSet.mpr ⟨j, by dsimp [j]; omega, rfl⟩
  rw [← he] at hj
  obtain ⟨i,hi,hh⟩ := Finset.mem_image.mp hj
  have hip := neighbor_index_pos hm i (mem_neighborIndices.mp hi)
  have hik := hp.chord_bound hk hfree i hip (mem_neighborIndices.mp hi)
  have hv := congrArg Fin.val (hp.1 hh)
  change i.val-1 = min k m - 1 at hv
  omega

end
end EvenCycleTuran.EvenCount.Fresh
end

section

noncomputable section
namespace EvenCycleTuran.EvenCount.Fresh

private def edgeArray {V : Type*} (u v : V) : Fin 2 → V :=
  fun i => if i.val = 0 then u else v

lemma edge_path_array {V : Type*} (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    ∃ p : Fin 2 → V, PathArray G p := by
  refine ⟨edgeArray u v, ?_, ?_⟩
  · intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [edgeArray, huv.ne, huv.ne']
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [edgeArray]

lemma exists_maximal_path_array {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v) :
    ∃ m : ℕ, ∃ hm : 0 < m, ∃ p : Fin m → V,
      PathArray G p ∧
      (∀ (t : ℕ) (q : Fin t → V), PathArray G q → t ≤ m) ∧
      (∀ q : Fin m → V, PathArray G q →
        G.degree (q ⟨0, hm⟩) ≤ G.degree (p ⟨0, hm⟩)) := by
  classical
  let P : ℕ → Prop := fun t => ∃ q : Fin t → V, PathArray G q
  obtain ⟨q2, hq2⟩ := edge_path_array G huv
  have h2N : 2 ≤ Fintype.card V := PathArray.card_le G hq2
  have hP2 : P 2 := ⟨q2, hq2⟩
  let m := Nat.findGreatest P (Fintype.card V)
  have hmP : P m := Nat.findGreatest_spec (P := P) h2N hP2
  have hm2 : 2 ≤ m := Nat.le_findGreatest (P := P) h2N hP2
  have hm : 0 < m := by omega
  have hmax : ∀ (t : ℕ) (q : Fin t → V), PathArray G q → t ≤ m := by
    intro t q hq
    exact Nat.le_findGreatest (P := P) (PathArray.card_le G hq) ⟨q, hq⟩
  obtain ⟨p0, hp0⟩ := hmP
  let Q : ℕ → Prop := fun d => ∃ p : Fin m → V,
    PathArray G p ∧ G.degree (p ⟨0, hm⟩) = d
  let D := Nat.findGreatest Q (Fintype.card V)
  have hQ : Q D := Nat.findGreatest_spec (P := Q)
    (G.degree_lt_card_verts (p0 ⟨0, hm⟩)).le ⟨p0, hp0, rfl⟩
  obtain ⟨p, hp, hdeg⟩ := hQ
  refine ⟨m, hm, p, hp, hmax, ?_⟩
  intro q hq
  have hh : G.degree (q ⟨0, hm⟩) ≤ D := Nat.le_findGreatest (P := Q)
    (G.degree_lt_card_verts (q ⟨0, hm⟩)).le ⟨q, hq, rfl⟩
  rw [hdeg]
  exact hh

end EvenCycleTuran.EvenCount.Fresh
end

section
open Finset SimpleGraph
namespace EvenCycleTuran.EvenCount.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma neighbor_indices_card {m : ℕ} {p : Fin m → V} (hp : PathArray G p)
    (hm : 0 < m)
    (hmax : ∀ t (q : Fin t → V), PathArray G q → t ≤ m) :
    (univ.filter (fun i : Fin m => G.Adj (p ⟨0, hm⟩) (p i))).card =
      G.degree (p ⟨0, hm⟩) := by
  have he : (univ.filter (fun i : Fin m => G.Adj (p ⟨0, hm⟩) (p i))).image p =
      G.neighborFinset (p ⟨0, hm⟩) := by
    ext w
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hw
      obtain ⟨i, rfl⟩ := hp.neighbor_mem_range hm hmax hw
      exact ⟨i, hw, rfl⟩
  have hc := congrArg Finset.card he
  simpa only [Finset.card_image_of_injective _ hp.1,
    SimpleGraph.card_neighborFinset_eq_degree] using hc

end EvenCycleTuran.EvenCount.Fresh
end

section
open Finset SimpleGraph
namespace EvenCycleTuran.EvenCount.Fresh

lemma exists_localized_set {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 2 ≤ k)
    (hedge : ∃ v w, G.Adj v w)
    (hfree : ∀ a : ℕ, k < a → (cycleGraph a).Free G) :
    ∃ S X : Finset V, S.Nonempty ∧ S ⊆ X ∧ S.card < X.card ∧ X.card ≤ k ∧
      (∀ v ∈ S, G.degree v ≤ S.card) ∧
      (∀ v ∈ S, ∀ w, G.Adj v w → w ∈ X) := by
  classical
  obtain ⟨u,v,huv⟩ := hedge
  obtain ⟨m,hm,p,hp,hmax,hdegree⟩ := exists_maximal_path_array G huv
  obtain ⟨q,hq⟩ := edge_path_array G huv
  have hm2 : 2 ≤ m := hmax 2 q hq
  have hcard : (predecessorSet (G := G) p hm).card = G.degree (p ⟨0,hm⟩) := by
    rw [card_predecessorSet hm hp]
    exact neighbor_indices_card G hp hm hmax
  refine ⟨predecessorSet (G := G) p hm, prefixSet p k, ?_,
    predecessor_subset_prefix hm hp hk hfree,
    predecessor_card_lt_prefix hm hp hk hfree, ?_, ?_, ?_⟩
  · apply Finset.image_nonempty.mpr
    refine ⟨⟨1, by omega⟩, mem_neighborIndices.mpr ?_⟩
    exact hp.2 ⟨0,hm⟩ ⟨1,by omega⟩ rfl
  · rw [card_prefixSet hp.1]
    exact min_le_left k m
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    have hip := neighbor_index_pos hm i (mem_neighborIndices.mp hi)
    have hr := PathArray.rotate G hp i hip (mem_neighborIndices.mp hi)
    have hh := hdegree (p ∘ reversePrefix i) hr
    rw [PathArray.rotate_head (p := p) i hip] at hh
    rw [hcard]
    exact hh
  · intro z hz w hzw
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact rotated_neighbor_localized hp hm hk hfree hmax i
      (mem_neighborIndices.mp hi) hzw

end EvenCycleTuran.EvenCount.Fresh
end

section

open Finset SimpleGraph
namespace EvenCycleTuran.EvenCount.Fresh

theorem native_theorem_2 (n k : ℕ) (hk : 2 ≤ k) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (hG : ∀ a : ℕ, k < a → (cycleGraph a).Free G) :
    2 * #G.edgeFinset ≤ k * (n - 1) := by
  have h := edge_bound_of_localization k
    (fun H _ hedge hfree => exists_localized_set H hk hedge hfree) G hG
  simpa only [Fintype.card_fin] using h

end EvenCycleTuran.EvenCount.Fresh
end

open Finset SimpleGraph EvenCycleTuran.EvenCount

theorem solution (n k : ℕ) (hk : 2 ≤ k) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : ∀ a : ℕ, k < a → (cycleGraph a).Free G) :
    2 * #G.edgeFinset ≤ k * (n - 1)  := by
  exact Fresh.native_theorem_2 n k hk G hG
