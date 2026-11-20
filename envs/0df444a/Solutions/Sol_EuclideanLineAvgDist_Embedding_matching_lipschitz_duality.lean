-- Prove2me | solution 1 for EuclideanLineAvgDist.Embedding.matching_lipschitz_duality
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:12:16.126219+00:00
-- url     : https://prove2.me/submissions/45c8ca25-6a60-4097-8a83-899180d3cc29

import Mathlib
import Definitions.Def_EuclideanLineAvgDist_Embedding_Basic

section
open scoped BigOperators
set_option autoImplicit false

namespace EuclideanLineAvgDist.Dev.MatchingDuality

variable {ι : Type*}

/-- weight of the path given by a list -/
def pw (c : ι → ι → ℝ) : List ι → ℝ
  | x :: y :: l => c x y + pw c (y :: l)
  | _ => 0

@[simp] lemma pw_nil (c : ι → ι → ℝ) : pw c [] = 0 := by simp [pw]
@[simp] lemma pw_single (c : ι → ι → ℝ) (x : ι) : pw c [x] = 0 := by simp [pw]
@[simp] lemma pw_cons_cons (c : ι → ι → ℝ) (x y : ι) (l : List ι) :
    pw c (x :: y :: l) = c x y + pw c (y :: l) := by simp [pw]

lemma pw_split (c : ι → ι → ℝ) (a : ι) (Q : List ι) :
    ∀ P : List ι, pw c (P ++ a :: Q) = pw c (P ++ [a]) + pw c (a :: Q) := by
  intro P
  induction P with
  | nil => simp
  | cons x P ih =>
    cases P with
    | nil => simp
    | cons y P' =>
      simp only [List.cons_append, pw_cons_cons] at ih ⊢
      rw [ih]; ring

lemma pw_closed (c : ι → ι → ℝ) (e : ι) (r : List ι) :
    ∀ x : ι, pw c (x :: (r ++ [e])) = (List.zipWith c (x :: r) (r ++ [e])).sum := by
  induction r with
  | nil => intro x; simp
  | cons y r ih =>
    intro x
    simp only [List.cons_append, pw_cons_cons, List.zipWith_cons_cons, List.sum_cons]
    rw [ih]

lemma map_formPerm_eq_rotate [DecidableEq ι] (a : ι) (r : List ι) (h : (a :: r).Nodup) :
    (a :: r).map (List.formPerm (a :: r)) = r ++ [a] := by
  have hrot : (a :: r).rotate 1 = r ++ [a] := by simp
  rw [← hrot]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < (a :: r).length := by simpa using h1
    simp only [List.getElem_map]
    rw [List.formPerm_apply_getElem _ h i hi, List.getElem_rotate]

lemma cyc_sum [DecidableEq ι] [Fintype ι] (c : ι → ι → ℝ) (hc : ∀ x, c x x = 0) (a : ι) (r : List ι)
    (h : (a :: r).Nodup) :
    pw c (a :: (r ++ [a])) = ∑ b : ι, c b (List.formPerm (a :: r) b) := by
  rw [pw_closed]
  have h1 : ∑ b : ι, c b (List.formPerm (a :: r) b) =
      ∑ b ∈ (a :: r).toFinset, c b (List.formPerm (a :: r) b) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro b _ hb
    rw [List.formPerm_apply_of_notMem (by simpa using hb), hc]
  rw [h1, List.sum_toFinset _ h]
  have h2 := map_formPerm_eq_rotate a r h
  have h3 : ∀ (m : List ι) (σ : ι → ι),
      (m.map (fun b => c b (σ b))).sum = (List.zipWith c m (m.map σ)).sum := by
    intro m σ
    induction m with
    | nil => simp
    | cons x m ih => simp [ih]
  rw [h3, h2]


lemma exists_potential [DecidableEq ι] [Fintype ι] (c : ι → ι → ℝ)
    (hcyc : ∀ (a : ι) (r : List ι), (a :: r).Nodup → 0 ≤ pw c (a :: (r ++ [a]))) :
    ∃ h : ι → ℝ, ∀ a a', h a' - h a ≤ c a a' := by
  have hex : ∀ a : ι, ∃ P : List ι, P.Nodup ∧ P.head? = some a ∧
      ∀ L : List ι, L.Nodup → L.head? = some a → pw c P ≤ pw c L := by
    intro a
    have hfin : {L : List ι | L.Nodup ∧ L.head? = some a}.Finite := by
      apply (List.finite_length_le ι (Fintype.card ι)).subset
      intro L hL
      exact hL.1.length_le_card
    obtain ⟨P, hP, hmin⟩ := Set.exists_min_image _ (pw c) hfin ⟨[a], by simp⟩
    exact ⟨P, hP.1, hP.2, fun L h1 h2 => hmin L ⟨h1, h2⟩⟩
  choose P hPn hPh hPm using hex
  refine ⟨fun a => - pw c (P a), ?_⟩
  intro a a'
  suffices H : pw c (P a) ≤ c a a' + pw c (P a') by simp only; linarith
  obtain ⟨Q, hQ⟩ : ∃ Q, P a' = a' :: Q := by
    cases h : P a' with
    | nil => have := hPh a'; rw [h] at this; simp at this
    | cons x Q => 
      have := hPh a'
      rw [h] at this
      simp at this
      exact ⟨Q, by rw [this]⟩
  have hcons : pw c (a :: P a') = c a a' + pw c (P a') := by
    rw [hQ]; simp
  by_cases hmem : a ∈ P a'
  · obtain ⟨P1, P2, hsplit⟩ := List.append_of_mem hmem
    have hnd := hPn a'
    rw [hsplit] at hnd
    have hnd1 : (a :: P1).Nodup := by
      rw [List.nodup_cons]
      refine ⟨?_, (List.nodup_append.mp hnd).1⟩
      exact fun h => (List.nodup_append.mp hnd).2.2 a h a (by simp) rfl
    have hnd2 : (a :: P2).Nodup := hnd.sublist (List.sublist_append_right _ _)
    have h1 := hPm a (a :: P2) hnd2 (by simp)
    have h2 := hcyc a P1 hnd1
    have h3 : pw c (a :: P a') = pw c (a :: (P1 ++ [a])) + pw c (a :: P2) := by
      rw [hsplit]
      have := pw_split c a P2 (a :: P1)
      simpa using this
    linarith
  · have hnd : (a :: P a').Nodup := List.nodup_cons.mpr ⟨hmem, hPn a'⟩
    have := hPm a (a :: P a') hnd (by simp)
    linarith

end EuclideanLineAvgDist.Dev.MatchingDuality

namespace EuclideanLineAvgDist

open EuclideanLineAvgDist.Embedding
open EuclideanLineAvgDist.Dev.MatchingDuality

theorem chk_matching_lipschitz_duality {X : Type*} [MetricSpace X] [Fintype X]
    (A B : Finset X) (hdisj : Disjoint A B) (M : A ≃ B) (hM : IsMinMatching M) :
    ∃ f : X → ℝ, NonExpansive f ∧
      ∑ y ∈ B, f y - ∑ x ∈ A, f x = ∑ a : A, dist (a : X) (M a : X) := by
  classical
  let δ : A → ℝ := fun a => dist (a : X) (M a : X)
  let c : A → A → ℝ := fun a a' => dist (a : X) (M a' : X) - δ a
  have hcyc : ∀ (a : A) (r : List A), (a :: r).Nodup → 0 ≤ pw c (a :: (r ++ [a])) := by
    intro a r h
    rw [cyc_sum c (fun x => by simp [c, δ]) a r h]
    have := hM ((List.formPerm (a :: r)).trans M)
    simp only [matchingCost, Equiv.trans_apply] at this
    simp only [c, δ, Finset.sum_sub_distrib]
    linarith
  obtain ⟨h, hh⟩ := exists_potential c hcyc
  let f0 : X → ℝ := fun x =>
    if hx : x ∈ A then h ⟨x, hx⟩ - δ ⟨x, hx⟩ else if hb : x ∈ B then h (M.symm ⟨x, hb⟩) else 0
  have f0A : ∀ a : A, f0 (a : X) = h a - δ a := by
    intro a
    simp only [f0]
    rw [dif_pos a.2]
  have f0B : ∀ a : A, f0 ((M a : B) : X) = h a := by
    intro a
    have hnA : ((M a : B) : X) ∉ A := Finset.disjoint_right.mp hdisj (M a).2
    simp only [f0]
    rw [dif_neg hnA, dif_pos (M a).2]
    simp
  have hh' : ∀ a a' : A, h a' - h a ≤ dist (a : X) (M a' : X) - δ a := hh
  have hAA : ∀ a a' : A, f0 a - f0 a' ≤ dist (a : X) a' := by
    intro a a'
    rw [f0A, f0A]
    have h1 := hh' a' a
    have h2 := dist_triangle (a' : X) a (M a : X)
    have h3 := dist_comm (a : X) a'
    simp only [δ] at *
    linarith
  have hBB : ∀ a a' : A, f0 (M a : X) - f0 (M a' : X) ≤ dist (M a : X) (M a' : X) := by
    intro a a'
    rw [f0B, f0B]
    have h1 := hh' a' a
    have h2 := dist_triangle (a' : X) (M a' : X) (M a : X)
    have h3 := dist_comm (M a : X) (M a' : X)
    simp only [δ] at *
    linarith
  have hAB : ∀ a a' : A, f0 (M a' : X) - f0 a ≤ dist (a : X) (M a' : X) := by
    intro a a'
    rw [f0B, f0A]
    have h1 := hh' a a'
    simp only [δ] at *
    linarith
  have hBA : ∀ a a' : A, f0 a - f0 (M a' : X) ≤ dist (a : X) (M a' : X) := by
    intro a a'
    rw [f0B, f0A]
    have h1 := hh' a' a
    have h2 := dist_triangle (a' : X) (M a' : X) (a : X)
    have h3 := dist_triangle (a' : X) (a : X) (M a : X)
    have h4 := dist_triangle (a' : X) (M a' : X) (a : X)
    have h5 := dist_triangle4 (a' : X) (M a' : X) (a : X) (M a : X)
    have h6 := dist_comm (M a' : X) (a : X)
    simp only [δ] at *
    linarith
  have hcases : ∀ x : X, x ∈ A ∪ B → ∃ a : A, x = a ∨ x = (M a : X) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact ⟨⟨x, hx⟩, Or.inl rfl⟩
    · exact ⟨M.symm ⟨x, hx⟩, Or.inr (by simp)⟩
  have hone : ∀ x ∈ A ∪ B, ∀ y ∈ A ∪ B, f0 x - f0 y ≤ dist x y := by
    intro x hx y hy
    obtain ⟨a, ha⟩ := hcases x hx
    obtain ⟨a', ha'⟩ := hcases y hy
    rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl
    · exact hAA a a'
    · exact hBA a a'
    · rw [dist_comm]; exact hAB a' a
    · exact hBB a a'
  have hlip : LipschitzOnWith 1 f0 ((A ∪ B : Finset X) : Set X) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hx' : x ∈ A ∪ B := by simpa using hx
    have hy' : y ∈ A ∪ B := by simpa using hy
    rw [Real.dist_eq, abs_le]
    have := hone x hx' y hy'
    have := hone y hy' x hx'
    rw [dist_comm y x] at this
    simp
    constructor <;> linarith
  obtain ⟨g, hg, hgeq⟩ := hlip.extend_real
  refine ⟨g, ?_, ?_⟩
  · intro x y
    have := hg.dist_le_mul x y
    rw [Real.dist_eq] at this
    simpa using this
  · have hgA : ∀ a : A, g (a : X) = h a - δ a := by
      intro a
      rw [← hgeq (by simp), f0A]
    have hgB : ∀ a : A, g ((M a : B) : X) = h a := by
      intro a
      rw [← hgeq (by simp), f0B]
    have e1 : ∑ y ∈ B, g y = ∑ a : A, g ((M a : B) : X) := by
      rw [← Finset.sum_coe_sort B g]
      exact (Equiv.sum_comp M (fun b : B => g (b : X))).symm
    have e2 : ∑ x ∈ A, g x = ∑ a : A, g (a : X) := (Finset.sum_coe_sort A g).symm
    rw [e1, e2, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [hgA, hgB]
    simp [δ]

end EuclideanLineAvgDist

end

theorem solution : type_of% @EuclideanLineAvgDist.chk_matching_lipschitz_duality := @EuclideanLineAvgDist.chk_matching_lipschitz_duality
