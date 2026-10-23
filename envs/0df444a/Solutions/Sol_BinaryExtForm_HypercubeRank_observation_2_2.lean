-- Prove2me | solution 1 for BinaryExtForm.HypercubeRank.observation_2_2
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T05:46:54.637871+00:00
-- url     : https://prove2.me/submissions/16378f1e-7766-4f69-9da4-6e233087b61e

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model

set_option autoImplicit false

open Disjunctive.HigherDim

namespace BinaryExtForm.HypercubeRank.BalasProof

lemma convexHull_binary_subset {n : ℕ} (S : Set (Fin n → ℝ)) (i : Fin n)
    (hbox : ∀ x ∈ S, 0 ≤ x i ∧ x i ≤ 1) :
    convexHull ℝ S ∩ ZeroOneSet i ⊆ convexHull ℝ (S ∩ ZeroOneSet i) := by
  let C := convexHull ℝ (S ∩ ZeroOneSet i)
  let T : Set (Fin n → ℝ) := {x | 0 ≤ x i ∧ x i ≤ 1 ∧
    (x i = 0 ∨ x i = 1 → x ∈ C)}
  have hST : S ⊆ T := by
    intro x hx
    exact ⟨(hbox x hx).1, (hbox x hx).2,
      fun hb => subset_convexHull ℝ (S ∩ ZeroOneSet i) ⟨hx,hb⟩⟩
  have hT : Convex ℝ T := by
    intro x hx y hy a b ha hb hab
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0,hb1] using hy
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      simpa [hb0,ha1] using hx
    change 0 ≤ x i ∧ x i ≤ 1 ∧ (x i = 0 ∨ x i = 1 → x ∈ C) at hx
    change 0 ≤ y i ∧ y i ≤ 1 ∧ (y i = 0 ∨ y i = 1 → y ∈ C) at hy
    change 0 ≤ a*x i+b*y i ∧ a*x i+b*y i ≤ 1 ∧
      (a*x i+b*y i = 0 ∨ a*x i+b*y i = 1 → a • x+b • y ∈ C)
    have hlow : 0 ≤ a*x i+b*y i := add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
    have hupp : a*x i+b*y i ≤ 1 := by
      have hax := mul_le_mul_of_nonneg_left hx.2.1 ha
      have hby := mul_le_mul_of_nonneg_left hy.2.1 hb
      nlinarith
    refine ⟨hlow,hupp,?_⟩
    intro he
    rcases he with he | he
    · have hz := (add_eq_zero_iff_of_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)).mp he
      have hxi : x i = 0 := (mul_eq_zero.mp hz.1).resolve_left ha0
      have hyi : y i = 0 := (mul_eq_zero.mp hz.2).resolve_left hb0
      exact (convex_convexHull ℝ (S ∩ ZeroOneSet i))
        (hx.2.2 (Or.inl hxi)) (hy.2.2 (Or.inl hyi)) ha hb hab
    · have hdef : a*(1-x i)+b*(1-y i) = 0 := by nlinarith
      have hz := (add_eq_zero_iff_of_nonneg (mul_nonneg ha (sub_nonneg.mpr hx.2.1))
        (mul_nonneg hb (sub_nonneg.mpr hy.2.1))).mp hdef
      have hxi : x i = 1 := by have := (mul_eq_zero.mp hz.1).resolve_left ha0; linarith
      have hyi : y i = 1 := by have := (mul_eq_zero.mp hz.2).resolve_left hb0; linarith
      exact (convex_convexHull ℝ (S ∩ ZeroOneSet i))
        (hx.2.2 (Or.inr hxi)) (hy.2.2 (Or.inr hyi)) ha hb hab
  intro x hx
  exact (convexHull_min hST hT hx.1).2.2 hx.2

lemma split_convexHull_eq {n : ℕ} (S : Set (Fin n → ℝ)) (i : Fin n)
    (hbox : ∀ x ∈ S, 0 ≤ x i ∧ x i ≤ 1) :
    SplitConvexify (convexHull ℝ S) i = convexHull ℝ (S ∩ ZeroOneSet i) := by
  unfold SplitConvexify
  apply Set.Subset.antisymm
  · exact convexHull_min (convexHull_binary_subset S i hbox) (convex_convexHull ℝ _)
  · exact convexHull_mono (fun x hx => ⟨subset_convexHull ℝ S hx.1, hx.2⟩)

lemma iteratedSplit_convexHull {n : ℕ} (S : Set (Fin n → ℝ)) (l : List (Fin n))
    (hbox : ∀ x ∈ S, ∀ i ∈ l, 0 ≤ x i ∧ x i ≤ 1) :
    IteratedSplit (convexHull ℝ S) l =
      convexHull ℝ (S ∩ {x | ∀ i ∈ l, x ∈ ZeroOneSet i}) := by
  induction l generalizing S with
  | nil => simp [IteratedSplit]
  | cons i l ih =>
    change IteratedSplit (SplitConvexify (convexHull ℝ S) i) l = _
    rw [split_convexHull_eq S i (fun x hx => hbox x hx i (by simp))]
    rw [ih (S ∩ ZeroOneSet i) (fun x hx k hk => hbox x hx.1 k (by simp [hk]))]
    congr 1
    ext x
    simp [List.mem_cons, and_assoc]

lemma convexHull_binary_restriction {n : ℕ} (S : Set (Fin n → ℝ)) (l : List (Fin n))
    (hbox : ∀ x ∈ S, ∀ i ∈ l, 0 ≤ x i ∧ x i ≤ 1)
    {x : Fin n → ℝ} (hx : x ∈ convexHull ℝ S) (hbin : ∀ i ∈ l, x ∈ ZeroOneSet i) :
    x ∈ convexHull ℝ (S ∩ {z | ∀ i ∈ l, z ∈ ZeroOneSet i}) := by
  induction l generalizing S with
  | nil => simpa using hx
  | cons i l ih =>
    have hx' : x ∈ convexHull ℝ (S ∩ ZeroOneSet i) :=
      convexHull_binary_subset S i (fun z hz => hbox z hz i (by simp))
        ⟨hx,hbin i (by simp)⟩
    have hr := ih (S ∩ ZeroOneSet i) (fun z hz k hk => hbox z hz.1 k (by simp [hk]))
      hx' (fun k hk => hbin k (by simp [hk]))
    have heq : (S ∩ ZeroOneSet i) ∩ {z | ∀ k ∈ l, z ∈ ZeroOneSet k} =
        S ∩ {z | ∀ k ∈ i::l, z ∈ ZeroOneSet k} := by
      ext z
      simp [List.mem_cons,and_assoc]
    rwa [heq] at hr

lemma binary_restriction_nonempty_iff {n : ℕ} (S : Set (Fin n → ℝ)) (l : List (Fin n))
    (hbox : ∀ x ∈ S, ∀ i ∈ l, 0 ≤ x i ∧ x i ≤ 1) :
    (convexHull ℝ S ∩ {x | ∀ i ∈ l, x ∈ ZeroOneSet i}).Nonempty ↔
      (S ∩ {x | ∀ i ∈ l, x ∈ ZeroOneSet i}).Nonempty := by
  constructor
  · rintro ⟨x,hx,hbin⟩
    exact convexHull_nonempty_iff.mp ⟨x,convexHull_binary_restriction S l hbox hx hbin⟩
  · rintro ⟨x,hx,hbin⟩
    exact ⟨x,subset_convexHull ℝ S hx,hbin⟩

lemma binary_restriction_finset_nonempty_iff {n : ℕ} (S : Set (Fin n → ℝ))
    (H : Finset (Fin n)) (hbox : ∀ x ∈ S, ∀ i ∈ H, 0 ≤ x i ∧ x i ≤ 1) :
    (convexHull ℝ S ∩ ⋂ i ∈ H, ZeroOneSet i).Nonempty ↔
      (S ∩ ⋂ i ∈ H, ZeroOneSet i).Nonempty := by
  classical
  have heq : {x : Fin n → ℝ | ∀ i ∈ H.toList, x ∈ ZeroOneSet i} =
      ⋂ i ∈ H, ZeroOneSet i := by
    ext x
    simp
  rw [← heq]
  exact binary_restriction_nonempty_iff S H.toList (by simpa using hbox)

end BinaryExtForm.HypercubeRank.BalasProof

namespace BinaryExtForm.HypercubeRank.VertexCoverProof

lemma polytope_convex {n : ℕ} {Q : Set (Fin n → ℝ)} (hQ : IsPolytope Q) : Convex ℝ Q := by
  obtain ⟨S, rfl⟩ := hQ
  exact convex_convexHull ℝ _

lemma convexHull_extreme_eq {n : ℕ} {Q : Set (Fin n → ℝ)} (hQ : IsPolytope Q) :
    convexHull ℝ (Set.extremePoints ℝ Q) = Q := by
  obtain ⟨S, rfl⟩ := hQ
  have hv : (Set.extremePoints ℝ (convexHull ℝ (S : Set (Fin n → ℝ)))).Finite :=
    S.finite_toSet.subset extremePoints_convexHull_subset
  have h := closure_convexHull_extremePoints (S.finite_toSet.isCompact_convexHull ℝ)
    (convex_convexHull ℝ (S : Set (Fin n → ℝ)))
  rwa [(hv.isClosed_convexHull ℝ).closure_eq] at h

lemma extreme_mem_of_mem_hull {n : ℕ} {Q S : Set (Fin n → ℝ)}
    (hQ : Convex ℝ Q) (hSQ : S ⊆ Q) {v : Fin n → ℝ}
    (hv : v ∈ Set.extremePoints ℝ Q) (hmem : v ∈ convexHull ℝ S) : v ∈ S := by
  apply (extremePoints_convexHull_subset (𝕜 := ℝ) (A := S))
  refine ⟨hmem, ?_⟩
  intro x hx y hy hseg
  exact hv.2 (convexHull_min hSQ hQ hx) (convexHull_min hSQ hQ hy) hseg

lemma iteratedSplit_eq_extreme {n : ℕ} (Q : Set (Fin n → ℝ)) (H : Finset (Fin n))
    (hQ : IsPolytope Q) (hQH : ∀ p ∈ Q, ∀ i ∈ H, 0 ≤ p i ∧ p i ≤ 1)
    (l : List (Fin n)) (hlH : ∀ i ∈ l, i ∈ H) :
    IteratedSplit Q l = convexHull ℝ (Set.extremePoints ℝ Q ∩
      {x | ∀ i ∈ l, x ∈ ZeroOneSet i}) := by
  calc
    IteratedSplit Q l = IteratedSplit (convexHull ℝ (Set.extremePoints ℝ Q)) l := by
      rw [convexHull_extreme_eq hQ]
    _ = _ := BalasProof.iteratedSplit_convexHull _ l
      (fun x hx i hi => hQH x hx.1 i (hlH i hi))

lemma iteratedSplit_eq_restriction {n : ℕ} (Q : Set (Fin n → ℝ)) (H : Finset (Fin n))
    (hQ : IsPolytope Q) (hQH : ∀ p ∈ Q, ∀ i ∈ H, 0 ≤ p i ∧ p i ≤ 1)
    (l : List (Fin n)) (hlH : ∀ i ∈ l, i ∈ H) :
    IteratedSplit Q l = convexHull ℝ (Q ∩ {x | ∀ i ∈ l, x ∈ ZeroOneSet i}) := by
  have h := BalasProof.iteratedSplit_convexHull Q l
    (fun x hx i hi => hQH x hx i (hlH i hi))
  rwa [(polytope_convex hQ).convexHull_eq] at h

lemma iteratedSplit_eq_intHull_iff {n : ℕ} (Q : Set (Fin n → ℝ)) (H : Finset (Fin n))
    (hQ : IsPolytope Q) (hQH : ∀ p ∈ Q, ∀ i ∈ H, 0 ≤ p i ∧ p i ≤ 1)
    (l : List (Fin n)) (hlH : ∀ i ∈ l, i ∈ H) :
    IteratedSplit Q l = intHull Q H ↔
      ∀ v ∈ Set.extremePoints ℝ Q, (∃ i ∈ H, v i ≠ 0 ∧ v i ≠ 1) →
        ∃ i ∈ l.toFinset, v i ≠ 0 ∧ v i ≠ 1 := by
  classical
  constructor
  · intro heq v hv hfrac
    by_contra hhit
    have hbin : ∀ i ∈ l, v ∈ ZeroOneSet i := by
      intro i hi
      change v i = 0 ∨ v i = 1
      by_contra hnot
      exact hhit ⟨i, List.mem_toFinset.mpr hi, (not_or.mp hnot).1, (not_or.mp hnot).2⟩
    have hvsplit : v ∈ IteratedSplit Q l := by
      rw [iteratedSplit_eq_extreme Q H hQ hQH l hlH]
      exact subset_convexHull ℝ _ ⟨hv, hbin⟩
    rw [heq] at hvsplit
    have hmem : v ∈ Q ∩ ⋂ i ∈ H, ZeroOneSet i :=
      extreme_mem_of_mem_hull (polytope_convex hQ) (fun _ h => h.1) hv hvsplit
    obtain ⟨i, hi, hzero, hone⟩ := hfrac
    have hbi : v i = 0 ∨ v i = 1 := Set.mem_iInter.mp (Set.mem_iInter.mp hmem.2 i) hi
    exact hbi.elim hzero hone
  · intro hcover
    apply Set.Subset.antisymm
    · rw [iteratedSplit_eq_extreme Q H hQ hQH l hlH]
      apply convexHull_mono
      rintro v ⟨hv, hbin⟩
      refine ⟨hv.1, ?_⟩
      simp only [Set.mem_iInter]
      intro i hi
      change v i = 0 ∨ v i = 1
      by_contra hnot
      obtain ⟨j, hj, hzero, hone⟩ := hcover v hv
        ⟨i, hi, (not_or.mp hnot).1, (not_or.mp hnot).2⟩
      exact (hbin j (List.mem_toFinset.mp hj)).elim hzero hone
    · rw [iteratedSplit_eq_restriction Q H hQ hQH l hlH]
      apply convexHull_mono
      rintro v ⟨hv, hbin⟩
      refine ⟨hv, ?_⟩
      intro i hi
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hbin i) (hlH i hi)

end BinaryExtForm.HypercubeRank.VertexCoverProof

namespace BinaryExtForm.HypercubeRank.CoverProof

/-- Minimizing the length of lists with a property of their support is the same
as minimizing the cardinality of finite supports with that property. -/
theorem list_min_eq_finset_min {α : Type*} [DecidableEq α]
    (H : Finset α) (P : Finset α → Prop)
    (hne : ∃ Z, Z ⊆ H ∧ P Z) :
    sInf {k : ℕ | ∃ l : List α,
      (∀ i ∈ l, i ∈ H) ∧ l.length = k ∧ P l.toFinset} =
      sInf {c : ℕ | ∃ Z : Finset α, Z ⊆ H ∧ Z.card = c ∧ P Z} := by
  classical
  let L : Set ℕ := {k | ∃ l : List α,
    (∀ i ∈ l, i ∈ H) ∧ l.length = k ∧ P l.toFinset}
  let F : Set ℕ := {c | ∃ Z : Finset α, Z ⊆ H ∧ Z.card = c ∧ P Z}
  change sInf L = sInf F
  have to_list : ∀ Z : Finset α, Z ⊆ H → P Z → Z.card ∈ L := by
    intro Z hZH hZ
    refine ⟨Z.toList, ?_, Finset.length_toList Z, ?_⟩
    · intro i hi
      exact hZH (Finset.mem_toList.mp hi)
    · simpa using hZ
  obtain ⟨Z, hZH, hZ⟩ := hne
  have hL : L.Nonempty := ⟨Z.card, to_list Z hZH hZ⟩
  have hF : F.Nonempty := ⟨Z.card, Z, hZH, rfl, hZ⟩
  apply le_antisymm
  · apply le_csInf hF
    rintro c ⟨Y, hYH, hcard, hY⟩
    rw [← hcard]
    exact csInf_le (OrderBot.bddBelow L) (to_list Y hYH hY)
  · apply le_csInf hL
    rintro k ⟨l, hlH, hlen, hl⟩
    have hmem : l.toFinset.card ∈ F :=
      ⟨l.toFinset, fun i hi => hlH i (List.mem_toFinset.mp hi), rfl, hl⟩
    exact (csInf_le (OrderBot.bddBelow F) hmem).trans
      (hlen ▸ List.toFinset_card_le l)

end BinaryExtForm.HypercubeRank.CoverProof

open BinaryExtForm.HypercubeRank

theorem solution {n : ℕ} (Q : Set (Fin n → ℝ)) (H : Finset (Fin n)) (hQ : IsPolytope Q)
    (hQH : ∀ p ∈ Q, ∀ i ∈ H, 0 ≤ p i ∧ p i ≤ 1) :
    lpr Q H = sInf {c : ℕ | ∃ Z : Finset (Fin n), Z ⊆ H ∧ Z.card = c ∧
      ∀ v ∈ Set.extremePoints ℝ Q, (∃ i ∈ H, v i ≠ 0 ∧ v i ≠ 1) →
        ∃ i ∈ Z, v i ≠ 0 ∧ v i ≠ 1} := by
  classical
  let P : Finset (Fin n) → Prop := fun Z =>
    ∀ v ∈ Set.extremePoints ℝ Q, (∃ i ∈ H, v i ≠ 0 ∧ v i ≠ 1) →
      ∃ i ∈ Z, v i ≠ 0 ∧ v i ≠ 1
  have hne : ∃ Z : Finset (Fin n), Z ⊆ H ∧ P Z :=
    ⟨H, Finset.Subset.refl H, fun _ _ h => h⟩
  calc
    lpr Q H = sInf {k : ℕ | ∃ l : List (Fin n),
        (∀ i ∈ l, i ∈ H) ∧ l.length = k ∧ P l.toFinset} := by
      unfold lpr
      congr 1
      ext k
      constructor
      · rintro ⟨l, hl, hlen, hs⟩
        exact ⟨l, hl, hlen,
          (VertexCoverProof.iteratedSplit_eq_intHull_iff Q H hQ hQH l hl).mp hs⟩
      · rintro ⟨l, hl, hlen, hs⟩
        exact ⟨l, hl, hlen,
          (VertexCoverProof.iteratedSplit_eq_intHull_iff Q H hQ hQH l hl).mpr hs⟩
    _ = _ := CoverProof.list_min_eq_finset_min H P hne
