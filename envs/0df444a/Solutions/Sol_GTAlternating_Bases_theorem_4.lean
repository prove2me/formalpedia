-- Prove2me | solution 1 for GTAlternating.Bases.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T07:44:06.154793+00:00
-- url     : https://prove2.me/submissions/19a8a2b7-62dc-4662-ac4b-38f21dfee92c

import Mathlib
import Definitions.Def_GTAlternating_Bases_Model

set_option autoImplicit false

namespace GTAlternating.Bases
namespace Lib

open Classical QAlgorithms.Papers.Independent.Renew46.P26

/-! ## Basic facts on `boxOf` and `SYT` -/

lemma boxOf_lt {n : ℕ} (T : YoungTableau n) (k : ℕ) (h : k < n) :
    boxOf T k = T.1 ⟨k, h⟩ := by
  simp [boxOf, h]

lemma boxOf_ge {n : ℕ} (T : YoungTableau n) (k : ℕ) (h : ¬ k < n) :
    boxOf T k = (0, 0) := by
  simp [boxOf, h]

lemma SYT_ext {lam : YoungDiagram} {T U : SYT lam}
    (h : ∀ k, k < lam.cells.card → boxOf U.1 k = boxOf T.1 k) : U = T := by
  apply Subtype.ext; apply Subtype.ext; funext i
  have := h i.val i.isLt
  simpa [boxOf, i.isLt] using this

lemma SYT_image {lam : YoungDiagram} (T : SYT lam) :
    Finset.univ.image T.1.1 = lam.cells := by
  show (tableauShape T.1).cells = lam.cells
  rw [T.2]

lemma SYT_mem {lam : YoungDiagram} (T : SYT lam) (i : Fin lam.cells.card) :
    T.1.1 i ∈ lam.cells := by
  have h := SYT_image T
  have : T.1.1 i ∈ Finset.univ.image T.1.1 := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  rw [h] at this; exact this

lemma SYT_boxOf_mem {lam : YoungDiagram} (T : SYT lam) (k : ℕ) (hk : k < lam.cells.card) :
    boxOf T.1 k ∈ lam.cells := by
  rw [boxOf_lt _ _ hk]; exact SYT_mem T _

lemma SYT_exists_of_mem {lam : YoungDiagram} (T : SYT lam) {b : ℕ × ℕ} (hb : b ∈ lam.cells) :
    ∃ k, k < lam.cells.card ∧ boxOf T.1 k = b := by
  rw [← SYT_image T] at hb
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
  exact ⟨i.val, i.isLt, by rw [boxOf_lt _ _ i.isLt]⟩

lemma SYT_boxOf_inj {lam : YoungDiagram} (T : SYT lam) {k l : ℕ}
    (hk : k < lam.cells.card) (hl : l < lam.cells.card) (h : boxOf T.1 k = boxOf T.1 l) :
    k = l := by
  rw [boxOf_lt _ _ hk, boxOf_lt _ _ hl] at h
  have := T.1.2.1 h
  simp at this; exact this

/-! ## One-box edges -/

lemma edge_subset {mu lam : YoungDiagram} (h : YoungEdge mu lam) : mu.cells ⊆ lam.cells :=
  YoungDiagram.cells_subset_iff.mpr h.1

lemma edge_card {mu lam : YoungDiagram} (h : YoungEdge mu lam) :
    lam.cells.card = mu.cells.card + 1 := by
  have h1 := Finset.card_sdiff_add_card_eq_card (edge_subset h)
  rw [h.2] at h1; omega

lemma edge_box {mu lam : YoungDiagram} (h : YoungEdge mu lam) :
    ∃ c, lam.cells \ mu.cells = {c} := Finset.card_eq_one.mp h.2

/-! ## Extension of a tableau of `mu` to `lam` along an edge -/

/-- the label function of the extension: `T` on `k < |mu|`, the new box `c` at label `|mu|`. -/
def extFun {mu : YoungDiagram} (T : SYT mu) (c : ℕ × ℕ) (n : ℕ) : Fin n → ℕ × ℕ :=
  fun i => if i.val < mu.cells.card then boxOf T.1 i.val else c

lemma exists_ext {mu lam : YoungDiagram} (h : YoungEdge mu lam) (T : SYT mu) :
    ∃ U : SYT lam, ∀ k, k < mu.cells.card → boxOf U.1 k = boxOf T.1 k := by
  obtain ⟨c, hc⟩ := edge_box h
  have hcard := edge_card h
  have hsub := edge_subset h
  have hcl : c ∈ lam.cells := (Finset.mem_sdiff.mp (hc ▸ Finset.mem_singleton_self c)).1
  have hcm : c ∉ mu.cells := (Finset.mem_sdiff.mp (hc ▸ Finset.mem_singleton_self c)).2
  have hsplit : ∀ b, b ∈ lam.cells ↔ b ∈ mu.cells ∨ b = c := by
    intro b
    constructor
    · intro hb
      by_cases hbm : b ∈ mu.cells
      · exact Or.inl hbm
      · right
        have : b ∈ lam.cells \ mu.cells := Finset.mem_sdiff.mpr ⟨hb, hbm⟩
        rw [hc] at this; exact Finset.mem_singleton.mp this
    · rintro (hb | rfl)
      · exact hsub hb
      · exact hcl
  set n := lam.cells.card with hn
  let t : Fin n → ℕ × ℕ := extFun T c n
  have ht_lt : ∀ i : Fin n, i.val < mu.cells.card → t i = boxOf T.1 i.val := by
    intro i hi; simp [t, extFun, hi]
  have ht_ge : ∀ i : Fin n, ¬ i.val < mu.cells.card → t i = c := by
    intro i hi; simp [t, extFun, hi]
  have ht_mem : ∀ i : Fin n, t i ∈ lam.cells := by
    intro i
    by_cases hi : i.val < mu.cells.card
    · rw [ht_lt i hi]; exact hsub (SYT_boxOf_mem T _ hi)
    · rw [ht_ge i hi]; exact hcl
  have hinj : Function.Injective t := by
    intro i j hij
    apply Fin.ext
    by_cases hi : i.val < mu.cells.card <;> by_cases hj : j.val < mu.cells.card
    · rw [ht_lt i hi, ht_lt j hj] at hij; exact SYT_boxOf_inj T hi hj hij
    · rw [ht_lt i hi, ht_ge j hj] at hij
      exact absurd (hij ▸ SYT_boxOf_mem T _ hi) hcm
    · rw [ht_ge i hi, ht_lt j hj] at hij
      exact absurd (hij.symm ▸ SYT_boxOf_mem T _ hj) hcm
    · have := i.isLt; have := j.isLt; omega
  have hall : ∀ b, b ∈ lam.cells → ∃ i : Fin n, t i = b := by
    intro b hb
    rcases (hsplit b).mp hb with hbm | rfl
    · obtain ⟨k, hk, rfl⟩ := SYT_exists_of_mem T hbm
      exact ⟨⟨k, by omega⟩, ht_lt ⟨k, by omega⟩ hk⟩
    · exact ⟨⟨mu.cells.card, by omega⟩, ht_ge _ (lt_irrefl _)⟩
  have hlow : ∀ m : ℕ, m ≤ n → IsLowerSet {b | ∃ i : Fin n, i.val < m ∧ t i = b} := by
    intro m hm a b hba ha
    obtain ⟨i, hi, rfl⟩ := ha
    by_cases hmm : m ≤ mu.cells.card
    · have hi' : i.val < mu.cells.card := by omega
      rw [ht_lt i hi', boxOf_lt _ _ hi'] at hba
      obtain ⟨j, hj, hjb⟩ := T.1.2.2 m hmm hba ⟨⟨i.val, hi'⟩, hi, rfl⟩
      refine ⟨⟨j.val, by omega⟩, hj, ?_⟩
      rw [ht_lt _ (by simpa using lt_of_lt_of_le hj hmm), ← hjb, boxOf_lt _ _ j.isLt]
    · have hb : b ∈ lam.cells := lam.isLowerSet hba (ht_mem i)
      obtain ⟨j, rfl⟩ := hall b hb
      exact ⟨j, by have := j.isLt; omega, rfl⟩
  let U0 : YoungTableau n := ⟨t, hinj, hlow⟩
  have hshape : tableauShape U0 = lam := by
    apply YoungDiagram.ext
    ext b
    show b ∈ Finset.univ.image t ↔ b ∈ lam.cells
    constructor
    · intro hb; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb; exact ht_mem i
    · intro hb; obtain ⟨i, rfl⟩ := hall b hb; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  refine ⟨⟨U0, hshape⟩, fun k hk => ?_⟩
  rw [boxOf_lt _ _ (by omega : k < n)]
  exact ht_lt ⟨k, by omega⟩ hk

lemma ext_unique {mu lam : YoungDiagram} (h : YoungEdge mu lam) (T : SYT mu) (U U' : SYT lam)
    (hU : ∀ k, k < mu.cells.card → boxOf U.1 k = boxOf T.1 k)
    (hU' : ∀ k, k < mu.cells.card → boxOf U'.1 k = boxOf T.1 k) : U = U' := by
  have hcard := edge_card h
  apply SYT_ext
  intro k hk
  by_cases hkm : k < mu.cells.card
  · rw [hU k hkm, hU' k hkm]
  · have hk' : k = mu.cells.card := by omega
    subst hk'
    -- the box of the last label is the unique box of `lam` not in `mu`
    have key : ∀ V : SYT lam, (∀ k, k < mu.cells.card → boxOf V.1 k = boxOf T.1 k) →
        boxOf V.1 mu.cells.card ∈ lam.cells \ mu.cells := by
      intro V hV
      refine Finset.mem_sdiff.mpr ⟨SYT_boxOf_mem V _ hk, fun hm => ?_⟩
      obtain ⟨j, hj, hjb⟩ := SYT_exists_of_mem T hm
      rw [← hV j hj] at hjb
      have := SYT_boxOf_inj V (by omega) hk hjb
      omega
    obtain ⟨c, hc⟩ := edge_box h
    have h1 := key U' hU'; have h2 := key U hU
    rw [hc, Finset.mem_singleton] at h1 h2
    rw [h1, h2]

/-- the extension of `T` along the edge. -/
noncomputable def extT {mu lam : YoungDiagram} (h : YoungEdge mu lam) (T : SYT mu) : SYT lam :=
  (exists_ext h T).choose

lemma extT_spec {mu lam : YoungDiagram} (h : YoungEdge mu lam) (T : SYT mu) :
    ∀ k, k < mu.cells.card → boxOf (extT h T).1 k = boxOf T.1 k :=
  (exists_ext h T).choose_spec

lemma embed_vT {mu lam : YoungDiagram} (h : YoungEdge mu lam) (T : SYT mu) :
    embed mu lam (vT T) = vT (extT h T) := by
  unfold embed vT
  rw [Finsupp.linearCombination_single, one_smul]
  have hh : YoungEdge mu lam ∧
      ∃ U : SYT lam, ∀ k, k < mu.cells.card → boxOf U.1 k = boxOf T.1 k := ⟨h, exists_ext h T⟩
  rw [dif_pos hh]
  rfl

lemma extT_injective {mu lam : YoungDiagram} (h : YoungEdge mu lam) :
    Function.Injective (extT (lam := lam) h) := by
  intro T T' hTT
  apply SYT_ext
  intro k hk
  rw [← extT_spec h T k hk, ← extT_spec h T' k hk, hTT]


/-! ## The last box, restriction, and compatibility with Young's form -/

lemma last_box_mem {mu lam : YoungDiagram} (h : YoungEdge mu lam) (T : SYT mu) (V : SYT lam)
    (hV : ∀ k, k < mu.cells.card → boxOf V.1 k = boxOf T.1 k) :
    boxOf V.1 mu.cells.card ∈ lam.cells \ mu.cells := by
  have hcard := edge_card h
  refine Finset.mem_sdiff.mpr ⟨SYT_boxOf_mem V _ (by omega), fun hm => ?_⟩
  obtain ⟨j, hj, hjb⟩ := SYT_exists_of_mem T hm
  rw [← hV j hj] at hjb
  have := SYT_boxOf_inj V (by omega) (by omega) hjb
  omega

lemma exists_restrict {mu lam : YoungDiagram} (h : YoungEdge mu lam) (U : SYT lam)
    (hU : boxOf U.1 mu.cells.card ∉ mu.cells) :
    ∃ T : SYT mu, ∀ k, k < mu.cells.card → boxOf U.1 k = boxOf T.1 k := by
  have hcard := edge_card h
  obtain ⟨c, hc⟩ := edge_box h
  set m := mu.cells.card with hm
  let t : Fin m → ℕ × ℕ := fun j => boxOf U.1 j.val
  have hinj : Function.Injective t := by
    intro i j hij; apply Fin.ext
    exact SYT_boxOf_inj U (by have := i.isLt; omega) (by have := j.isLt; omega) hij
  have hlow : ∀ m' : ℕ, m' ≤ m → IsLowerSet {b | ∃ i : Fin m, i.val < m' ∧ t i = b} := by
    intro m' hm' a b hba ha
    obtain ⟨i, hi, rfl⟩ := ha
    have hi' : i.val < lam.cells.card := by have := i.isLt; omega
    have ht : t i = U.1.1 ⟨i.val, hi'⟩ := boxOf_lt _ _ hi'
    rw [ht] at hba
    obtain ⟨j, hj, hjb⟩ := U.1.2.2 m' (by omega) hba ⟨⟨i.val, hi'⟩, hi, rfl⟩
    refine ⟨⟨j.val, by omega⟩, hj, ?_⟩
    show boxOf U.1 j.val = b
    rw [boxOf_lt _ _ j.isLt]; exact hjb
  have himg_sub : Finset.univ.image t ⊆ mu.cells := by
    intro b hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
    have hi' : i.val < lam.cells.card := by have := i.isLt; omega
    have hl : t i ∈ lam.cells := SYT_boxOf_mem U _ hi'
    have hne : t i ≠ boxOf U.1 m := by
      intro he; have := SYT_boxOf_inj U hi' (by omega) he; have := i.isLt; omega
    by_contra hnm
    have h1 : t i ∈ lam.cells \ mu.cells := Finset.mem_sdiff.mpr ⟨hl, hnm⟩
    have h2 : boxOf U.1 m ∈ lam.cells \ mu.cells :=
      Finset.mem_sdiff.mpr ⟨SYT_boxOf_mem U _ (by omega), hU⟩
    rw [hc] at h1 h2
    exact hne ((Finset.mem_singleton.mp h1).trans (Finset.mem_singleton.mp h2).symm)
  have himg : Finset.univ.image t = mu.cells := by
    apply Finset.eq_of_subset_of_card_le himg_sub
    rw [Finset.card_image_of_injective _ hinj]; simp [m]
  have hshape : tableauShape (⟨t, hinj, hlow⟩ : YoungTableau m) = mu := by
    apply YoungDiagram.ext
    exact himg
  refine ⟨⟨⟨t, hinj, hlow⟩, hshape⟩, fun k hk => ?_⟩
  rw [boxOf_lt _ _ hk]

lemma embed_swapVec {mu lam : YoungDiagram} (h : YoungEdge mu lam) (T : SYT mu) (i : ℕ)
    (hi : i + 1 < mu.cells.card) :
    embed mu lam (swapVec T i) = swapVec (extT h T) i := by
  have hcard := edge_card h
  have hτ : ∀ k, (if k = i then i + 1 else if k = i + 1 then i else k) < mu.cells.card ↔
      k < mu.cells.card := by
    intro k; split_ifs <;> omega
  have hτfix : ∀ k, ¬ k < mu.cells.card →
      (if k = i then i + 1 else if k = i + 1 then i else k) = k := by
    intro k hk; split_ifs <;> omega
  unfold swapVec
  by_cases hT : ∃ U : SYT mu, ∀ k, boxOf U.1 k =
      boxOf T.1 (if k = i then i + 1 else if k = i + 1 then i else k)
  · rw [dif_pos hT]
    have hspec : ∀ k, boxOf (extT h hT.choose).1 k =
        boxOf (extT h T).1 (if k = i then i + 1 else if k = i + 1 then i else k) := by
      intro k
      by_cases hk : k < mu.cells.card
      · rw [extT_spec h _ k hk, hT.choose_spec k, extT_spec h _ _ ((hτ k).mpr hk)]
      · rw [hτfix k hk]
        by_cases hk2 : k = mu.cells.card
        · subst hk2
          have h1 := last_box_mem h _ _ (extT_spec h hT.choose)
          have h2 := last_box_mem h _ _ (extT_spec h T)
          obtain ⟨c, hc⟩ := edge_box h
          rw [hc, Finset.mem_singleton] at h1 h2
          rw [h1, h2]
        · rw [boxOf_ge _ _ (by omega), boxOf_ge _ _ (by omega)]
    have hU : ∃ U : SYT lam, ∀ k, boxOf U.1 k =
        boxOf (extT h T).1 (if k = i then i + 1 else if k = i + 1 then i else k) :=
      ⟨_, hspec⟩
    rw [dif_pos hU]
    have e := embed_vT h hT.choose
    unfold vT at e
    rw [e]
    congr 1
    apply SYT_ext; intro k _
    rw [hU.choose_spec k, hspec k]
  · rw [dif_neg hT, map_zero, dif_neg]
    rintro ⟨U2, hU2⟩
    apply hT
    have hlast : boxOf U2.1 mu.cells.card ∉ mu.cells := by
      rw [hU2, hτfix _ (lt_irrefl _)]
      exact (Finset.mem_sdiff.mp (last_box_mem h T _ (extT_spec h T))).2
    obtain ⟨T2, hT2⟩ := exists_restrict h U2 hlast
    refine ⟨T2, fun k => ?_⟩
    by_cases hk : k < mu.cells.card
    · rw [← hT2 k hk, hU2 k, extT_spec h T _ ((hτ k).mpr hk)]
    · rw [hτfix k hk, boxOf_ge _ _ hk, boxOf_ge _ _ hk]

/-- L1: the embedding intertwines Young's form for labels below `|mu|`. -/
lemma embed_sigma {mu lam : YoungDiagram} (h : YoungEdge mu lam) (i : ℕ)
    (hi : i + 1 < mu.cells.card) :
    embed mu lam ∘ₗ sigma mu i = sigma lam i ∘ₗ embed mu lam := by
  have hcard := edge_card h
  apply Finsupp.lhom_ext'
  intro T
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  have e1 : embed mu lam (Finsupp.single T 1) = Finsupp.single (extT h T) 1 := embed_vT h T
  have e2 := embed_swapVec h T i hi
  have e1' : ∀ c : ℂ, embed mu lam (Finsupp.single T c) = Finsupp.single (extT h T) c := by
    intro c
    rw [show Finsupp.single T c = c • Finsupp.single T (1 : ℂ) by simp, map_smul, e1]; simp
  rw [e1]
  unfold sigma
  rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, one_smul, one_smul]
  have hb1 := extT_spec h T i (by omega)
  have hb2 := extT_spec h T (i+1) hi
  simp only [hb1, hb2, if_pos hi, if_pos (show i + 1 < lam.cells.card by omega), vT]
  split_ifs <;> simp [map_add, map_neg, e1, e1', e2]


/-! ## Signs: inversion counts are `Equiv.Perm.sign` -/

lemma signAux_eq_sign {n : ℕ} (f : Equiv.Perm (Fin n)) :
    Equiv.Perm.signAux f = Equiv.Perm.sign f := by
  induction f using Equiv.Perm.swap_induction_on with
  | one => simp [Equiv.Perm.signAux_one]
  | swap_mul f x y hxy ih =>
    rw [Equiv.Perm.signAux_mul, Equiv.Perm.signAux_swap hxy, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap hxy, ih]

lemma neg_one_pow_inv_eq_sign {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (-1 : ℂ) ^ (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.1 > π p.2)).card =
      ((Equiv.Perm.sign π : ℤ) : ℂ) := by
  rw [← signAux_eq_sign]
  unfold Equiv.Perm.signAux
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one]
  push_cast
  congr 1
  apply Finset.card_nbij' (fun p => (⟨p.2, p.1⟩ : Σ _ : Fin n, Fin n)) (fun x => (x.2, x.1))
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Equiv.Perm.mem_finPairsLT,
      Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx.1, hx.2.le⟩
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Equiv.Perm.mem_finPairsLT,
      Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx.1, lt_of_le_of_ne hx.2 (fun he => (ne_of_gt hx.1) (π.injective he))⟩
  · intro x _; rfl
  · intro x _; rfl

/-! ## Conjugate tableaux -/

lemma transpose_card (lam : YoungDiagram) : lam.transpose.cells.card = lam.cells.card := by
  apply Finset.card_nbij' Prod.swap Prod.swap
  · intro x hx; simpa [YoungDiagram.mem_transpose] using hx
  · intro x hx; simpa [YoungDiagram.mem_transpose] using hx
  · intro x _; rfl
  · intro x _; rfl

lemma exists_conj {lam : YoungDiagram} (T : SYT lam) :
    ∃ U : SYT lam.transpose, ∀ k, k < lam.cells.card → boxOf U.1 k = (boxOf T.1 k).swap := by
  have hc := transpose_card lam
  set m := lam.transpose.cells.card with hm
  let t : Fin m → ℕ × ℕ := fun j => (boxOf T.1 j.val).swap
  have hinj : Function.Injective t := by
    intro i j hij; apply Fin.ext
    exact SYT_boxOf_inj T (by have := i.isLt; omega) (by have := j.isLt; omega)
      (Prod.swap_injective hij)
  have hlow : ∀ m' : ℕ, m' ≤ m → IsLowerSet {b | ∃ i : Fin m, i.val < m' ∧ t i = b} := by
    intro m' hm' a b hba ha
    obtain ⟨i, hi, rfl⟩ := ha
    have hi' : i.val < lam.cells.card := by have := i.isLt; omega
    have ht : t i = (T.1.1 ⟨i.val, hi'⟩).swap := by
      show (boxOf T.1 i.val).swap = _; rw [boxOf_lt _ _ hi']
    rw [ht] at hba
    have hba' : b.swap ≤ T.1.1 ⟨i.val, hi'⟩ := by
      have := Prod.swap_le_swap.mpr hba; simpa using this
    obtain ⟨j, hj, hjb⟩ := T.1.2.2 m' (by omega) hba' ⟨⟨i.val, hi'⟩, hi, rfl⟩
    refine ⟨⟨j.val, by omega⟩, hj, ?_⟩
    show (boxOf T.1 j.val).swap = b
    rw [boxOf_lt _ _ j.isLt, hjb, Prod.swap_swap]
  have himg : Finset.univ.image t = lam.transpose.cells := by
    ext b
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_transpose, Finset.mem_image]
    constructor
    · rintro ⟨i, -, rfl⟩
      rw [← YoungDiagram.mem_cells]
      show (boxOf T.1 i.val).swap.swap ∈ lam.cells
      rw [Prod.swap_swap]; exact SYT_boxOf_mem T _ (by have := i.isLt; omega)
    · intro hb
      obtain ⟨k, hk, hkb⟩ := SYT_exists_of_mem T ((YoungDiagram.mem_cells _).mpr hb)
      exact ⟨⟨k, by omega⟩, Finset.mem_univ _, by
        show (boxOf T.1 k).swap = b; rw [hkb, Prod.swap_swap]⟩
  have hshape : tableauShape (⟨t, hinj, hlow⟩ : YoungTableau m) = lam.transpose := by
    apply YoungDiagram.ext
    exact himg
  refine ⟨⟨⟨t, hinj, hlow⟩, hshape⟩, fun k hk => ?_⟩
  rw [boxOf_lt _ _ (by omega : k < m)]

/-! ## Self-conjugate conjugation `T ↦ T'` -/

lemma exists_conj_sc {lam : YoungDiagram} (hsc : lam.transpose = lam) (T : SYT lam) :
    ∃ U : SYT lam, ∀ k, k < lam.cells.card → boxOf U.1 k = (boxOf T.1 k).swap := by
  have h := exists_conj T
  rw [hsc] at h
  exact h

noncomputable def conjT {lam : YoungDiagram} (hsc : lam.transpose = lam) (T : SYT lam) :
    SYT lam :=
  (exists_conj_sc hsc T).choose

lemma conjT_spec {lam : YoungDiagram} (hsc : lam.transpose = lam) (T : SYT lam) :
    ∀ k, k < lam.cells.card → boxOf (conjT hsc T).1 k = (boxOf T.1 k).swap :=
  (exists_conj_sc hsc T).choose_spec

lemma conjT_conjT {lam : YoungDiagram} (hsc : lam.transpose = lam) (T : SYT lam) :
    conjT hsc (conjT hsc T) = T := by
  apply SYT_ext; intro k hk
  rw [conjT_spec hsc _ k hk, conjT_spec hsc T k hk, Prod.swap_swap]

lemma conjInto_sc {lam : YoungDiagram} (hsc : lam.transpose = lam) (T : SYT lam) :
    conjInto lam T = vT (conjT hsc T) := by
  rw [conjInto, dif_pos ⟨rfl, exists_conj_sc hsc T⟩]
  rfl

lemma phi_vT {lam : YoungDiagram} (hsc : lam.transpose = lam) (T : SYT lam) :
    phi lam (vT T) =
      (Complex.I ^ ((lam.cells.card - diagLen lam) / 2) * signW T) • vT (conjT hsc T) := by
  show phi lam (Finsupp.single T 1) = _
  rw [phi, Finsupp.linearCombination_single, one_smul, conjInto_sc hsc]

/-! ## `labelAt` -/

lemma labelAt_boxOf {lam : YoungDiagram} (T : SYT lam) (k : ℕ) (hk : k < lam.cells.card) :
    labelAt T.1 (boxOf T.1 k) = k := by
  unfold labelAt
  rw [Finset.sum_eq_single ⟨k, hk⟩]
  · simp [boxOf_lt _ _ hk]
  · intro i _ hi
    rw [if_neg]
    intro h; apply hi; apply T.1.2.1; rw [h, boxOf_lt _ _ hk]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma labelAt_of_mem {lam : YoungDiagram} (T : SYT lam) {b : ℕ × ℕ} (hb : b ∈ lam.cells) :
    labelAt T.1 b < lam.cells.card ∧ boxOf T.1 (labelAt T.1 b) = b := by
  obtain ⟨k, hk, rfl⟩ := SYT_exists_of_mem T hb
  rw [labelAt_boxOf T k hk]; exact ⟨hk, rfl⟩

lemma labelAt_inj {lam : YoungDiagram} (T : SYT lam) {b c : ℕ × ℕ} (hb : b ∈ lam.cells)
    (hc : c ∈ lam.cells) (h : labelAt T.1 b = labelAt T.1 c) : b = c := by
  rw [← (labelAt_of_mem T hb).2, ← (labelAt_of_mem T hc).2, h]

lemma labelAt_conjT {lam : YoungDiagram} (hsc : lam.transpose = lam) (T : SYT lam)
    (b : ℕ × ℕ) : labelAt (conjT hsc T).1 b = labelAt T.1 b.swap := by
  unfold labelAt
  apply Finset.sum_congr rfl
  intro i _
  have h := conjT_spec hsc T i.val i.isLt
  rw [boxOf_lt _ _ i.isLt, boxOf_lt _ _ i.isLt] at h
  simp only [Fin.eta] at h
  rw [h]
  by_cases hb : T.1.1 i = b.swap
  · rw [if_pos hb, if_pos (by rw [hb, Prod.swap_swap])]
  · rw [if_neg hb, if_neg (fun e => hb (by rw [← e, Prod.swap_swap]))]

/-! ## The diagonal and the reference boxes -/

lemma diag_mem (lam : YoungDiagram) (h : 0 < diagLen lam) :
    (diagLen lam - 1, diagLen lam - 1) ∈ lam.cells := by
  by_contra hc
  have hsub : lam.cells.filter (fun b => b.1 = b.2) ⊆
      (Finset.range (diagLen lam - 1)).image (fun i => (i, i)) := by
    rintro ⟨i, j⟩ hb
    simp only [Finset.mem_filter] at hb
    obtain ⟨hb, rfl⟩ := hb
    rw [Finset.mem_image]
    refine ⟨i, Finset.mem_range.mpr ?_, rfl⟩
    by_contra hlt; push Not at hlt; apply hc
    exact (YoungDiagram.mem_cells _).mpr (lam.up_left_mem hlt hlt ((YoungDiagram.mem_cells _).mp hb))
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun i j h => by simpa using h), Finset.card_range] at h2
  have h3 : diagLen lam ≤ diagLen lam - 1 := h2
  omega

lemma cellsLex_nodup (lam : YoungDiagram) : (cellsLex lam).Nodup := by
  unfold cellsLex
  exact (Finset.sort_nodup _ _).map ofLex.injective

lemma mem_cellsLex (lam : YoungDiagram) (b : ℕ × ℕ) : b ∈ cellsLex lam ↔ b ∈ lam.cells := by
  unfold cellsLex
  rw [List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Finset.mem_sort, Finset.mem_image] at ha
    obtain ⟨c, hc, rfl⟩ := ha
    simpa using hc
  · intro hb
    exact ⟨toLex b, by rw [Finset.mem_sort, Finset.mem_image]; exact ⟨b, hb, rfl⟩, rfl⟩

lemma cellsLex_length (lam : YoungDiagram) : (cellsLex lam).length = lam.cells.card := by
  unfold cellsLex
  rw [List.length_map, Finset.length_sort, Finset.card_image_of_injective _ toLex.injective]

lemma getD_mem_inj (l : List (ℕ × ℕ)) (hnd : l.Nodup) :
    (∀ k, k < l.length → l.getD k (0, 0) ∈ l) ∧
    (∀ k q, k < l.length → q < l.length → l.getD k (0, 0) = l.getD q (0, 0) → k = q) := by
  have e : ∀ k (hk : k < l.length), l.getD k (0, 0) = l[k] := by
    intro k hk; simp [List.getD_eq_getElem?_getD, hk]
  refine ⟨fun k hk => by rw [e k hk]; exact List.getElem_mem hk, fun k q hk hq h => ?_⟩
  rw [e k hk, e q hq] at h
  exact (hnd.getElem_inj_iff).mp h

lemma refBox_mem_inj (lam : YoungDiagram) :
    (∀ k, k < lam.cells.card → refBox lam k ∈ lam.cells) ∧
    (∀ k q, k < lam.cells.card → q < lam.cells.card → refBox lam k = refBox lam q → k = q) := by
  have hnd := cellsLex_nodup lam
  have hlen := cellsLex_length lam
  by_cases hld : lastDiagRemovable lam
  · set c : ℕ × ℕ := (diagLen lam - 1, diagLen lam - 1) with hcdef
    have hc : c ∈ lam.cells := diag_mem lam hld.1
    have hcl : c ∈ cellsLex lam := (mem_cellsLex lam c).mpr hc
    have hf : (cellsLex lam).filter (fun b => b ≠ c) = (cellsLex lam).erase c := by
      rw [List.Nodup.erase_eq_filter hnd]
      apply List.filter_congr; intro x _; by_cases hx : x = c <;> simp [hx]
    have hnd' : ((cellsLex lam).erase c).Nodup := hnd.erase c
    have hlen' : ((cellsLex lam).erase c).length = lam.cells.card - 1 := by
      rw [List.length_erase_of_mem hcl, hlen]
    have hR : ∀ k, refBox lam k = if k + 1 = lam.cells.card then c
        else ((cellsLex lam).erase c).getD k (0, 0) := by
      intro k; unfold refBox; rw [if_pos hld, hf]
    obtain ⟨gm, gi⟩ := getD_mem_inj _ hnd'
    have memE : ∀ k, k < lam.cells.card → ¬ k + 1 = lam.cells.card →
        ((cellsLex lam).erase c).getD k (0, 0) ∈ lam.cells ∧
          ((cellsLex lam).erase c).getD k (0, 0) ≠ c := by
      intro k hk hk1
      have hm := gm k (by omega)
      rw [hnd.mem_erase_iff] at hm
      exact ⟨(mem_cellsLex lam _).mp hm.2, hm.1⟩
    refine ⟨fun k hk => ?_, fun k q hk hq h => ?_⟩
    · rw [hR k]; split_ifs with hk1
      · exact hc
      · exact (memE k hk hk1).1
    · rw [hR k, hR q] at h
      split_ifs at h with hk1 hq1
      · omega
      · exact absurd h.symm (memE q hq hq1).2
      · exact absurd h (memE k hk hk1).2
      · exact gi k q (by omega) (by omega) h
  · have hR : ∀ k, refBox lam k = (cellsLex lam).getD k (0, 0) := by
      intro k; unfold refBox; rw [if_neg hld]
    obtain ⟨gm, gi⟩ := getD_mem_inj _ hnd
    refine ⟨fun k hk => ?_, fun k q hk hq h => ?_⟩
    · rw [hR k]; exact (mem_cellsLex lam _).mp (gm k (by omega))
    · rw [hR k, hR q] at h; exact gi k q (by omega) (by omega) h

/-! ## `signW` is the sign of a permutation -/

lemma piT_inj {lam : YoungDiagram} (T : SYT lam) :
    Function.Injective (fun p : Fin lam.cells.card =>
      (⟨labelAt T.1 (refBox lam p), (labelAt_of_mem T ((refBox_mem_inj lam).1 p p.isLt)).1⟩ :
        Fin lam.cells.card)) := by
  intro p q h
  simp only [Fin.mk.injEq] at h
  exact Fin.ext ((refBox_mem_inj lam).2 p q p.isLt q.isLt
    (labelAt_inj T ((refBox_mem_inj lam).1 p p.isLt) ((refBox_mem_inj lam).1 q q.isLt) h))

noncomputable def piT {lam : YoungDiagram} (T : SYT lam) : Equiv.Perm (Fin lam.cells.card) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (piT_inj T))

lemma piT_apply {lam : YoungDiagram} (T : SYT lam) (p : Fin lam.cells.card) :
    (piT T p).val = labelAt T.1 (refBox lam p) := rfl

lemma signW_eq_sign {lam : YoungDiagram} (T : SYT lam) :
    signW T = ((Equiv.Perm.sign (piT T) : ℤ) : ℂ) := by
  rw [← neg_one_pow_inv_eq_sign]
  unfold signW
  congr 2

/-! ## L3: `phi^2 = 1` on self-conjugate shapes -/

lemma refBox_surj (lam : YoungDiagram) {b : ℕ × ℕ} (hb : b ∈ lam.cells) :
    ∃ q, q < lam.cells.card ∧ refBox lam q = b := by
  have hsub : (Finset.range lam.cells.card).image (refBox lam) ⊆ lam.cells := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact (refBox_mem_inj lam).1 k (Finset.mem_range.mp hk)
  have hcard : ((Finset.range lam.cells.card).image (refBox lam)).card = lam.cells.card := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro x hx y hy h
    exact (refBox_mem_inj lam).2 x y (by simpa using hx) (by simpa using hy) h
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard])
  rw [← heq] at hb
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
  exact ⟨q, Finset.mem_range.mp hq, rfl⟩

lemma swap_mem_sc {lam : YoungDiagram} (hsc : lam.transpose = lam) {b : ℕ × ℕ}
    (hb : b ∈ lam.cells) : b.swap ∈ lam.cells := by
  have h : b.swap ∈ lam.transpose.cells := by
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_transpose, Prod.swap_swap,
      ← YoungDiagram.mem_cells]
    exact hb
  rw [hsc] at h; exact h

lemma rho_ex {lam : YoungDiagram} (hsc : lam.transpose = lam) (p : Fin lam.cells.card) :
    ∃ q, q < lam.cells.card ∧ refBox lam q = (refBox lam p).swap :=
  refBox_surj lam (swap_mem_sc hsc ((refBox_mem_inj lam).1 p p.isLt))

noncomputable def rhoF {lam : YoungDiagram} (hsc : lam.transpose = lam)
    (p : Fin lam.cells.card) : Fin lam.cells.card :=
  ⟨(rho_ex hsc p).choose, (rho_ex hsc p).choose_spec.1⟩

lemma rhoF_spec {lam : YoungDiagram} (hsc : lam.transpose = lam) (p : Fin lam.cells.card) :
    refBox lam (rhoF hsc p) = (refBox lam p).swap :=
  (rho_ex hsc p).choose_spec.2

lemma rhoF_inj {lam : YoungDiagram} (hsc : lam.transpose = lam) :
    Function.Injective (rhoF hsc) := by
  intro p q h
  have h1 := rhoF_spec hsc p
  rw [h, rhoF_spec hsc q] at h1
  exact Fin.ext ((refBox_mem_inj lam).2 p q p.isLt q.isLt (Prod.swap_injective h1).symm)

noncomputable def rho {lam : YoungDiagram} (hsc : lam.transpose = lam) :
    Equiv.Perm (Fin lam.cells.card) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (rhoF_inj hsc))

lemma rho_spec {lam : YoungDiagram} (hsc : lam.transpose = lam) (p : Fin lam.cells.card) :
    refBox lam (rho hsc p) = (refBox lam p).swap := rhoF_spec hsc p

lemma rho_eq_iff {lam : YoungDiagram} (hsc : lam.transpose = lam) (p q : Fin lam.cells.card) :
    rho hsc p = q ↔ refBox lam q = (refBox lam p).swap := by
  constructor
  · rintro rfl; exact rho_spec hsc p
  · intro h
    rw [← rho_spec hsc p] at h
    exact (Fin.ext ((refBox_mem_inj lam).2 q (rho hsc p) q.isLt (rho hsc p).isLt h)).symm

lemma rho_mul_rho {lam : YoungDiagram} (hsc : lam.transpose = lam) :
    rho hsc * rho hsc = 1 := by
  ext p
  rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  congr 1
  exact (rho_eq_iff hsc _ p).mpr (by rw [rho_spec hsc p, Prod.swap_swap])

lemma piT_conjT {lam : YoungDiagram} (hsc : lam.transpose = lam) (T : SYT lam) :
    piT (conjT hsc T) = piT T * rho hsc := by
  ext p
  rw [Equiv.Perm.mul_apply, piT_apply, piT_apply, labelAt_conjT, rho_spec]

lemma sign_involution {m : ℕ} (σ : Equiv.Perm (Fin m)) (h2 : σ * σ = 1) :
    (Equiv.Perm.sign σ : ℤ) = (-1) ^ (σ.support.card / 2) := by
  by_cases h1 : σ = 1
  · subst h1; simp
  · have ho : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact h2) h1
    obtain ⟨k, hk⟩ := Equiv.Perm.cycleType_prime_order (by rw [ho]; exact Nat.prime_two)
    rw [ho] at hk
    have hs : σ.support.card = (k + 1) * 2 := by
      rw [← Equiv.Perm.sum_cycleType, hk, Multiset.sum_replicate, smul_eq_mul]
    rw [Equiv.Perm.sign_of_cycleType, hk, Multiset.sum_replicate, Multiset.card_replicate,
      smul_eq_mul, hs, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
    push_cast
    rw [pow_add, Even.neg_one_pow ⟨k + 1, by ring⟩, one_mul]

lemma rho_fixed_card {lam : YoungDiagram} (hsc : lam.transpose = lam) :
    (Finset.univ.filter (fun p => rho hsc p = p)).card = diagLen lam := by
  unfold diagLen
  apply Finset.card_bij (fun (p : Fin lam.cells.card) _ => refBox lam p)
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    refine ⟨(refBox_mem_inj lam).1 p p.isLt, ?_⟩
    have h := (rho_eq_iff hsc p p).mp hp.2
    exact congrArg Prod.fst h
  · intro p _ q _ h
    exact Fin.ext ((refBox_mem_inj lam).2 p q p.isLt q.isLt h)
  · intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨q, hq, rfl⟩ := refBox_surj lam hb.1
    refine ⟨⟨q, hq⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (rho_eq_iff hsc _ _).mpr ?_⟩
    show refBox lam q = (refBox lam q).swap
    exact Prod.ext hb.2 hb.2.symm

lemma rho_support_card {lam : YoungDiagram} (hsc : lam.transpose = lam) :
    (rho hsc).support.card = lam.cells.card - diagLen lam := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun p : Fin lam.cells.card => rho hsc p = p)
  rw [rho_fixed_card hsc, Finset.card_univ, Fintype.card_fin] at h
  have hs : (rho hsc).support = Finset.univ.filter (fun p => ¬ rho hsc p = p) := by
    ext p; simp [Equiv.Perm.mem_support]
  rw [hs]; omega

lemma signW_mul_conj {lam : YoungDiagram} (hsc : lam.transpose = lam) (T : SYT lam) :
    signW T * signW (conjT hsc T) = (-1 : ℂ) ^ ((lam.cells.card - diagLen lam) / 2) := by
  rw [signW_eq_sign, signW_eq_sign, piT_conjT, Equiv.Perm.sign_mul, ← Int.cast_mul,
    ← Units.val_mul, ← mul_assoc, Int.units_mul_self, one_mul,
    sign_involution _ (rho_mul_rho hsc), rho_support_card hsc]
  push_cast; rfl

theorem phi_sq {lam : YoungDiagram} (hsc : lam.transpose = lam) :
    phi lam * phi lam = 1 := by
  apply Finsupp.lhom_ext
  intro T c
  have hs : (Finsupp.single T c : V lam) = c • vT T := by
    rw [vT, Finsupp.smul_single_one]
  have hab : (Complex.I ^ ((lam.cells.card - diagLen lam) / 2) * signW T) *
      (Complex.I ^ ((lam.cells.card - diagLen lam) / 2) * signW (conjT hsc T)) = 1 := by
    have h := signW_mul_conj hsc T
    calc _ = (Complex.I * Complex.I) ^ ((lam.cells.card - diagLen lam) / 2) *
          (signW T * signW (conjT hsc T)) := by ring
      _ = 1 := by rw [Complex.I_mul_I, h, ← mul_pow]; norm_num
  rw [hs, Module.End.mul_apply, LinearMap.map_smul, LinearMap.map_smul, phi_vT hsc,
    LinearMap.map_smul, phi_vT hsc, conjT_conjT, smul_smul, smul_smul, mul_assoc, hab, mul_one,
    Module.End.one_apply]

/-! ## L2: `phi` anticommutes with `sigma i` on self-conjugate shapes -/

lemma sigma_vT (lam : YoungDiagram) (i : ℕ) (T : SYT lam) :
    sigma lam i (vT T) =
      (if i + 1 < lam.cells.card then
        (if (boxOf T.1 i).1 = (boxOf T.1 (i + 1)).1 then vT T
         else if (boxOf T.1 i).2 = (boxOf T.1 (i + 1)).2 then -vT T
         else (((boxContent (boxOf T.1 (i + 1)) - boxContent (boxOf T.1 i) : ℤ) : ℂ))⁻¹ • vT T +
           ((Real.sqrt (1 - 1 / (((boxContent (boxOf T.1 (i + 1)) -
              boxContent (boxOf T.1 i) : ℤ)) : ℝ) ^ 2) : ℝ) : ℂ) • swapVec T i)
       else vT T) := by
  show sigma lam i (Finsupp.single T 1) = _
  rw [sigma, Finsupp.linearCombination_single, one_smul]
  all_goals rfl

lemma boxContent_swap (b : ℕ × ℕ) : boxContent b.swap = -boxContent b := by
  simp [boxContent]

lemma swapVec_of {lam : YoungDiagram} (T U : SYT lam) (i : ℕ)
    (hU : ∀ k, boxOf U.1 k = boxOf T.1 (if k = i then i + 1 else if k = i + 1 then i else k)) :
    swapVec T i = vT U := by
  have e : ∀ h : (∃ V : SYT lam, ∀ k, boxOf V.1 k =
      boxOf T.1 (if k = i then i + 1 else if k = i + 1 then i else k)), h.choose = U :=
    fun h => SYT_ext (fun k _ => by rw [h.choose_spec k, hU k])
  unfold swapVec
  rw [dif_pos ⟨U, hU⟩, e]
  rfl

lemma swapVec_none {lam : YoungDiagram} (T : SYT lam) (i : ℕ)
    (h : ¬ ∃ U : SYT lam, ∀ k, boxOf U.1 k =
      boxOf T.1 (if k = i then i + 1 else if k = i + 1 then i else k)) :
    swapVec T i = 0 := by
  unfold swapVec
  rw [dif_neg h]

lemma swap_conj {lam : YoungDiagram} (hsc : lam.transpose = lam) (T U : SYT lam) {i : ℕ}
    (hi : i + 1 < lam.cells.card)
    (hU : ∀ k, boxOf U.1 k = boxOf T.1 (if k = i then i + 1 else if k = i + 1 then i else k)) :
    ∀ k, boxOf (conjT hsc U).1 k =
      boxOf (conjT hsc T).1 (if k = i then i + 1 else if k = i + 1 then i else k) := by
  intro k
  by_cases hk : k < lam.cells.card
  · have hs : (if k = i then i + 1 else if k = i + 1 then i else k) < lam.cells.card := by
      split_ifs <;> omega
    rw [conjT_spec hsc U k hk, hU k, conjT_spec hsc T _ hs]
  · have hs : (if k = i then i + 1 else if k = i + 1 then i else k) = k := by
      split_ifs <;> omega
    rw [hs, boxOf_ge _ _ hk, boxOf_ge _ _ hk]

lemma signW_swap {lam : YoungDiagram} (T U : SYT lam) {i : ℕ} (hi : i + 1 < lam.cells.card)
    (hU : ∀ k, boxOf U.1 k = boxOf T.1 (if k = i then i + 1 else if k = i + 1 then i else k)) :
    signW U = -signW T := by
  have key : ∀ c ∈ lam.cells, labelAt U.1 c =
      (if labelAt T.1 c = i then i + 1 else if labelAt T.1 c = i + 1 then i else labelAt T.1 c) := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := SYT_exists_of_mem T hc
    rw [labelAt_boxOf T k hk]
    have hsw : (if (if k = i then i + 1 else if k = i + 1 then i else k) = i then i + 1
        else if (if k = i then i + 1 else if k = i + 1 then i else k) = i + 1 then i
        else (if k = i then i + 1 else if k = i + 1 then i else k)) = k := by
      split_ifs <;> omega
    have hsk : (if k = i then i + 1 else if k = i + 1 then i else k) < lam.cells.card := by
      split_ifs <;> omega
    have h1 : boxOf U.1 (if k = i then i + 1 else if k = i + 1 then i else k) = boxOf T.1 k := by
      rw [hU, hsw]
    rw [← h1, labelAt_boxOf U _ hsk]
  have hne : (⟨i, by omega⟩ : Fin lam.cells.card) ≠ ⟨i + 1, hi⟩ := by
    intro h; rw [Fin.mk.injEq] at h; omega
  have hperm : piT U = Equiv.swap (⟨i, by omega⟩ : Fin lam.cells.card) ⟨i + 1, hi⟩ * piT T := by
    ext p
    rw [Equiv.Perm.mul_apply, piT_apply, key _ ((refBox_mem_inj lam).1 p p.isLt),
      ← piT_apply T p, Equiv.swap_apply_def]
    generalize piT T p = x
    by_cases h1 : x.val = i
    · have : x = ⟨i, by omega⟩ := Fin.ext h1
      rw [this]; simp
    · by_cases h2 : x.val = i + 1
      · have : x = ⟨i + 1, hi⟩ := Fin.ext h2
        rw [this]; simp
      · rw [if_neg h1, if_neg h2, if_neg (fun e => h1 (by rw [e])),
          if_neg (fun e => h2 (by rw [e]))]
  rw [signW_eq_sign, signW_eq_sign, hperm, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne]
  push_cast; ring

lemma phi_swapVec {lam : YoungDiagram} (hsc : lam.transpose = lam) (T : SYT lam) {i : ℕ}
    (hi : i + 1 < lam.cells.card) :
    phi lam (swapVec T i) =
      -(Complex.I ^ ((lam.cells.card - diagLen lam) / 2) * signW T) •
        swapVec (conjT hsc T) i := by
  by_cases h : ∃ U : SYT lam, ∀ k, boxOf U.1 k =
      boxOf T.1 (if k = i then i + 1 else if k = i + 1 then i else k)
  · obtain ⟨U, hU⟩ := h
    rw [swapVec_of T U i hU, swapVec_of (conjT hsc T) (conjT hsc U) i (swap_conj hsc T U hi hU),
      phi_vT hsc, signW_swap T U hi hU, mul_neg]
  · have h' : ¬ ∃ U : SYT lam, ∀ k, boxOf U.1 k =
        boxOf (conjT hsc T).1 (if k = i then i + 1 else if k = i + 1 then i else k) := by
      rintro ⟨V, hV⟩
      apply h
      refine ⟨conjT hsc V, ?_⟩
      have := swap_conj hsc (conjT hsc T) V hi hV
      rwa [conjT_conjT] at this
    rw [swapVec_none T i h, swapVec_none _ i h', map_zero, smul_zero]

lemma phi_sigma_vT {lam : YoungDiagram} (hsc : lam.transpose = lam) (T : SYT lam) {i : ℕ}
    (hi : i + 1 < lam.cells.card) :
    phi lam (sigma lam i (vT T)) = -(sigma lam i (phi lam (vT T))) := by
  have hA : boxOf (conjT hsc T).1 i = (boxOf T.1 i).swap := conjT_spec hsc T i (by omega)
  have hB : boxOf (conjT hsc T).1 (i + 1) = (boxOf T.1 (i + 1)).swap := conjT_spec hsc T _ hi
  rw [sigma_vT, phi_vT hsc, map_smul, sigma_vT]
  simp only [if_pos hi, hA, hB]
  simp only [Prod.fst_swap, Prod.snd_swap]
  have hab : boxOf T.1 i ≠ boxOf T.1 (i + 1) := fun h => by
    have := SYT_boxOf_inj T (by omega) hi h; omega
  by_cases h1 : (boxOf T.1 i).1 = (boxOf T.1 (i + 1)).1
  · have h2 : (boxOf T.1 i).2 ≠ (boxOf T.1 (i + 1)).2 := fun h => hab (Prod.ext h1 h)
    simp only [if_pos h1, if_neg h2]
    rw [phi_vT hsc, smul_neg, neg_neg]
  · by_cases h2 : (boxOf T.1 i).2 = (boxOf T.1 (i + 1)).2
    · simp only [if_neg h1, if_pos h2]
      rw [map_neg, phi_vT hsc]
    · simp only [if_neg h1, if_neg h2]
      rw [map_add, map_smul, map_smul, phi_vT hsc, phi_swapVec hsc T hi,
        boxContent_swap, boxContent_swap]
      have hr : (-boxContent (boxOf T.1 (i + 1)) - -boxContent (boxOf T.1 i) : ℤ) =
          -(boxContent (boxOf T.1 (i + 1)) - boxContent (boxOf T.1 i)) := by ring
      simp only [hr, Int.cast_neg, neg_sq, inv_neg]
      module

theorem phi_sigma {lam : YoungDiagram} (hsc : lam.transpose = lam) {i : ℕ}
    (hi : i + 1 < lam.cells.card) :
    phi lam ∘ₗ sigma lam i = -(sigma lam i ∘ₗ phi lam) := by
  apply Finsupp.lhom_ext
  intro T c
  have hs : (Finsupp.single T c : V lam) = c • vT T := by
    rw [vT, Finsupp.smul_single_one]
  rw [hs, LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.comp_apply, map_smul, map_smul,
    map_smul, map_smul, phi_sigma_vT hsc T hi, smul_neg]

/-! ## L4: `embed` commutes with `phi` along self-conjugate edges -/

lemma labelAt_extT_old {mu lam : YoungDiagram} (h : YoungEdge mu lam) (T : SYT mu)
    {b : ℕ × ℕ} (hb : b ∈ mu.cells) : labelAt (extT h T).1 b = labelAt T.1 b := by
  obtain ⟨hk, hbk⟩ := labelAt_of_mem T hb
  have hc := edge_card h
  have e : boxOf (extT h T).1 (labelAt T.1 b) = b := by rw [extT_spec h T _ hk, hbk]
  calc labelAt (extT h T).1 b
      = labelAt (extT h T).1 (boxOf (extT h T).1 (labelAt T.1 b)) := by rw [e]
    _ = labelAt T.1 b := labelAt_boxOf _ _ (by omega)

lemma labelAt_extT_new {mu lam : YoungDiagram} (h : YoungEdge mu lam) (T : SYT mu)
    {c : ℕ × ℕ} (hc : lam.cells \ mu.cells = {c}) :
    labelAt (extT h T).1 c = mu.cells.card := by
  have hm := last_box_mem h T _ (extT_spec h T)
  rw [hc, Finset.mem_singleton] at hm
  have hcard := edge_card h
  calc labelAt (extT h T).1 c
      = labelAt (extT h T).1 (boxOf (extT h T).1 mu.cells.card) := by rw [hm]
    _ = mu.cells.card := labelAt_boxOf _ _ (by omega)

lemma conjT_extT {mu lam : YoungDiagram} (hmu : mu.transpose = mu) (hlam : lam.transpose = lam)
    (h : YoungEdge mu lam) (T : SYT mu) :
    conjT hlam (extT h T) = extT h (conjT hmu T) := by
  have hcard := edge_card h
  apply ext_unique h (conjT hmu T)
  · intro k hk
    rw [conjT_spec hlam _ k (by omega), extT_spec h T k hk, conjT_spec hmu T k hk]
  · exact extT_spec h _

lemma diag_iff (lam : YoungDiagram) (j : ℕ) : (j, j) ∈ lam.cells ↔ j < diagLen lam := by
  set S := lam.cells.filter (fun b => b.1 = b.2) with hS
  have hinj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, hS, Finset.mem_filter] at hx hy
    exact Prod.ext hxy (by rw [← hx.2, ← hy.2, hxy])
  have hcard : (S.image Prod.fst).card = diagLen lam := Finset.card_image_of_injOn hinj
  have hmem : ∀ i, i ∈ S.image Prod.fst ↔ (i, i) ∈ lam.cells := by
    intro i
    simp only [Finset.mem_image, hS, Finset.mem_filter]
    constructor
    · rintro ⟨⟨a, b⟩, ⟨hab, he⟩, rfl⟩
      simp only at he; subst he; exact hab
    · intro hi; exact ⟨(i, i), ⟨hi, rfl⟩, rfl⟩
  have hdown : ∀ i k, i ≤ k → (k, k) ∈ lam.cells → (i, i) ∈ lam.cells := by
    intro i k hik hk
    exact (YoungDiagram.mem_cells _).mpr
      (lam.up_left_mem hik hik ((YoungDiagram.mem_cells _).mp hk))
  have hsub : S.image Prod.fst ⊆ Finset.range (diagLen lam) := by
    intro k hk
    rw [Finset.mem_range]
    have hr : Finset.range (k + 1) ⊆ S.image Prod.fst := by
      intro i hi
      rw [hmem]
      exact hdown i k (by rw [Finset.mem_range] at hi; omega) ((hmem k).mp hk)
    have := Finset.card_le_card hr
    rw [Finset.card_range, hcard] at this; omega
  have heq : S.image Prod.fst = Finset.range (diagLen lam) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range, hcard])
  rw [← hmem, heq, Finset.mem_range]

lemma sc_edge {mu lam : YoungDiagram} (hmu : mu.transpose = mu) (hlam : lam.transpose = lam)
    (h : YoungEdge mu lam) :
    lam.cells \ mu.cells = {(diagLen lam - 1, diagLen lam - 1)} ∧ lastDiagRemovable lam ∧
      diagLen lam = diagLen mu + 1 ∧ ¬ lastDiagRemovable mu := by
  obtain ⟨c, hc⟩ := edge_box h
  have hcin : c ∈ lam.cells \ mu.cells := by rw [hc]; exact Finset.mem_singleton_self c
  have hcl : c ∈ lam.cells := (Finset.mem_sdiff.mp hcin).1
  have hcm : c ∉ mu.cells := (Finset.mem_sdiff.mp hcin).2
  have hlm : ∀ b, b ∈ lam.cells → b ≠ c → b ∈ mu.cells := by
    intro b hb hbc
    by_contra hbm
    have : b ∈ lam.cells \ mu.cells := Finset.mem_sdiff.mpr ⟨hb, hbm⟩
    rw [hc, Finset.mem_singleton] at this; exact hbc this
  have dl : ∀ {i j i' j' : ℕ}, i' ≤ i → j' ≤ j → (i, j) ∈ lam.cells → (i', j') ∈ lam.cells :=
    fun hi hj hm => (YoungDiagram.mem_cells _).mpr
      (lam.up_left_mem hi hj ((YoungDiagram.mem_cells _).mp hm))
  have dm : ∀ {i j i' j' : ℕ}, i' ≤ i → j' ≤ j → (i, j) ∈ mu.cells → (i', j') ∈ mu.cells :=
    fun hi hj hm => (YoungDiagram.mem_cells _).mpr
      (mu.up_left_mem hi hj ((YoungDiagram.mem_cells _).mp hm))
  have hdiag : c.swap = c := by
    by_contra hne
    exact hcm (by simpa using swap_mem_sc hmu (hlm _ (swap_mem_sc hlam hcl) hne))
  obtain ⟨j, j'⟩ := c
  have hjj : j' = j := congrArg Prod.fst hdiag
  subst hjj
  have hjd : j' < diagLen lam := (diag_iff lam j').mp hcl
  have hd : diagLen lam = j' + 1 := by
    by_contra hne
    have h1 : (j' + 1, j' + 1) ∈ lam.cells := (diag_iff lam _).mpr (by omega)
    exact hcm (dm (Nat.le_succ j') (Nat.le_succ j')
      (hlm _ h1 (by intro he; simp only [Prod.mk.injEq] at he; omega)))
  have hdm : diagLen mu = j' := by
    apply le_antisymm
    · by_contra hlt
      exact hcm ((diag_iff mu j').mpr (not_le.mp hlt))
    · by_contra hlt
      have hlt' := not_le.mp hlt
      have h1 : (diagLen mu, diagLen mu) ∈ lam.cells := (diag_iff lam _).mpr (by omega)
      have h2 := hlm _ h1 (by intro he; simp only [Prod.mk.injEq] at he; omega)
      exact absurd ((diag_iff mu _).mp h2) (lt_irrefl _)
  have hld : lastDiagRemovable lam := by
    unfold lastDiagRemovable
    rw [hd, Nat.add_sub_cancel]
    refine ⟨by omega, fun hm => ?_, fun hm => ?_⟩
    · exact hcm (dm le_rfl (Nat.le_succ j')
        (hlm _ hm (by intro he; simp only [Prod.mk.injEq] at he; omega)))
    · exact hcm (dm (Nat.le_succ j') le_rfl
        (hlm _ hm (by intro he; simp only [Prod.mk.injEq] at he; omega)))
  refine ⟨by rw [hd, Nat.add_sub_cancel]; exact hc, hld, by rw [hd, hdm], ?_⟩
  intro hm
  unfold lastDiagRemovable at hm
  obtain ⟨h0, h1, -⟩ := hm
  rw [hdm] at h0 h1
  apply h1
  exact hlm _ (dl (Nat.sub_le j' 1) le_rfl hcl)
    (by intro he; simp only [Prod.mk.injEq] at he; omega)

lemma cellsLex_filter {mu lam : YoungDiagram} (h : YoungEdge mu lam) {c : ℕ × ℕ}
    (hc : lam.cells \ mu.cells = {c}) :
    (cellsLex lam).filter (fun b => b ≠ c) = cellsLex mu := by
  have hcin : c ∈ lam.cells \ mu.cells := by rw [hc]; exact Finset.mem_singleton_self c
  have hlm : ∀ b, (b ∈ lam.cells ∧ b ≠ c) ↔ b ∈ mu.cells := by
    intro b; constructor
    · rintro ⟨hb, hbc⟩
      by_contra hbm
      have : b ∈ lam.cells \ mu.cells := Finset.mem_sdiff.mpr ⟨hb, hbm⟩
      rw [hc, Finset.mem_singleton] at this; exact hbc this
    · intro hb
      exact ⟨edge_subset h hb, fun e => (Finset.mem_sdiff.mp hcin).2 (e ▸ hb)⟩
  unfold cellsLex
  rw [List.filter_map]
  congr 1
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · exact (Finset.pairwise_sort _ _).filter _
  · exact Finset.pairwise_sort _ _
  · rw [List.perm_ext_iff_of_nodup ((Finset.sort_nodup _ _).filter _) (Finset.sort_nodup _ _)]
    intro x
    obtain ⟨y, rfl⟩ := toLex.surjective x
    rw [List.mem_filter, Finset.mem_sort, Finset.mem_sort, Finset.mem_image, Finset.mem_image]
    simp only [EmbeddingLike.apply_eq_iff_eq, exists_eq_right, Function.comp_apply,
      ofLex_toLex, decide_eq_true_eq]
    exact ⟨fun hh => (hlm y).mp ⟨hh.1, of_decide_eq_true hh.2⟩,
      fun hh => ⟨((hlm y).mpr hh).1, decide_eq_true ((hlm y).mpr hh).2⟩⟩

lemma refBox_sc_edge {mu lam : YoungDiagram} (hmu : mu.transpose = mu)
    (hlam : lam.transpose = lam) (h : YoungEdge mu lam) {k : ℕ} (hk : k < mu.cells.card) :
    refBox lam k = refBox mu k := by
  obtain ⟨hc, hld, -, hnmu⟩ := sc_edge hmu hlam h
  have hcard := edge_card h
  unfold refBox
  rw [if_pos hld, if_neg (show ¬ (k + 1 = lam.cells.card) by omega), if_neg hnmu,
    cellsLex_filter h hc]

lemma refBox_sc_last {mu lam : YoungDiagram} (hmu : mu.transpose = mu)
    (hlam : lam.transpose = lam) (h : YoungEdge mu lam) :
    refBox lam mu.cells.card = (diagLen lam - 1, diagLen lam - 1) := by
  obtain ⟨-, hld, -, -⟩ := sc_edge hmu hlam h
  have hcard := edge_card h
  unfold refBox
  rw [if_pos hld, if_pos (show mu.cells.card + 1 = lam.cells.card by omega)]

lemma signW_extT_sc {mu lam : YoungDiagram} (hmu : mu.transpose = mu)
    (hlam : lam.transpose = lam) (h : YoungEdge mu lam) (T : SYT mu) :
    signW (extT h T) = signW T := by
  obtain ⟨hc, -, -, -⟩ := sc_edge hmu hlam h
  have hcard := edge_card h
  unfold signW
  congr 1
  symm
  apply Finset.card_bij (fun (p : Fin mu.cells.card × Fin mu.cells.card) _ =>
    ((⟨p.1.val, by omega⟩ : Fin lam.cells.card), (⟨p.2.val, by omega⟩ : Fin lam.cells.card)))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [refBox_sc_edge hmu hlam h p.1.isLt, refBox_sc_edge hmu hlam h p.2.isLt,
      labelAt_extT_old h T ((refBox_mem_inj mu).1 _ p.1.isLt),
      labelAt_extT_old h T ((refBox_mem_inj mu).1 _ p.2.isLt)]
    exact ⟨Fin.lt_def.mpr (Fin.lt_def.mp hp.1), hp.2⟩
  · intro a _ b _ hab
    simp only [Prod.mk.injEq, Fin.mk.injEq] at hab
    exact Prod.ext (Fin.ext hab.1) (Fin.ext hab.2)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    have h2 : q.2.val < mu.cells.card := by
      by_contra hne
      have he : q.2.val = mu.cells.card := by have := q.2.isLt; omega
      have hq2 := hq.2
      rw [he, refBox_sc_last hmu hlam h, labelAt_extT_new h T hc] at hq2
      have := (labelAt_of_mem (extT h T) ((refBox_mem_inj lam).1 q.1 q.1.isLt)).1
      omega
    have h1 : q.1.val < mu.cells.card := lt_trans (Fin.lt_def.mp hq.1) h2
    refine ⟨(⟨q.1.val, h1⟩, ⟨q.2.val, h2⟩), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hq2 := hq.2
    rw [refBox_sc_edge hmu hlam h h1, refBox_sc_edge hmu hlam h h2,
      labelAt_extT_old h T ((refBox_mem_inj mu).1 _ h1),
      labelAt_extT_old h T ((refBox_mem_inj mu).1 _ h2)] at hq2
    exact ⟨Fin.lt_def.mpr (Fin.lt_def.mp hq.1), hq2⟩

theorem embed_phi {mu lam : YoungDiagram} (hmu : mu.transpose = mu)
    (hlam : lam.transpose = lam) (h : YoungEdge mu lam) :
    embed mu lam ∘ₗ phi mu = phi lam ∘ₗ embed mu lam := by
  obtain ⟨-, -, hdl, -⟩ := sc_edge hmu hlam h
  have hcard := edge_card h
  have hexp : (lam.cells.card - diagLen lam) / 2 = (mu.cells.card - diagLen mu) / 2 := by
    rw [hcard, hdl, Nat.add_sub_add_right]
  apply Finsupp.lhom_ext
  intro T c
  have hs : (Finsupp.single T c : V mu) = c • vT T := by
    rw [vT, Finsupp.smul_single_one]
  rw [hs, LinearMap.comp_apply, LinearMap.comp_apply]
  simp only [map_smul, phi_vT hmu, phi_vT hlam, embed_vT h, signW_extT_sc hmu hlam h, hexp,
    conjT_extT hmu hlam h]


/-! ## Part 1 helpers -/

lemma embed_eq_mapDomain {mu lam : YoungDiagram} (h : YoungEdge mu lam) :
    embed mu lam = Finsupp.lmapDomain ℂ ℂ (extT h) := by
  apply Finsupp.lhom_ext
  intro T c
  have hs : (Finsupp.single T c : V mu) = c • vT T := by rw [vT, Finsupp.smul_single_one]
  rw [hs, map_smul, map_smul, embed_vT h, Finsupp.lmapDomain_apply]
  simp only [vT, Finsupp.mapDomain_single]

lemma embed_injective {mu lam : YoungDiagram} (h : YoungEdge mu lam) :
    Function.Injective (embed mu lam) := by
  intro x y hxy
  rw [embed_eq_mapDomain h, Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply] at hxy
  exact Finsupp.mapDomain_injective (extT_injective h) hxy

lemma embed_equiv {mu lam : YoungDiagram} (h : YoungEdge mu lam) {k : ℕ}
    (hk : k ≤ mu.cells.card) : IsAltEquivariant k (embed mu lam) := by
  intro i j hi hj
  apply LinearMap.ext; intro x
  have e1 := LinearMap.congr_fun (embed_sigma h i (by omega))
  have e2 := LinearMap.congr_fun (embed_sigma h j (by omega))
  simp only [LinearMap.comp_apply] at e1 e2
  simp only [LinearMap.comp_apply, Module.End.mul_apply]
  rw [e1, e2]

lemma equiv_mono {k k' : ℕ} {mu lam : YoungDiagram} {f : V mu →ₗ[ℂ] V lam}
    (hf : IsAltEquivariant k f) (hk : k' ≤ k) : IsAltEquivariant k' f :=
  fun i j hi hj => hf i j (by omega) (by omega)

lemma equiv_comp {k : ℕ} {A B C : YoungDiagram} {f : V A →ₗ[ℂ] V B} {g : V B →ₗ[ℂ] V C}
    (hf : IsAltEquivariant k f) (hg : IsAltEquivariant k g) : IsAltEquivariant k (g ∘ₗ f) := by
  intro i j hi hj
  apply LinearMap.ext; intro x
  have e1 := LinearMap.congr_fun (hf i j hi hj) x
  have e2 := LinearMap.congr_fun (hg i j hi hj) (f x)
  simp only [LinearMap.comp_apply] at e1 e2 ⊢
  rw [e1, e2]

/-- `1 ± φ`. -/
noncomputable def pm (lam : YoungDiagram) (s : Bool) : Module.End ℂ (V lam) :=
  1 + (if s then (1 : ℂ) else -1) • phi lam

lemma pm_apply (lam : YoungDiagram) (s : Bool) (x : V lam) :
    pm lam s x = x + (if s then (1 : ℂ) else -1) • phi lam x := by
  simp only [pm, LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply]

lemma phi_comm_sigma2 {lam : YoungDiagram} (hsc : lam.transpose = lam) {i j : ℕ}
    (hi : i + 1 < lam.cells.card) (hj : j + 1 < lam.cells.card) (x : V lam) :
    phi lam (sigma lam i (sigma lam j x)) = sigma lam i (sigma lam j (phi lam x)) := by
  have e1 := LinearMap.congr_fun (phi_sigma hsc hi)
  have e2 := LinearMap.congr_fun (phi_sigma hsc hj)
  simp only [LinearMap.comp_apply, LinearMap.neg_apply] at e1 e2
  rw [e1, e2, map_neg, neg_neg]

lemma pm_equiv {lam : YoungDiagram} (hsc : lam.transpose = lam) (s : Bool) {k : ℕ}
    (hk : k ≤ lam.cells.card) : IsAltEquivariant k (pm lam s) := by
  intro i j hi hj
  apply LinearMap.ext; intro x
  simp only [LinearMap.comp_apply, Module.End.mul_apply, pm_apply, map_add, map_smul,
    phi_comm_sigma2 hsc (i := i) (j := j) (by omega) (by omega)]

lemma phi_phi {lam : YoungDiagram} (hsc : lam.transpose = lam) (y : V lam) :
    phi lam (phi lam y) = y := by
  have := LinearMap.congr_fun (phi_sq hsc) y
  simpa only [Module.End.mul_apply, Module.End.one_apply] using this

lemma mem_Vpm {lam : YoungDiagram} {s : Bool} {x : V lam} :
    x ∈ Vpm lam s ↔ phi lam x = (if s then (1 : ℂ) else -1) • x := by
  rw [Vpm, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    sub_eq_zero]

lemma pm_mem {lam : YoungDiagram} (hsc : lam.transpose = lam) (s : Bool) (x : V lam) :
    pm lam s x ∈ Vpm lam s := by
  rw [mem_Vpm, pm_apply, map_add, map_smul, phi_phi hsc]
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> module

lemma phi_apply {lam : YoungDiagram} (hsc : lam.transpose = lam) (v : V lam) (T : SYT lam) :
    phi lam v T = (Complex.I ^ ((lam.cells.card - diagLen lam) / 2) * signW (conjT hsc T)) *
      v (conjT hsc T) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, Finsupp.add_apply, hf, hg, Finsupp.add_apply, mul_add]
  | single U c =>
    have hs : (Finsupp.single U c : V lam) = c • vT U := by rw [vT, Finsupp.smul_single_one]
    rw [hs, map_smul, phi_vT hsc]
    simp only [Finsupp.smul_apply, vT, smul_eq_mul, Finsupp.single_apply]
    by_cases hU : conjT hsc U = T
    · subst hU
      simp only [conjT_conjT]
      simp
      try ring
    · have hU' : U ≠ conjT hsc T := fun e => hU (by rw [e, conjT_conjT])
      simp [hU, Ne.symm hU, hU', Ne.symm hU']

lemma nsc_edge_offdiag {mu lam : YoungDiagram} (hlam : lam.transpose = lam)
    (hmu : mu.transpose ≠ mu) (h : YoungEdge mu lam) {c : ℕ × ℕ}
    (hc : lam.cells \ mu.cells = {c}) : c.swap ≠ c := by
  intro hcc
  apply hmu
  have hcin : c ∈ lam.cells \ mu.cells := by rw [hc]; exact Finset.mem_singleton_self c
  have hlm : ∀ b, b ∈ mu.cells ↔ b ∈ lam.cells ∧ b ≠ c := by
    intro b; constructor
    · intro hb; exact ⟨edge_subset h hb, fun e => (Finset.mem_sdiff.mp hcin).2 (e ▸ hb)⟩
    · rintro ⟨hb, hbc⟩
      by_contra hbm
      have : b ∈ lam.cells \ mu.cells := Finset.mem_sdiff.mpr ⟨hb, hbm⟩
      rw [hc, Finset.mem_singleton] at this; exact hbc this
  apply YoungDiagram.ext
  ext b
  have e1 : b ∈ mu.transpose.cells ↔ b.swap ∈ mu.cells := by
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_transpose, YoungDiagram.mem_cells]
  rw [e1, hlm, hlm]
  constructor
  · rintro ⟨hb, hbc⟩
    refine ⟨by simpa using swap_mem_sc hlam hb, fun e => hbc (by rw [e, hcc])⟩
  · rintro ⟨hb, hbc⟩
    refine ⟨swap_mem_sc hlam hb, fun e => hbc ?_⟩
    rw [← Prod.swap_swap b, e, hcc]

lemma pm_embed_ne_zero {mu lam : YoungDiagram} (hlam : lam.transpose = lam)
    (hmu : mu.transpose ≠ mu) (h : YoungEdge mu lam) (s : Bool) {x : V mu} (hx : x ≠ 0) :
    pm lam s (embed mu lam x) ≠ 0 := by
  obtain ⟨c, hc⟩ := edge_box h
  have hoff := nsc_edge_offdiag hlam hmu h hc
  have hcard := edge_card h
  obtain ⟨T0, hT0⟩ : ∃ T0, x T0 ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hx (Finsupp.ext hne)
  have hlast : ∀ V : SYT mu, boxOf (extT h V).1 mu.cells.card = c := by
    intro V
    have hm := last_box_mem h V _ (extT_spec h V)
    rwa [hc, Finset.mem_singleton] at hm
  have hnot : conjT hlam (extT h T0) ∉ Set.range (extT h) := by
    rintro ⟨V, hV⟩
    have h1 := hlast V
    rw [hV, conjT_spec hlam _ _ (by omega), hlast T0] at h1
    exact hoff h1
  have hval : (embed mu lam x) (extT h T0) = x T0 := by
    rw [embed_eq_mapDomain h, Finsupp.lmapDomain_apply, Finsupp.mapDomain_apply (extT_injective h)]
  have hval2 : (embed mu lam x) (conjT hlam (extT h T0)) = 0 := by
    rw [embed_eq_mapDomain h, Finsupp.lmapDomain_apply]
    exact Finsupp.mapDomain_of_notMem_range _ _ hnot
  have hev : (pm lam s (embed mu lam x)) (extT h T0) = x T0 := by
    rw [pm_apply, Finsupp.add_apply, Finsupp.smul_apply, phi_apply hlam, hval, hval2]
    simp
  intro hz
  rw [hz, Finsupp.zero_apply] at hev
  exact hT0 hev.symm

lemma mem_Iso_of {k : ℕ} {mu lam : YoungDiagram} (W : Submodule ℂ (V mu))
    (f : V mu →ₗ[ℂ] V lam) (hf : IsAltEquivariant k f) {x : V mu} (hx : x ∈ W) :
    f x ∈ Iso k W lam := by
  unfold Iso
  exact Submodule.mem_iSup_of_mem f (Submodule.mem_iSup_of_mem hf (Submodule.mem_map_of_mem hx))

lemma map_Iso {k : ℕ} {nu mu lam : YoungDiagram} (W : Submodule ℂ (V nu))
    (F : V mu →ₗ[ℂ] V lam) (hF : IsAltEquivariant k F) {x : V mu} (hx : x ∈ Iso k W mu) :
    F x ∈ Iso k W lam := by
  unfold Iso at hx ⊢
  have key : (⨆ (f : V nu →ₗ[ℂ] V mu) (_ : IsAltEquivariant k f), W.map f).map F ≤
      ⨆ (f : V nu →ₗ[ℂ] V lam) (_ : IsAltEquivariant k f), W.map f := by
    rw [Submodule.map_iSup]
    apply iSup_le; intro f
    rw [Submodule.map_iSup]
    apply iSup_le; intro hf
    rw [← Submodule.map_comp]
    exact le_iSup₂_of_le (F ∘ₗ f) (equiv_comp hf hF) le_rfl
  exact key (Submodule.mem_map_of_mem hx)

lemma path_size : ∀ (p : List Label) (b : Label), IsPath b p → ∀ c ∈ p, c.size < b.size := by
  intro p
  induction p with
  | nil => intro b _ c hc; simp at hc
  | cons b0 rest ih =>
    intro b hp c hc
    have hp' : Dagger b b0 ∧ IsPath b0 rest := hp
    have he := edge_card hp'.1.1
    have hs : b0.size < b.size := by unfold Label.size; omega
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact hs
    · exact lt_trans (ih b0 hp'.2 c hc') hs

/-! ## Size two -/

lemma corner_mem (lam : YoungDiagram) (h : 0 < lam.cells.card) :
    ((0 : ℕ), (0 : ℕ)) ∈ lam.cells := by
  obtain ⟨b, hb⟩ := Finset.card_pos.mp h
  exact (YoungDiagram.mem_cells _).mpr
    (lam.up_left_mem (Nat.zero_le b.1) (Nat.zero_le b.2) ((YoungDiagram.mem_cells _).mp hb))

lemma two_cells {lam : YoungDiagram} (h2 : lam.cells.card = 2) :
    ∃ b, b ≠ ((0 : ℕ), (0 : ℕ)) ∧ lam.cells = {(0, 0), b} := by
  have h00 := corner_mem lam (by omega)
  obtain ⟨b, hb, hb0⟩ :=
    Finset.exists_mem_ne (show 1 < lam.cells.card by omega) ((0 : ℕ), (0 : ℕ))
  refine ⟨b, hb0, (Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    exacts [h00, hb]
  · rw [h2, Finset.card_pair_eq_two_iff.mpr hb0.symm]

lemma not_sc_two {lam : YoungDiagram} (hsc : lam.transpose = lam) : lam.cells.card ≠ 2 := by
  intro h2
  have h00 := corner_mem lam (by omega)
  obtain ⟨b, hb0, hcells⟩ := two_cells h2
  have hb : b ∈ lam.cells := by rw [hcells]; simp
  have dl : ∀ {i j i' j' : ℕ}, i' ≤ i → j' ≤ j → (i, j) ∈ lam.cells → (i', j') ∈ lam.cells :=
    fun hi hj hm => (YoungDiagram.mem_cells _).mpr
      (lam.up_left_mem hi hj ((YoungDiagram.mem_cells _).mp hm))
  have key : ((1 : ℕ), (0 : ℕ)) ∈ lam.cells ∧ ((0 : ℕ), (1 : ℕ)) ∈ lam.cells := by
    obtain ⟨i, j⟩ := b
    by_cases hi : 1 ≤ i
    · have h10 : ((1 : ℕ), (0 : ℕ)) ∈ lam.cells := dl hi (Nat.zero_le _) hb
      exact ⟨h10, by simpa using swap_mem_sc hsc h10⟩
    · have hj : 1 ≤ j := by
        by_contra hj
        apply hb0
        simp only [Prod.mk.injEq]; omega
      have h01 : ((0 : ℕ), (1 : ℕ)) ∈ lam.cells := dl (Nat.zero_le _) hj hb
      exact ⟨by simpa using swap_mem_sc hsc h01, h01⟩
  have hsub : ({(0, 0), (1, 0), (0, 1)} : Finset (ℕ × ℕ)) ⊆ lam.cells := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    exacts [h00, key.1, key.2]
  have h3 := Finset.card_le_card hsub
  have h3' : ({(0, 0), (1, 0), (0, 1)} : Finset (ℕ × ℕ)).card = 3 := by decide
  omega

lemma syt_two_nonempty {lam : YoungDiagram} (h2 : lam.cells.card = 2) : Nonempty (SYT lam) := by
  obtain ⟨b, hb0, hcells⟩ := two_cells h2
  let t : Fin lam.cells.card → ℕ × ℕ := fun i => if i.val = 0 then (0, 0) else b
  have hinj : Function.Injective t := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    apply Fin.ext
    by_cases h1 : i.val = 0 <;> by_cases h1' : j.val = 0 <;> simp [t, h1, h1'] at hij <;>
      first | omega | exact absurd hij.symm hb0 | exact absurd hij hb0
  have hlow : ∀ m : ℕ, m ≤ lam.cells.card →
      IsLowerSet {x | ∃ i : Fin lam.cells.card, i.val < m ∧ t i = x} := by
    intro m hm x y hyx hx
    obtain ⟨i, hi, rfl⟩ := hx
    by_cases hi0 : i.val = 0
    · have htx : t i = (0, 0) := by simp [t, hi0]
      rw [htx] at hyx
      have hy : y = (0, 0) := le_antisymm hyx (Prod.le_def.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩)
      exact ⟨i, hi, by rw [htx, hy]⟩
    · have hm2 : m = 2 := by have := i.isLt; omega
      have hb : b ∈ lam.cells := by rw [hcells]; simp
      have htx : t i = b := by simp [t, hi0]
      have hy : y ∈ lam.cells := lam.isLowerSet hyx (by rw [htx]; exact hb)
      rw [hcells] at hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact ⟨⟨0, by omega⟩, (show (0 : ℕ) < m by omega), by simp [t]⟩
      · exact ⟨i, hi, htx⟩
  let T : YoungTableau lam.cells.card := ⟨t, hinj, hlow⟩
  refine ⟨⟨T, ?_⟩⟩
  apply YoungDiagram.ext
  show Finset.univ.image t = lam.cells
  ext x
  have hx : x ∈ lam.cells ↔ x = (0, 0) ∨ x = b := by rw [hcells]; simp
  rw [hx]
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi0 : i.val = 0
    · left; simp [t, hi0]
    · right; simp [t, hi0]
  · rintro (rfl | rfl)
    · exact ⟨⟨0, by omega⟩, by simp [t]⟩
    · exact ⟨⟨1, by omega⟩, by simp [t]⟩

lemma embed_Vpm {mu lam : YoungDiagram} (hmu : mu.transpose = mu) (hlam : lam.transpose = lam)
    (h : YoungEdge mu lam) {s : Bool} {u : V mu} (hu : u ∈ Vpm mu s) :
    embed mu lam u ∈ Vpm lam s := by
  rw [mem_Vpm] at hu ⊢
  have e := LinearMap.congr_fun (embed_phi hmu hlam h) u
  simp only [LinearMap.comp_apply] at e
  rw [← e, hu, map_smul]

/-! ## Part 1 -/

theorem part1 : ∀ (p : List Label) (a : Label), IsPath a p →
    uVec a p ≠ 0 ∧ uVec a p ∈ a.space ∧ ∀ b ∈ p, uVec a p ∈ Iso b.size b.space a.shape := by
  intro p
  induction p with
  | nil =>
    intro a ha
    have ha' : a.size = 2 := ha
    have hne : Nonempty (SYT a.shape) := syt_two_nonempty ha'
    refine ⟨?_, ?_, fun b hb => by simp at hb⟩
    · have hu : uVec a [] = if h : a.size = 2 ∧ Nonempty (SYT a.shape) then
          Finsupp.single (Classical.choice h.2) 1 else 0 := rfl
      rw [hu, dif_pos ⟨ha', hne⟩]
      exact Finsupp.single_ne_zero.mpr one_ne_zero
    · cases a with
      | nsc lam h => exact Submodule.mem_top
      | sc lam h s => exact absurd ha' (not_sc_two h)
  | cons b0 rest ih =>
    intro a ha
    have ha' : Dagger a b0 ∧ IsPath b0 rest := ha
    obtain ⟨hu0, hsp0, hiso0⟩ := ih b0 ha'.2
    have hsz : ∀ c ∈ rest, c.size ≤ b0.size :=
      fun c hc => le_of_lt (path_size rest b0 ha'.2 c hc)
    suffices H : ∃ F : V b0.shape →ₗ[ℂ] V a.shape, IsAltEquivariant b0.size F ∧
        uVec a (b0 :: rest) = F (uVec b0 rest) ∧ F (uVec b0 rest) ≠ 0 ∧
        F (uVec b0 rest) ∈ a.space by
      obtain ⟨F, hF, he, hne, hsp⟩ := H
      rw [he]
      refine ⟨hne, hsp, fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact mem_Iso_of _ F hF hsp0
      · exact map_Iso _ F (equiv_mono hF (hsz b hb')) (hiso0 b hb')
    have hedge : YoungEdge b0.shape a.shape := ha'.1.1
    have hne_emb : embed b0.shape a.shape (uVec b0 rest) ≠ 0 := fun hz =>
      hu0 (embed_injective hedge (hz.trans (map_zero _).symm))
    cases a with
    | nsc lam hl =>
      exact ⟨embed b0.shape lam, embed_equiv hedge le_rfl, by cases b0 <;> rfl, hne_emb,
        Submodule.mem_top⟩
    | sc lam hl s =>
      cases b0 with
      | nsc mu hm =>
        refine ⟨pm lam s ∘ₗ embed mu lam,
          equiv_comp (embed_equiv hedge le_rfl)
            (pm_equiv hl s (by have := edge_card hedge; unfold Label.size; simp only [Label.shape] at this ⊢; omega)),
          by show _ = pm lam s (embed mu lam (uVec (Label.nsc mu hm) rest)); rw [pm_apply]; rfl,
          pm_embed_ne_zero hl hm hedge s hu0,
          pm_mem hl s _⟩
      | sc mu hm t =>
        have hst : s = t := ha'.1.2
        subst hst
        exact ⟨embed mu lam, embed_equiv hedge le_rfl, rfl, hne_emb,
          embed_Vpm hm hl hedge (u := uVec (Label.sc mu hm s) rest) hsp0⟩


end Lib
end GTAlternating.Bases


set_option autoImplicit false

namespace GTAlternating.Bases
namespace Lib

open Classical QAlgorithms.Papers.Independent.Renew46.P26

/-! ## Part 2a: label-indexed lex sign `epsL`, the conjugation map `Cinto`,
its compatibility with `embed` (b), and `phi = K • Cinto` on self-conjugate shapes (c). -/

noncomputable def epsG {lam : YoungDiagram} (T : SYT lam) (k l : ℕ) : ℂ :=
  if k < l ∧ toLex (boxOf T.1 l) < toLex (boxOf T.1 k) then -1 else 1

noncomputable def epsL {lam : YoungDiagram} (T : SYT lam) : ℂ :=
  ∏ i ∈ Finset.range lam.cells.card, ∏ j ∈ Finset.range lam.cells.card, epsG T i j

noncomputable def lexrank (lam : YoungDiagram) (b : ℕ × ℕ) : ℕ :=
  (lam.cells.filter (fun e => toLex e < toLex b)).card

lemma lexrank_lt_card {lam : YoungDiagram} {b : ℕ × ℕ} (hb : b ∈ lam.cells) :
    lexrank lam b < lam.cells.card :=
  Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨b, hb, lt_irrefl _⟩)

lemma lexrank_strictMono {lam : YoungDiagram} {b b' : ℕ × ℕ} (hb : b ∈ lam.cells)
    (h : toLex b < toLex b') : lexrank lam b < lexrank lam b' := by
  have hsub : lam.cells.filter (fun e => toLex e < toLex b) ⊆
      lam.cells.filter (fun e => toLex e < toLex b') := by
    intro e he
    simp only [Finset.mem_filter] at he ⊢
    exact ⟨he.1, he.2.trans h⟩
  exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2
    ⟨b, Finset.mem_filter.2 ⟨hb, h⟩, fun h' => lt_irrefl _ (Finset.mem_filter.1 h').2⟩)

lemma lexrank_lt_iff {lam : YoungDiagram} {b b' : ℕ × ℕ} (hb : b ∈ lam.cells)
    (hb' : b' ∈ lam.cells) : lexrank lam b < lexrank lam b' ↔ toLex b < toLex b' := by
  refine ⟨fun h => ?_, lexrank_strictMono hb⟩
  rcases lt_trichotomy (toLex b) (toLex b') with h1 | h1 | h1
  · exact h1
  · have : b = b' := toLex.injective h1
    subst this; exact absurd h (lt_irrefl _)
  · exact absurd h (not_lt.2 (lexrank_strictMono hb' h1).le)

lemma lexrank_inj {lam : YoungDiagram} {b b' : ℕ × ℕ} (hb : b ∈ lam.cells)
    (hb' : b' ∈ lam.cells) (h : lexrank lam b = lexrank lam b') : b = b' := by
  rcases lt_trichotomy (toLex b) (toLex b') with h1 | h1 | h1
  · exact absurd h (ne_of_lt (lexrank_strictMono hb h1))
  · exact toLex.injective h1
  · exact absurd h.symm (ne_of_lt (lexrank_strictMono hb' h1))

lemma lexP_inj {lam : YoungDiagram} (T : SYT lam) :
    Function.Injective (fun l : Fin lam.cells.card =>
      (⟨lexrank lam (boxOf T.1 l), lexrank_lt_card (SYT_boxOf_mem T l l.isLt)⟩ :
        Fin lam.cells.card)) := by
  intro p q h
  simp only [Fin.mk.injEq] at h
  exact Fin.ext (SYT_boxOf_inj T p.isLt q.isLt
    (lexrank_inj (SYT_boxOf_mem T p p.isLt) (SYT_boxOf_mem T q q.isLt) h))

noncomputable def lexP {lam : YoungDiagram} (T : SYT lam) : Equiv.Perm (Fin lam.cells.card) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (lexP_inj T))

lemma lexP_apply {lam : YoungDiagram} (T : SYT lam) (l : Fin lam.cells.card) :
    (lexP T l).val = lexrank lam (boxOf T.1 l) := rfl

lemma prod_ite_neg_one {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] :
    ∏ x, (if P x then (-1 : ℂ) else 1) = (-1 : ℂ) ^ (Finset.univ.filter P).card := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

lemma epsL_fin {lam : YoungDiagram} (T : SYT lam) :
    epsL T = ∏ p : Fin lam.cells.card × Fin lam.cells.card, epsG T p.1 p.2 := by
  rw [Fintype.prod_prod_type, epsL, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← Fin.prod_univ_eq_prod_range]

lemma epsL_sign {lam : YoungDiagram} (T : SYT lam) :
    epsL T = ((Equiv.Perm.sign (lexP T) : ℤ) : ℂ) := by
  rw [epsL_fin, ← neg_one_pow_inv_eq_sign, ← prod_ite_neg_one]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  unfold epsG
  refine if_congr ?_ rfl rfl
  have h1 := SYT_boxOf_mem T p.1 p.1.isLt
  have h2 := SYT_boxOf_mem T p.2 p.2.isLt
  rw [Fin.lt_def, gt_iff_lt, Fin.lt_def, lexP_apply, lexP_apply, lexrank_lt_iff h2 h1]

lemma epsL_sq {lam : YoungDiagram} (T : SYT lam) : epsL T * epsL T = 1 := by
  rw [epsL_sign, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one,
    Int.cast_one]

lemma epsL_ne_zero {lam : YoungDiagram} (T : SYT lam) : epsL T ≠ 0 := by
  intro h; have := epsL_sq T; rw [h, zero_mul] at this; exact zero_ne_one this

lemma signW_ne_zero {lam : YoungDiagram} (T : SYT lam) : signW T ≠ 0 := by
  unfold signW; exact pow_ne_zero _ (by norm_num)

lemma lexP_mul_piT {lam : YoungDiagram} (T U : SYT lam) :
    lexP T * piT T = lexP U * piT U := by
  ext p
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  rw [lexP_apply, lexP_apply, piT_apply, piT_apply]
  have hm := (refBox_mem_inj lam).1 p p.isLt
  rw [(labelAt_of_mem T hm).2, (labelAt_of_mem U hm).2]

lemma epsL_signW_const {lam : YoungDiagram} (T U : SYT lam) :
    epsL T * signW T = epsL U * signW U := by
  rw [epsL_sign, epsL_sign, signW_eq_sign, signW_eq_sign, ← Int.cast_mul, ← Int.cast_mul,
    ← Units.val_mul, ← Units.val_mul, ← Equiv.Perm.sign_mul, ← Equiv.Perm.sign_mul,
    lexP_mul_piT T U]

/-- The conjugation map `v_T ↦ epsL T • v_{T'}` into any target diagram. -/
noncomputable def Cinto (nu : YoungDiagram) {lam : YoungDiagram} : V lam →ₗ[ℂ] V nu :=
  Finsupp.linearCombination ℂ (fun T : SYT lam => epsL T • conjInto nu T)

lemma Cinto_vT (nu : YoungDiagram) {lam : YoungDiagram} (T : SYT lam) :
    Cinto nu (vT T) = epsL T • conjInto nu T := by
  show Finsupp.linearCombination ℂ _ (Finsupp.single T 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

/-- (c): on a self-conjugate shape, `phi` is a nonzero multiple of `Cinto`. -/
theorem phi_eq_Cinto {lam : YoungDiagram} :
    ∃ K : ℂ, K ≠ 0 ∧ phi lam = K • (Cinto lam : V lam →ₗ[ℂ] V lam) := by
  by_cases hne : Nonempty (SYT lam)
  · obtain ⟨T0⟩ := hne
    refine ⟨Complex.I ^ ((lam.cells.card - diagLen lam) / 2) * (signW T0 * epsL T0), ?_, ?_⟩
    · exact mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero)
        (mul_ne_zero (signW_ne_zero T0) (epsL_ne_zero T0))
    · apply Finsupp.lhom_ext
      intro T b
      rw [LinearMap.smul_apply]
      unfold phi Cinto
      rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, smul_smul,
        smul_smul, smul_smul]
      have hs : signW T = signW T0 * epsL T0 * epsL T := by
        have h1 := epsL_signW_const T T0
        calc signW T = (epsL T * epsL T) * signW T := by rw [epsL_sq, one_mul]
          _ = epsL T * (epsL T0 * signW T0) := by rw [mul_assoc, h1]
          _ = _ := by ring
      rw [hs]; congr 1; ring
  · refine ⟨1, one_ne_zero, ?_⟩
    apply Finsupp.lhom_ext
    intro T; exact absurd ⟨T⟩ hne

/-! ## (b): `Cinto ∘ embed = κ • embed ∘ Cinto` -/

noncomputable def conjG {lam : YoungDiagram} (T : SYT lam) : SYT lam.transpose :=
  (exists_conj T).choose

lemma conjG_spec {lam : YoungDiagram} (T : SYT lam) :
    ∀ k, k < lam.cells.card → boxOf (conjG T).1 k = (boxOf T.1 k).swap :=
  (exists_conj T).choose_spec

lemma conjInto_tr {lam : YoungDiagram} (T : SYT lam) :
    conjInto lam.transpose T = vT (conjG T) := by
  rw [conjInto, dif_pos ⟨transpose_card lam, exists_conj T⟩]
  rfl

lemma edge_tr {mu lam : YoungDiagram} (h : YoungEdge mu lam) :
    YoungEdge mu.transpose lam.transpose := by
  refine ⟨YoungDiagram.transpose_le_iff.2 h.1, ?_⟩
  rw [← h.2]
  apply Finset.card_nbij' Prod.swap Prod.swap
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_sdiff, YoungDiagram.mem_cells,
      YoungDiagram.mem_transpose] at hx ⊢
    exact hx
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_sdiff, YoungDiagram.mem_cells,
      YoungDiagram.mem_transpose, Prod.swap_swap] at hx ⊢
    exact hx
  · intro x _; rfl
  · intro x _; rfl

lemma conjG_extT {mu lam : YoungDiagram} (h : YoungEdge mu lam) (T : SYT mu) :
    conjG (extT h T) = extT (edge_tr h) (conjG T) := by
  have hcard := edge_card h
  apply ext_unique (edge_tr h) (conjG T)
  · intro k hk
    rw [transpose_card] at hk
    rw [conjG_spec _ k (by omega), extT_spec h T k hk, conjG_spec T k hk]
  · exact extT_spec _ _

noncomputable def kapB (mu : YoungDiagram) (c : ℕ × ℕ) : ℂ :=
  ∏ b ∈ mu.cells, if toLex c < toLex b then (-1 : ℂ) else 1

lemma kap_eq {mu : YoungDiagram} (T : SYT mu) (c : ℕ × ℕ) :
    ∏ i ∈ Finset.range mu.cells.card, (if toLex c < toLex (boxOf T.1 i) then (-1 : ℂ) else 1) =
      kapB mu c := by
  unfold kapB
  apply Finset.prod_nbij (fun i => boxOf T.1 i)
  · intro i hi; exact SYT_boxOf_mem T i (Finset.mem_range.1 hi)
  · intro i hi j hj hij
    exact SYT_boxOf_inj T (Finset.mem_range.1 (Finset.mem_coe.1 hi))
      (Finset.mem_range.1 (Finset.mem_coe.1 hj)) hij
  · intro b hb
    obtain ⟨k, hk, rfl⟩ := SYT_exists_of_mem T (Finset.mem_coe.1 hb)
    exact ⟨k, Finset.mem_coe.2 (Finset.mem_range.2 hk), rfl⟩
  · intro i _; rfl

lemma epsL_extT {mu lam : YoungDiagram} (h : YoungEdge mu lam) (T : SYT mu) {c : ℕ × ℕ}
    (hc : lam.cells \ mu.cells = {c}) : epsL (extT h T) = epsL T * kapB mu c := by
  have hn := edge_card h
  have hr : Finset.range lam.cells.card = Finset.range (mu.cells.card + 1) := by rw [hn]
  have hlast : boxOf (extT h T).1 mu.cells.card = c := by
    have hm := last_box_mem h T _ (extT_spec h T)
    rw [hc, Finset.mem_singleton] at hm
    exact hm
  unfold epsL
  rw [hr, Finset.prod_range_succ]
  have h1 : ∏ j ∈ Finset.range (mu.cells.card + 1), epsG (extT h T) mu.cells.card j = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    rw [Finset.mem_range] at hj
    unfold epsG
    rw [if_neg (fun hh => absurd hh.1 (by omega))]
  rw [h1, mul_one, ← kap_eq T c, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [Finset.prod_range_succ]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    unfold epsG
    rw [extT_spec h T i hi, extT_spec h T j hj]
  · unfold epsG
    rw [hlast, extT_spec h T i hi]
    exact if_congr ⟨fun hh => hh.2, fun hh => ⟨hi, hh⟩⟩ rfl rfl

/-- (b) -/
theorem Cinto_embed {mu lam mu' lam' : YoungDiagram} (h : YoungEdge mu lam) {c : ℕ × ℕ}
    (hc : lam.cells \ mu.cells = {c}) (hmu : mu' = mu.transpose) (hlam : lam' = lam.transpose) :
    (Cinto lam' : V lam →ₗ[ℂ] V lam') ∘ₗ embed mu lam =
      kapB mu c • (embed mu' lam' ∘ₗ (Cinto mu' : V mu →ₗ[ℂ] V mu')) := by
  subst hmu hlam
  apply Finsupp.lhom_ext'
  intro T
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, Finsupp.lsingle_apply]
  show Cinto _ (embed mu lam (vT T)) = kapB mu c • embed _ _ (Cinto _ (vT T))
  rw [embed_vT h, Cinto_vT, Cinto_vT, conjInto_tr, conjInto_tr, map_smul, embed_vT (edge_tr h),
    conjG_extT h, epsL_extT h T hc, smul_smul, mul_comm]

end Lib
end GTAlternating.Bases


set_option autoImplicit false

namespace GTAlternating.Bases
namespace Lib

open Classical QAlgorithms.Papers.Independent.Renew46.P26

/-! ## Part 2b: the step map, spanning by all paths, and the E-lemmas (equivalent paths give
proportional vectors). -/

noncomputable def step : (a b : Label) → (V b.shape →ₗ[ℂ] V a.shape)
  | .sc lam _ s, .nsc mu _ => pm lam s ∘ₗ embed mu lam
  | a, b => embed b.shape a.shape

lemma uVec_cons (a b : Label) (rest : List Label) :
    uVec a (b :: rest) = step a b (uVec b rest) := by
  cases a with
  | nsc lam h => cases b <;> rfl
  | sc lam h s =>
    cases b with
    | nsc mu hm =>
      show _ = pm lam s (embed mu lam _)
      rw [pm_apply]; rfl
    | sc mu hm t => rfl

lemma uVec_nil (a : Label) (h : a.size = 2) :
    uVec a [] = vT (Classical.choice (syt_two_nonempty (lam := a.shape) h)) := by
  have hu : uVec a [] = if h : a.size = 2 ∧ Nonempty (SYT a.shape) then
      Finsupp.single (Classical.choice h.2) 1 else 0 := rfl
  rw [hu, dif_pos ⟨h, syt_two_nonempty (lam := a.shape) h⟩]
  rfl

lemma box0 {lam : YoungDiagram} (T : SYT lam) (h : 0 < lam.cells.card) :
    boxOf T.1 0 = (0, 0) := by
  have hl := T.1.2.2 1 (by omega)
  have hmem : boxOf T.1 0 ∈ {b | ∃ i : Fin lam.cells.card, i.val < 1 ∧ T.1.1 i = b} :=
    ⟨⟨0, h⟩, Nat.zero_lt_one, (boxOf_lt _ _ h).symm⟩
  obtain ⟨i, hi, hie⟩ := hl (show ((0 : ℕ), (0 : ℕ)) ≤ boxOf T.1 0 from
    Prod.mk_le_mk.2 ⟨Nat.zero_le _, Nat.zero_le _⟩) hmem
  have : i = ⟨0, h⟩ := Fin.ext (Nat.lt_one_iff.mp hi)
  rw [boxOf_lt _ _ h, ← this]; exact hie

lemma syt_two_subsingleton {lam : YoungDiagram} (h2 : lam.cells.card = 2) :
    Subsingleton (SYT lam) := ⟨fun T U => by
  apply SYT_ext
  intro k hk
  obtain ⟨b, hb0, hcells⟩ := two_cells h2
  rw [h2] at hk
  interval_cases k
  · rw [box0 T (by omega), box0 U (by omega)]
  · have m1 := SYT_boxOf_mem T 1 (by omega)
    have m2 := SYT_boxOf_mem U 1 (by omega)
    replace m1 := (Finset.ext_iff.1 hcells _).1 m1
    replace m2 := (Finset.ext_iff.1 hcells _).1 m2
    have n1 : boxOf T.1 1 ≠ (0, 0) := by
      rw [← box0 T (by omega)]; intro e
      exact absurd (SYT_boxOf_inj T (by omega) (by omega) e) (by norm_num)
    have n2 : boxOf U.1 1 ≠ (0, 0) := by
      rw [← box0 U (by omega)]; intro e
      exact absurd (SYT_boxOf_inj U (by omega) (by omega) e) (by norm_num)
    simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2
    rcases m1 with m1 | m1
    · exact absurd m1 n1
    rcases m2 with m2 | m2
    · exact absurd m2 n2
    rw [m1, m2]⟩

lemma kapB_ne_zero (mu : YoungDiagram) (c : ℕ × ℕ) : kapB mu c ≠ 0 := by
  unfold kapB
  rw [Finset.prod_ne_zero_iff]
  intro b _
  split_ifs <;> norm_num

lemma pm_phi {lam : YoungDiagram} (hsc : lam.transpose = lam) (s : Bool) (z : V lam) :
    pm lam s (phi lam z) = (if s then (1 : ℂ) else -1) • pm lam s z := by
  rw [pm_apply, pm_apply, phi_phi hsc]
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> module

lemma nsc_pair_sc {mu lam : YoungDiagram} (h1 : YoungEdge mu lam)
    (h2 : YoungEdge mu.transpose lam) (hne : mu.transpose ≠ mu) : lam.transpose = lam := by
  have s1 := edge_subset h1
  have s2 := edge_subset h2
  have hc := edge_card h1
  have hct := transpose_card mu
  have hnsub : ¬ mu.transpose.cells ⊆ mu.cells := by
    intro hs
    apply hne
    exact YoungDiagram.ext (Finset.eq_of_subset_of_card_le hs (by rw [hct]))
  have hU : lam.cells = mu.cells ∪ mu.transpose.cells := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.union_subset s1 s2)
    obtain ⟨x, hx, hxn⟩ := Finset.not_subset.1 hnsub
    have : (insert x mu.cells).card ≤ (mu.cells ∪ mu.transpose.cells).card :=
      Finset.card_le_card (Finset.insert_subset (Finset.mem_union_right _ hx)
        Finset.subset_union_left)
    rw [Finset.card_insert_of_notMem hxn] at this
    omega
  have key : ∀ y : ℕ × ℕ, y ∈ lam.cells ↔ y ∈ mu.cells ∨ y.swap ∈ mu.cells := by
    intro y; rw [hU, Finset.mem_union]; simp [YoungDiagram.mem_transpose]
  apply YoungDiagram.ext
  ext y
  have e1 : y ∈ lam.transpose.cells ↔ y.swap ∈ lam.cells := by
    simp [YoungDiagram.mem_transpose]
  rw [e1, key y.swap, key y, Prod.swap_swap, or_comm]

/-- Restriction: every tableau is the extension of a tableau of a child shape. -/
lemma restrict_exists {lam : YoungDiagram} (U : SYT lam) {m : ℕ} (hm : lam.cells.card = m + 1) :
    ∃ (mu : YoungDiagram) (h : YoungEdge mu lam) (T : SYT mu), extT h T = U := by
  let t : Fin m → ℕ × ℕ := fun j => boxOf U.1 j.val
  have hinj : Function.Injective t := by
    intro i j hij; apply Fin.ext
    exact SYT_boxOf_inj U (by have := i.isLt; omega) (by have := j.isLt; omega) hij
  have hlow : ∀ m' : ℕ, m' ≤ m → IsLowerSet {b | ∃ i : Fin m, i.val < m' ∧ t i = b} := by
    intro m' hm' a b hba ha
    obtain ⟨i, hi, rfl⟩ := ha
    have hi' : i.val < lam.cells.card := by have := i.isLt; omega
    have ht : t i = U.1.1 ⟨i.val, hi'⟩ := boxOf_lt _ _ hi'
    rw [ht] at hba
    obtain ⟨j, hj, hjb⟩ := U.1.2.2 m' (by omega) hba ⟨⟨i.val, hi'⟩, hi, rfl⟩
    refine ⟨⟨j.val, by omega⟩, hj, ?_⟩
    show boxOf U.1 j.val = b
    rw [boxOf_lt _ _ j.isLt]; exact hjb
  obtain ⟨mu, hmuc⟩ : ∃ mu : YoungDiagram, mu.cells = Finset.univ.image t :=
    ⟨tableauShape (⟨t, hinj, hlow⟩ : YoungTableau m), rfl⟩
  have hcard : mu.cells.card = m := by
    rw [hmuc, Finset.card_image_of_injective _ hinj]; simp
  have hsub : mu.cells ⊆ lam.cells := by
    intro b hb
    rw [hmuc] at hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
    exact SYT_boxOf_mem U _ (by have := i.isLt; omega)
  have hedge : YoungEdge mu lam := by
    refine ⟨YoungDiagram.cells_subset_iff.mp hsub, ?_⟩
    have := Finset.card_sdiff_add_card_eq_card hsub
    omega
  have hU : boxOf U.1 mu.cells.card ∉ mu.cells := by
    rw [hcard, hmuc]
    intro hmem
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
    have := SYT_boxOf_inj U (k := i.val) (l := m) (by have := i.isLt; omega) (by omega) hi
    have := i.isLt; omega
  obtain ⟨T, hT⟩ := exists_restrict hedge U hU
  exact ⟨mu, hedge, T, ext_unique hedge T _ _ (extT_spec hedge T) (fun k hk => hT k hk)⟩

/-! ## Spanning by all paths -/

def PS (a : Label) : Set (V a.shape) := {x | ∃ q, IsPath a q ∧ uVec a q = x}

lemma step_span (a b : Label) (hD : Dagger a b) (y : V b.shape)
    (hy : y ∈ Submodule.span ℂ (PS b)) : step a b y ∈ Submodule.span ℂ (PS a) := by
  have : (Submodule.span ℂ (PS b)).map (step a b) ≤ Submodule.span ℂ (PS a) := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨x, ⟨q, hq, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨b :: q, ⟨hD, hq⟩, uVec_cons a b q⟩
  exact this (Submodule.mem_map_of_mem hy)

lemma single_eq_smul_vT {lam : YoungDiagram} (U : SYT lam) (c : ℂ) :
    Finsupp.single U c = c • vT U := by
  rw [vT, Finsupp.smul_single, smul_eq_mul, mul_one]

theorem spanAll : ∀ n : ℕ, ∀ a : Label, a.size = n + 2 →
    Submodule.span ℂ (PS a) = a.space := by
  intro n
  induction n with
  | zero =>
    intro a ha
    apply le_antisymm
    · rw [Submodule.span_le]; rintro _ ⟨q, hq, rfl⟩; exact (part1 q a hq).2.1
    cases a with
    | sc lam h s => exact absurd ha (not_sc_two h)
    | nsc lam hl =>
      have h2 : lam.cells.card = 2 := ha
      have : Subsingleton (SYT (Label.nsc lam hl).shape) := syt_two_subsingleton h2
      intro x _
      set T0 := Classical.choice (syt_two_nonempty h2)
      have hx : x = x T0 • vT T0 := by
        ext T; rw [Subsingleton.elim T T0]
        show x T0 = (x T0 • vT T0) T0
        rw [Finsupp.smul_apply, vT, Finsupp.single_eq_same, smul_eq_mul, mul_one]
      rw [hx]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨[], h2, uVec_nil (Label.nsc lam hl) h2⟩)
  | succ n ih =>
    intro a ha
    apply le_antisymm
    · rw [Submodule.span_le]; rintro _ ⟨q, hq, rfl⟩; exact (part1 q a hq).2.1
    cases a with
    | nsc lam hl =>
      have ha' : lam.cells.card = (n + 2) + 1 := ha
      show (⊤ : Submodule ℂ (V lam)) ≤ Submodule.span ℂ (PS (Label.nsc lam hl))
      rintro (x : V lam) -
      induction x using Finsupp.induction_linear with
      | zero => exact Submodule.zero_mem _
      | add f g hf hg => exact Submodule.add_mem _ hf hg
      | single U c =>
        rw [single_eq_smul_vT]
        apply Submodule.smul_mem
        obtain ⟨mu, hedge, T, rfl⟩ := restrict_exists U ha'
        have hsz : mu.cells.card = n + 2 := by have := edge_card hedge; omega
        rw [← embed_vT hedge]
        by_cases hmu : mu.transpose = mu
        · have hsplit : vT T = (1 / 2 : ℂ) • pm mu true (vT T) +
              (1 / 2 : ℂ) • pm mu false (vT T) := by
            simp only [pm_apply, ↓reduceIte, Bool.false_eq_true]; module
          rw [hsplit, map_add, map_smul, map_smul]
          apply Submodule.add_mem <;> apply Submodule.smul_mem
          · exact step_span (Label.nsc lam hl) (Label.sc mu hmu true) ⟨hedge, trivial⟩ _
              (by rw [ih (Label.sc mu hmu true) hsz]; exact pm_mem hmu true _)
          · exact step_span (Label.nsc lam hl) (Label.sc mu hmu false) ⟨hedge, trivial⟩ _
              (by rw [ih (Label.sc mu hmu false) hsz]; exact pm_mem hmu false _)
        · exact step_span (Label.nsc lam hl) (Label.nsc mu hmu) ⟨hedge, trivial⟩ _
            (by rw [ih (Label.nsc mu hmu) hsz]; exact Submodule.mem_top)
    | sc lam hl s =>
      have ha' : lam.cells.card = (n + 2) + 1 := ha
      have hpm : ∀ y : V lam, pm lam s y ∈ Submodule.span ℂ (PS (Label.sc lam hl s)) := by
        intro y
        induction y using Finsupp.induction_linear with
        | zero => rw [map_zero]; exact Submodule.zero_mem _
        | add f g hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
        | single U c =>
          rw [single_eq_smul_vT, map_smul]
          apply Submodule.smul_mem
          obtain ⟨mu, hedge, T, rfl⟩ := restrict_exists U ha'
          have hsz : mu.cells.card = n + 2 := by have := edge_card hedge; omega
          rw [← embed_vT hedge]
          by_cases hmu : mu.transpose = mu
          · have e := LinearMap.congr_fun (embed_phi hmu hl hedge) (vT T)
            simp only [LinearMap.comp_apply] at e
            have he : pm lam s (embed mu lam (vT T)) = embed mu lam (pm mu s (vT T)) := by
              rw [pm_apply, pm_apply, map_add, map_smul, e]
            rw [he]
            exact step_span (Label.sc lam hl s) (Label.sc mu hmu s) ⟨hedge, rfl⟩ _
              (by rw [ih (Label.sc mu hmu s) hsz]; exact pm_mem hmu s _)
          · exact step_span (Label.sc lam hl s) (Label.nsc mu hmu) ⟨hedge, trivial⟩ _
              (by rw [ih (Label.nsc mu hmu) hsz]; exact Submodule.mem_top)
      show Vpm lam s ≤ Submodule.span ℂ (PS (Label.sc lam hl s))
      intro x hx
      have hx' : phi lam x = (if s then (1 : ℂ) else -1) • x := mem_Vpm.1 hx
      have hxe : x = (1 / 2 : ℂ) • pm lam s x := by
        rw [pm_apply, hx', smul_smul]
        cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> module
      rw [hxe]
      exact Submodule.smul_mem _ _ (hpm x)

/-! ## E-lemmas -/

lemma smul_fix {M : Type*} [AddCommGroup M] [Module ℂ M] (κ D : ℂ) (hD : D ≠ 0) (x : M) :
    κ • x = (κ * D⁻¹) • D • x := by
  rw [smul_smul, mul_assoc, inv_mul_cancel₀ hD, mul_one]

lemma smul_fix2 {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (f : M →ₗ[ℂ] N) (κ a b : ℂ) (h : a * b ≠ 0) (y : M) :
    f (κ • y) = (κ * (a * b)⁻¹) • a • f (b • y) := by
  rw [map_smul, map_smul, smul_smul, smul_smul, mul_assoc κ, mul_assoc κ, mul_assoc (a * b)⁻¹ a b,
    inv_mul_cancel₀ h, mul_one]

lemma smul_fix3 {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (f : M →ₗ[ℂ] N) (κ D : ℂ) (hD : D ≠ 0) (y : M) :
    f (κ • y) = (κ * D⁻¹) • D • f y := by
  rw [map_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hD, mul_one]

lemma nil_tr {lam : YoungDiagram} (T0 : SYT lam) (U : SYT lam.transpose)
    (h2 : lam.transpose.cells.card = 2) :
    vT U = epsL T0 • Cinto lam.transpose (vT T0) := by
  have := syt_two_subsingleton h2
  rw [Cinto_vT, conjInto_tr, smul_smul, epsL_sq, one_smul, Subsingleton.elim U (conjG T0)]

theorem E12 (p : List Label) :
    (∀ (a : Label) (q : List Label), IsPath a p → IsPath a q → List.Forall₂ Label.Equiv p q →
      ∃ κ : ℂ, uVec a q = κ • uVec a p) ∧
    (∀ (a a' : Label) (q : List Label), a.isSc = false → a'.isSc = false →
      a'.shape = a.shape.transpose → IsPath a p → IsPath a' q → List.Forall₂ Label.Equiv p q →
      ∃ κ : ℂ, uVec a' q = κ • Cinto a'.shape (uVec a p)) := by
  induction p with
  | nil =>
    refine ⟨fun a q _ _ hF => ?_, fun a a' q ha ha' hsh hp hq hF => ?_⟩
    · cases hF; exact ⟨1, (one_smul _ _).symm⟩
    · cases hF
      cases a with
      | sc lam h s => simp [Label.isSc] at ha
      | nsc lam hl =>
        cases a' with
        | sc lam' h' s' => simp [Label.isSc] at ha'
        | nsc lam' hl' =>
          simp only [Label.shape] at hsh
          subst hsh
          have h2 : lam.cells.card = 2 := hp
          have h2' : lam.transpose.cells.card = 2 := hq
          refine ⟨epsL (Classical.choice (syt_two_nonempty h2)), ?_⟩
          rw [uVec_nil (Label.nsc lam hl) h2, uVec_nil (Label.nsc lam.transpose hl') h2']
          exact nil_tr _ _ h2'
  | cons b r ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun a q hp hq hF => ?_, fun a a' q ha ha' hsh hp hq hF => ?_⟩
    · cases hF with
      | cons hbb' hF' =>
        rename_i b' r'
        obtain ⟨hD, hp'⟩ := hp
        obtain ⟨hD', hq'⟩ := hq
        rcases hbb' with rfl | ⟨hb1, hb2, hsh⟩
        · obtain ⟨κ, hκ⟩ := ih1 b r' hp' hq' hF'
          exact ⟨κ, by rw [uVec_cons, uVec_cons, hκ, map_smul]⟩
        · obtain ⟨κ, hκ⟩ := ih2 b b' r' hb1 hb2 hsh hp' hq' hF'
          cases b with
          | sc mu hmu t => simp [Label.isSc] at hb1
          | nsc mu hmu =>
          cases b' with
          | sc mu' hmu' t' => simp [Label.isSc] at hb2
          | nsc mu' hmu' =>
          simp only [Label.shape] at hsh
          subst hsh
          cases a with
          | nsc lam hl =>
            have hedge : YoungEdge mu lam := hD.1
            have hedge' : YoungEdge mu.transpose lam := hD'.1
            exact absurd (nsc_pair_sc hedge hedge' hmu) hl
          | sc lam hl s =>
            have hedge : YoungEdge mu lam := hD.1
            set y : V mu := uVec (Label.nsc mu hmu) r with hy_def
            obtain ⟨c, hc⟩ := edge_box hedge
            have hCE : Cinto lam (embed mu lam y) =
                kapB mu c • embed mu.transpose lam (Cinto mu.transpose y) :=
              LinearMap.congr_fun
                (Cinto_embed (mu' := mu.transpose) (lam' := lam) hedge hc rfl hl.symm) y
            obtain ⟨K, hK, hphi⟩ := phi_eq_Cinto (lam := lam)
            have hne : K * kapB mu c ≠ 0 := mul_ne_zero hK (kapB_ne_zero _ _)
            have hφ : phi lam (embed mu lam y) =
                (K * kapB mu c) • embed mu.transpose lam (Cinto mu.transpose y) := by
              rw [hphi, LinearMap.smul_apply, hCE, smul_smul]
            have hφ' : embed mu.transpose lam (Cinto mu.transpose y) =
                (K * kapB mu c)⁻¹ • phi lam (embed mu lam y) := by
              rw [hφ, smul_smul, inv_mul_cancel₀ hne, one_smul]
            refine ⟨κ * (K * kapB mu c)⁻¹ * (if s then 1 else -1), ?_⟩
            rw [uVec_cons, uVec_cons, hκ]
            show pm lam s (embed mu.transpose lam (κ • Cinto mu.transpose y)) =
              _ • pm lam s (embed mu lam y)
            simp only [map_smul, hφ', pm_phi hl, smul_smul]
            exact rfl
    · cases hF with
      | cons hbb' hF' =>
        rename_i b' r'
        obtain ⟨hD, hp'⟩ := hp
        obtain ⟨hD', hq'⟩ := hq
        cases a with
        | sc lam h s => simp [Label.isSc] at ha
        | nsc lam hl =>
        cases a' with
        | sc lam' h' s' => simp [Label.isSc] at ha'
        | nsc lam' hl' =>
        simp only [Label.shape] at hsh
        subst hsh
        rcases hbb' with rfl | ⟨hb1, hb2, hsh⟩
        · obtain ⟨κ, hκ⟩ := ih1 b r' hp' hq' hF'
          have hedge : YoungEdge b.shape lam := hD.1
          have hedge' : YoungEdge b.shape lam.transpose := hD'.1
          have hbsc : b.shape.transpose = b.shape := by
            by_contra hne
            have e2 : YoungEdge b.shape.transpose lam := by
              have := edge_tr hedge'; rwa [YoungDiagram.transpose_transpose] at this
            exact hl (nsc_pair_sc hedge e2 hne)
          cases b with
          | nsc mu hmu => exact absurd hbsc hmu
          | sc mu hmu t =>
            have hedge0 : YoungEdge mu lam := hedge
            set y : V mu := uVec (Label.sc mu hmu t) r with hy_def
            have hy : phi mu y = (if t then (1 : ℂ) else -1) • y :=
              mem_Vpm.1 (part1 r _ hp').2.1
            obtain ⟨c, hc⟩ := edge_box hedge0
            have hCE : Cinto lam.transpose (embed mu lam y) =
                kapB mu c • embed mu lam.transpose (Cinto mu y) :=
              LinearMap.congr_fun
                (Cinto_embed (mu' := mu) (lam' := lam.transpose) hedge0 hc hmu.symm rfl) y
            obtain ⟨K, hK, hphi⟩ := phi_eq_Cinto (lam := mu)
            have hC : Cinto mu y = (K⁻¹ * (if t then (1 : ℂ) else -1)) • y := by
              have e := LinearMap.congr_fun hphi y
              rw [LinearMap.smul_apply, hy] at e
              rw [← smul_smul, e, smul_smul, inv_mul_cancel₀ hK, one_smul]
            have hct : (if t then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
            have hne : kapB mu c * (K⁻¹ * (if t then (1 : ℂ) else -1)) ≠ 0 :=
              mul_ne_zero (kapB_ne_zero _ _) (mul_ne_zero (inv_ne_zero hK) hct)
            refine ⟨κ * (kapB mu c * (K⁻¹ * (if t then (1 : ℂ) else -1)))⁻¹, ?_⟩
            rw [uVec_cons, uVec_cons, hκ]
            show embed mu lam.transpose (κ • y) = _ • Cinto lam.transpose (embed mu lam y)
            rw [hCE, hC]
            exact smul_fix2 (embed mu lam.transpose) κ _ _ hne y
        · obtain ⟨κ, hκ⟩ := ih2 b b' r' hb1 hb2 hsh hp' hq' hF'
          cases b with
          | sc mu hmu t => simp [Label.isSc] at hb1
          | nsc mu hmu =>
          cases b' with
          | sc mu' hmu' t' => simp [Label.isSc] at hb2
          | nsc mu' hmu' =>
          simp only [Label.shape] at hsh
          subst hsh
          have hedge : YoungEdge mu lam := hD.1
          obtain ⟨c, hc⟩ := edge_box hedge
          have hCE : Cinto lam.transpose (embed mu lam (uVec (Label.nsc mu hmu) r : V mu)) =
              kapB mu c • embed mu.transpose lam.transpose
                (Cinto mu.transpose (uVec (Label.nsc mu hmu) r : V mu)) :=
            LinearMap.congr_fun (Cinto_embed (mu' := mu.transpose)
              (lam' := lam.transpose) hedge hc rfl rfl) _
          refine ⟨κ * (kapB mu c)⁻¹, ?_⟩
          rw [uVec_cons, uVec_cons, hκ]
          show embed mu.transpose lam.transpose
              (κ • Cinto mu.transpose (uVec (Label.nsc mu hmu) r)) =
            _ • Cinto lam.transpose (embed mu lam (uVec (Label.nsc mu hmu) r))
          rw [hCE]
          exact smul_fix3 (embed mu.transpose lam.transpose) κ (kapB mu c) (kapB_ne_zero _ _) _

end Lib
end GTAlternating.Bases


set_option autoImplicit false

namespace GTAlternating.Bases
namespace Lib

open Classical QAlgorithms.Papers.Independent.Renew46.P26

/-! ## Part 2c: projections onto children and the generic independence lemma. -/

/-- Projection `V lam → V mu` reading off the coefficients of tableaux extended from `mu`. -/
noncomputable def Q (mu lam : YoungDiagram) : V lam →ₗ[ℂ] V mu :=
  if h : YoungEdge mu lam then Finsupp.lcomapDomain (extT h) (extT_injective h) else 0

lemma Q_apply {mu lam : YoungDiagram} (h : YoungEdge mu lam) (x : V lam) (T : SYT mu) :
    Q mu lam x T = x (extT h T) := by
  rw [Q, dif_pos h]
  first
  | rfl
  | simp [Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply]

lemma embed_apply_ext {mu lam : YoungDiagram} (h : YoungEdge mu lam) (x : V mu) (T : SYT mu) :
    embed mu lam x (extT h T) = x T := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, hf, hg]
  | single U c =>
    rw [single_eq_smul_vT, map_smul, embed_vT h, Finsupp.smul_apply, Finsupp.smul_apply, vT, vT,
      Finsupp.single_apply, Finsupp.single_apply, (extT_injective h).eq_iff]

lemma Q_embed_self {mu lam : YoungDiagram} (h : YoungEdge mu lam) (x : V mu) :
    Q mu lam (embed mu lam x) = x := by
  ext T; rw [Q_apply h, embed_apply_ext h]

lemma cells_eq_image {mu : YoungDiagram} (T : SYT mu) :
    mu.cells = (Finset.range mu.cells.card).image (boxOf T.1) := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro b hb
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hb
    exact SYT_boxOf_mem T k (Finset.mem_range.1 hk)
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro k hk l hl e
    exact SYT_boxOf_inj T (by simpa using hk) (by simpa using hl) e

lemma extT_cells {mu lam : YoungDiagram} (h : YoungEdge mu lam) (T : SYT mu) :
    mu.cells = (Finset.range mu.cells.card).image (boxOf (extT h T).1) := by
  conv_lhs => rw [cells_eq_image T]
  apply Finset.image_congr
  intro k hk
  exact (extT_spec h T k (by simpa using hk)).symm

lemma extT_ne {mu nu lam : YoungDiagram} (h : YoungEdge mu lam) (h' : YoungEdge nu lam)
    (hne : mu ≠ nu) (T : SYT mu) (T' : SYT nu) : extT h T ≠ extT h' T' := by
  intro e
  apply hne
  have c1 := edge_card h
  have c2 := edge_card h'
  have hc : mu.cells.card = nu.cells.card := by omega
  apply YoungDiagram.ext
  rw [extT_cells h T, extT_cells h' T', e, hc]

lemma Q_embed_other {mu nu lam : YoungDiagram} (h : YoungEdge mu lam) (hne : mu ≠ nu)
    (x : V mu) : Q nu lam (embed mu lam x) = 0 := by
  by_cases h' : YoungEdge nu lam
  · ext T'
    rw [Q_apply h', Finsupp.zero_apply]
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [map_add, Finsupp.add_apply, hf, hg, add_zero]
    | single U c =>
      rw [single_eq_smul_vT, map_smul, embed_vT h, Finsupp.smul_apply, vT, Finsupp.single_apply,
        if_neg (extT_ne h h' hne U T'), smul_zero]
  · rw [Q, dif_neg h', LinearMap.zero_apply]

lemma pm_kill {mu : YoungDiagram} (s : Bool) (x : V mu) (hx : x ∈ Vpm mu (!s)) :
    pm mu s x = 0 := by
  rw [pm_apply, mem_Vpm.1 hx]
  cases s <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> module

lemma pm_fix {mu : YoungDiagram} (s : Bool) (x : V mu) (hx : x ∈ Vpm mu s) :
    (1 / 2 : ℂ) • pm mu s x = x := by
  rw [pm_apply, mem_Vpm.1 hx]
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> module

/-- Generic independence: a family is independent if, for each fiber of `g`, some linear map kills
every vector outside the fiber and is independent on the fiber. -/
lemma linInd_of_proj {ι J M : Type*} [AddCommGroup M] [Module ℂ M] (f : ι → M) (g : ι → J)
    (N : J → Type*) [∀ j, AddCommGroup (N j)] [∀ j, Module ℂ (N j)] (P : ∀ j, M →ₗ[ℂ] N j)
    (hzero : ∀ i j, g i ≠ j → P j (f i) = 0)
    (hind : ∀ j, LinearIndependent ℂ (fun i : {i // g i = j} => P j (f i.1))) :
    LinearIndependent ℂ f := by
  rw [linearIndependent_iff']
  intro s c hs i0 hi0
  have e : ∑ x ∈ s.subtype (fun i => g i = g i0), c x.1 • P (g i0) (f x.1) =
      ∑ i ∈ s, c i • P (g i0) (f i) := by
    rw [Finset.sum_subtype_eq_sum_filter (f := fun i => c i • P (g i0) (f i))]
    apply Finset.sum_filter_of_ne
    intro i _ hne
    by_contra hgi
    exact hne (by rw [hzero i _ hgi, smul_zero])
  have hs' : ∑ x ∈ s.subtype (fun i => g i = g i0), c x.1 • P (g i0) (f x.1) = 0 := by
    rw [e]
    simp_rw [← map_smul]
    rw [← map_sum, hs, map_zero]
  exact linearIndependent_iff'.1 (hind (g i0)) (s.subtype (fun i => g i = g i0))
    (fun x => c x.1) hs' ⟨i0, rfl⟩ (by simpa using hi0)

end Lib
end GTAlternating.Bases


set_option autoImplicit false

namespace GTAlternating.Bases
namespace Lib

open Classical QAlgorithms.Papers.Independent.Renew46.P26

/-! ## Part 2d: label transposition, `∼` is an equivalence, path lengths, base of independence. -/

/-- Transpose a label: `nsc λ ↦ nsc λᵗ`, self-conjugate labels fixed. -/
def trL : Label → Label
  | .nsc lam h => .nsc lam.transpose (by rw [YoungDiagram.transpose_transpose]; exact Ne.symm h)
  | .sc lam h s => .sc lam h s

lemma trL_shape (b : Label) : (trL b).shape = b.shape.transpose := by
  cases b with
  | nsc lam h => rfl
  | sc lam h s => exact h.symm

lemma trL_size (b : Label) : (trL b).size = b.size := by
  show (trL b).shape.cells.card = b.shape.cells.card
  rw [trL_shape, transpose_card]

lemma nsc_eq {l l' : YoungDiagram} (h : l.transpose ≠ l) (h' : l'.transpose ≠ l') (e : l = l') :
    Label.nsc l h = Label.nsc l' h' := by
  subst e; rfl

lemma equiv_trL (b : Label) : Label.Equiv b (trL b) := by
  cases b with
  | nsc lam h => exact Or.inr ⟨rfl, rfl, rfl⟩
  | sc lam h s => exact Or.inl rfl

lemma equiv_symm {a b : Label} (h : Label.Equiv a b) : Label.Equiv b a := by
  rcases h with rfl | ⟨ha, hb, hs⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hb, ha, by rw [hs, YoungDiagram.transpose_transpose]⟩

lemma equiv_trans {a b c : Label} (h1 : Label.Equiv a b) (h2 : Label.Equiv b c) :
    Label.Equiv a c := by
  rcases h1 with rfl | ⟨ha, hb, hs⟩
  · exact h2
  rcases h2 with rfl | ⟨hb', hc, hs'⟩
  · exact Or.inr ⟨ha, hb, hs⟩
  · left
    cases a with
    | sc l hl t => simp [Label.isSc] at ha
    | nsc l hl =>
      cases c with
      | sc l' hl' t => simp [Label.isSc] at hc
      | nsc l' hl' =>
        apply nsc_eq
        have e := hs'
        rw [hs] at e
        simp only [Label.shape, YoungDiagram.transpose_transpose] at e
        exact e.symm

lemma forall2_trans : ∀ {p q r : List Label}, List.Forall₂ Label.Equiv p q →
    List.Forall₂ Label.Equiv q r → List.Forall₂ Label.Equiv p r
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 t1, .cons h2 t2 => .cons (equiv_trans h1 h2) (forall2_trans t1 t2)

lemma forall2_symm : ∀ {p q : List Label}, List.Forall₂ Label.Equiv p q →
    List.Forall₂ Label.Equiv q p
  | _, _, .nil => .nil
  | _, _, .cons h1 t1 => .cons (equiv_symm h1) (forall2_symm t1)

lemma forall2_refl : ∀ (p : List Label), List.Forall₂ Label.Equiv p p
  | [] => .nil
  | b :: r => .cons (Or.inl rfl) (forall2_refl r)

lemma forall2_trL : ∀ (r : List Label), List.Forall₂ Label.Equiv r (r.map trL)
  | [] => .nil
  | b :: r => .cons (equiv_trL b) (forall2_trL r)

lemma dagger_trL {a b : Label} (h : Dagger a b) : Dagger (trL a) (trL b) := by
  refine ⟨?_, ?_⟩
  · rw [trL_shape, trL_shape]; exact edge_tr h.1
  · cases a <;> cases b <;> first | trivial | exact h.2

lemma isPath_trL : ∀ (r : List Label) (a : Label), IsPath a r → IsPath (trL a) (r.map trL)
  | [], a, h => by
    show (trL a).size = 2
    rw [trL_size]; exact h
  | b :: r, a, h => ⟨dagger_trL h.1, isPath_trL r b h.2⟩

lemma path_length : ∀ (p : List Label) (a : Label), IsPath a p → a.size = p.length + 2
  | [], a, h => h
  | b :: r, a, h => by
    have e1 := edge_card h.1.1
    have e2 := path_length r b h.2
    simp only [Label.size, List.length_cons] at *
    omega

/-- A set of paths at `a`, pairwise non-equivalent. -/
def PNE (a : Label) (R : Set (List Label)) : Prop :=
  (∀ p ∈ R, IsPath a p) ∧ ∀ p ∈ R, ∀ q ∈ R, List.Forall₂ Label.Equiv p q → p = q

lemma ind_base (a : Label) (ha : a.size = 2) (R : Set (List Label)) (hR : PNE a R) :
    LinearIndependent ℂ (fun p : R => uVec a p.1) := by
  have hsub : ∀ p ∈ R, p = [] := by
    intro p hp
    have e := path_length p a (hR.1 p hp)
    rw [ha] at e
    exact List.eq_nil_of_length_eq_zero (by omega)
  by_cases hne : [] ∈ R
  · haveI : Unique R := ⟨⟨⟨[], hne⟩⟩, fun p => Subtype.ext (hsub p.1 p.2)⟩
    rw [linearIndependent_unique_iff]
    have hd : ((default : R) : List Label) = [] := hsub _ (default : R).2
    rw [hd]
    exact (part1 [] a ha).1
  · have : IsEmpty R := ⟨fun p => hne (by have h := p.2; rwa [hsub p.1 p.2] at h)⟩
    exact linearIndependent_empty_type

end Lib
end GTAlternating.Bases


set_option autoImplicit false

namespace GTAlternating.Bases
namespace Lib

open Classical QAlgorithms.Papers.Independent.Renew46.P26

/-! ## Part 2e: linear independence of the `u`-vectors of pairwise non-equivalent paths. -/

lemma fiber_ind {ι : Type} (b : Label)
    (hIH : ∀ R : Set (List Label), PNE b R → LinearIndependent ℂ (fun p : R => uVec b p.1))
    (f : ι → V b.shape) (t : ι → List Label)
    (hf : ∀ i, ∃ c : ℂ, c ≠ 0 ∧ f i = c • uVec b (t i))
    (hpath : ∀ i, IsPath b (t i))
    (hinj : ∀ i i', List.Forall₂ Label.Equiv (t i) (t i') → i = i') :
    LinearIndependent ℂ f := by
  choose c hc hfc using hf
  have hPNE : PNE b (Set.range t) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨i, rfl⟩; exact hpath i
    · rintro _ ⟨i, rfl⟩ _ ⟨i', rfl⟩ hF
      rw [hinj i i' hF]
  have h1 := hIH _ hPNE
  have hinjt : Function.Injective (Set.rangeFactorization t) := by
    intro i i' e
    have e' : t i = t i' := congrArg Subtype.val e
    exact hinj i i' (by rw [e']; exact forall2_refl _)
  have h2 := h1.comp _ hinjt
  have h3 := h2.units_smul (fun i => Units.mk0 (c i) (hc i))
  convert h3 using 1
  funext i
  rw [hfc i]
  rfl

lemma uVec_cons_nsc (lam : YoungDiagram) (hl : lam.transpose ≠ lam) (b : Label) (r : List Label) :
    uVec (Label.nsc lam hl) (b :: r) = embed b.shape lam (uVec b r) := by
  rw [uVec_cons]; cases b <;> rfl

lemma uVec_cons_sc_sc (lam mu : YoungDiagram) (hl : lam.transpose = lam) (hm : mu.transpose = mu)
    (s t : Bool) (r : List Label) :
    uVec (Label.sc lam hl s) (Label.sc mu hm t :: r) = embed mu lam (uVec (Label.sc mu hm t) r) := by
  rw [uVec_cons]; rfl

lemma uVec_cons_sc_nsc (lam mu : YoungDiagram) (hl : lam.transpose = lam) (hm : mu.transpose ≠ mu)
    (s : Bool) (r : List Label) :
    uVec (Label.sc lam hl s) (Label.nsc mu hm :: r) =
      pm lam s (embed mu lam (uVec (Label.nsc mu hm) r)) := by
  rw [uVec_cons]; rfl

lemma edge_tr' {mu lam : YoungDiagram} (hl : lam.transpose = lam) (h : YoungEdge mu.transpose lam) :
    YoungEdge mu lam := by
  have := edge_tr h
  rwa [YoungDiagram.transpose_transpose, hl] at this

lemma pm_embed_nsc {mu lam : YoungDiagram} (hl : lam.transpose = lam) (hedge : YoungEdge mu lam)
    (s : Bool) (mu' : YoungDiagram) (hmu' : mu' = mu.transpose) (y : V mu) :
    ∃ d : ℂ, d ≠ 0 ∧
      pm lam s (embed mu lam y) = embed mu lam y + d • embed mu' lam (Cinto mu' y) := by
  obtain ⟨c, hc⟩ := edge_box hedge
  have hCE : Cinto lam (embed mu lam y) = kapB mu c • embed mu' lam (Cinto mu' y) :=
    LinearMap.congr_fun (Cinto_embed (mu' := mu') (lam' := lam) hedge hc hmu' hl.symm) y
  obtain ⟨K, hK, hphi⟩ := phi_eq_Cinto (lam := lam)
  refine ⟨(if s then (1 : ℂ) else -1) * (K * kapB mu c),
    mul_ne_zero ?_ (mul_ne_zero hK (kapB_ne_zero _ _)), ?_⟩
  · cases s <;> norm_num
  · rw [pm_apply, hphi, LinearMap.smul_apply, hCE, smul_smul, smul_smul, mul_assoc]

/-! ### Parent not self-conjugate -/

lemma half_pm_Q {mu lam : YoungDiagram} (hD : YoungEdge mu lam) (s : Bool) (y : V mu)
    (hy : y ∈ Vpm mu s) : ((1 / 2 : ℂ) • pm mu s) (Q mu lam (embed mu lam y)) = y := by
  rw [Q_embed_self hD, LinearMap.smul_apply]; exact pm_fix s y hy

lemma half_pm_kill {mu lam : YoungDiagram} (hD : YoungEdge mu lam) (t : Bool) (y : V mu)
    (hy : y ∈ Vpm mu (!t)) : ((1 / 2 : ℂ) • pm mu t) (Q mu lam (embed mu lam y)) = 0 := by
  rw [Q_embed_self hD, LinearMap.smul_apply, pm_kill t y hy, smul_zero]

lemma Q_pm_other {mu nu lam : YoungDiagram} (hl : lam.transpose = lam) (hD : YoungEdge mu lam)
    (s : Bool) (h1 : mu ≠ nu) (h2 : mu.transpose ≠ nu) (y : V mu) :
    Q nu lam (pm lam s (embed mu lam y)) = 0 := by
  obtain ⟨d, -, hd⟩ := pm_embed_nsc hl hD s mu.transpose rfl y
  have hD' : YoungEdge mu.transpose lam := by have := edge_tr hD; rwa [hl] at this
  rw [hd, map_add, map_smul, Q_embed_other hD h1, Q_embed_other hD' h2, smul_zero, add_zero]

lemma Q_pm_self {nu lam : YoungDiagram} (hl : lam.transpose = lam) (hE : YoungEdge nu lam)
    (hsc : nu.transpose ≠ nu) (s : Bool) (y : V nu) : Q nu lam (pm lam s (embed nu lam y)) = y := by
  obtain ⟨d, -, hd⟩ := pm_embed_nsc hl hE s nu.transpose rfl y
  have hE' : YoungEdge nu.transpose lam := by have := edge_tr hE; rwa [hl] at this
  rw [hd, map_add, map_smul, Q_embed_self hE, Q_embed_other hE' hsc, smul_zero, add_zero]

lemma Q_pm_tr {nu lam : YoungDiagram} (hl : lam.transpose = lam) (hE : YoungEdge nu lam)
    (hE' : YoungEdge nu.transpose lam) (hsc : nu.transpose ≠ nu) (s : Bool) (y : V nu.transpose) :
    ∃ d : ℂ, d ≠ 0 ∧ Q nu lam (pm lam s (embed nu.transpose lam y)) = d • Cinto nu y := by
  obtain ⟨d, hd0, hd⟩ := pm_embed_nsc hl hE' s nu (by rw [YoungDiagram.transpose_transpose]) y
  refine ⟨d, hd0, ?_⟩
  rw [hd, map_add, map_smul, Q_embed_other hE' hsc, Q_embed_self hE, zero_add]

lemma smul_inv_aux {M : Type*} [AddCommGroup M] [Module ℂ M] (d κ : ℂ) (hκ : κ ≠ 0) (u w : M)
    (h : u = κ • w) : d • w = (d * κ⁻¹) • u := by
  rw [h, smul_smul, mul_assoc, inv_mul_cancel₀ hκ, mul_one]

noncomputable def Pn (lam : YoungDiagram) : (j : Label) → (V lam →ₗ[ℂ] V j.shape)
  | .nsc mu _ => Q mu lam
  | .sc mu _ s => ((1 / 2 : ℂ) • pm mu s) ∘ₗ Q mu lam

lemma Pn_zero (lam : YoungDiagram) (j : Label) (x : V lam) (h : Q j.shape lam x = 0) :
    Pn lam j x = 0 := by
  cases j with
  | nsc mu _ => exact h
  | sc mu _ s =>
    show ((1 / 2 : ℂ) • pm mu s) (Q mu lam x) = 0
    rw [show Q mu lam x = 0 from h, map_zero]

lemma Pn_self (lam : YoungDiagram) (b : Label) (r : List Label) (hD : YoungEdge b.shape lam)
    (hp : IsPath b r) : Pn lam b (embed b.shape lam (uVec b r)) = uVec b r := by
  cases b with
  | nsc mu _ => exact Q_embed_self hD _
  | sc mu hm s =>
    change YoungEdge mu lam at hD
    exact half_pm_Q hD s _ (part1 r _ hp).2.1

lemma headD_cons' {l : List Label} {d b : Label} (hne : l ≠ []) (h : l.headD d = b) :
    l = b :: l.tail := by
  cases l with
  | nil => exact absurd rfl hne
  | cons x xs => simp only [List.headD_cons] at h; subst h; rfl

theorem ind_nsc (lam : YoungDiagram) (hl : lam.transpose ≠ lam) (R : Set (List Label))
    (hR : PNE (Label.nsc lam hl) R) (hne : ∀ p ∈ R, p ≠ [])
    (hIH : ∀ b, Dagger (Label.nsc lam hl) b → ∀ R : Set (List Label), PNE b R →
      LinearIndependent ℂ (fun p : R => uVec b p.1)) :
    LinearIndependent ℂ (fun p : R => uVec (Label.nsc lam hl) p.1) := by
  have hcons : ∀ p ∈ R, ∃ b r, p = b :: r := by
    intro p hp
    cases p with
    | nil => exact absurd rfl (hne _ hp)
    | cons b r => exact ⟨b, r, rfl⟩
  apply linInd_of_proj (fun p : R => uVec (Label.nsc lam hl) p.1)
    (fun p : R => p.1.headD (Label.nsc lam hl)) (fun j : Label => V j.shape) (fun j => Pn lam j)
  · rintro ⟨p, hp⟩ j hj
    obtain ⟨b, r, rfl⟩ := hcons p hp
    simp only [List.headD_cons] at hj
    have hpath := hR.1 _ hp
    have hD : YoungEdge b.shape lam := hpath.1.1
    show Pn lam j (uVec (Label.nsc lam hl) (b :: r)) = 0
    rw [uVec_cons_nsc]
    by_cases hs : b.shape = j.shape
    · cases b with
      | nsc mu hm =>
        cases j with
        | nsc nu hn => exact absurd (nsc_eq hm hn hs) hj
        | sc nu hn t =>
          change mu = nu at hs
          exact absurd (by rw [hs]; exact hn) hm
      | sc mu hm t =>
        cases j with
        | nsc nu hn =>
          change mu = nu at hs
          exact absurd (by rw [← hs]; exact hm) hn
        | sc nu hn t' =>
          change mu = nu at hs
          subst hs
          change YoungEdge mu lam at hD
          have htt : t = !t' := by
            cases t <;> cases t' <;> first | rfl | exact absurd rfl hj
          subst htt
          exact half_pm_kill hD t' _ (part1 r _ hpath.2).2.1
    · exact Pn_zero lam j _ (Q_embed_other hD hs _)
  · intro j
    by_cases hD : Dagger (Label.nsc lam hl) j
    · apply fiber_ind j (hIH j hD) _ (fun i => i.1.1.tail)
      · rintro ⟨⟨p, hp⟩, hg⟩
        obtain ⟨b, r, rfl⟩ := hcons p hp
        simp only [List.headD_cons] at hg
        subst hg
        refine ⟨1, one_ne_zero, ?_⟩
        rw [one_smul]
        show Pn lam b (uVec (Label.nsc lam hl) (b :: r)) = uVec b r
        rw [uVec_cons_nsc]
        exact Pn_self lam b r hD.1 (hR.1 _ hp).2
      · rintro ⟨⟨p, hp⟩, hg⟩
        have e := headD_cons' (hne p hp) hg
        show IsPath j p.tail
        rw [e] at hp
        exact (hR.1 _ hp).2
      · rintro ⟨⟨p, hp⟩, hg⟩ ⟨⟨p', hp'⟩, hg'⟩ hF
        have e := headD_cons' (hne p hp) hg
        have e' := headD_cons' (hne p' hp') hg'
        have : p = p' := hR.2 p hp p' hp' (by
          rw [e, e']; exact List.Forall₂.cons (Or.inl rfl) hF)
        subst this; rfl
    · have : IsEmpty {i : R // i.1.headD (Label.nsc lam hl) = j} :=
        ⟨fun ⟨⟨p, hp⟩, hg⟩ => hD (by
          have e := headD_cons' (hne p hp) hg
          rw [e] at hp
          exact (hR.1 _ hp).1)⟩
      exact linearIndependent_empty_type

/-! ### Parent self-conjugate -/

/-- A representative of `{μ, μᵗ}`. -/
noncomputable def rep (mu : YoungDiagram) : YoungDiagram :=
  @Classical.epsilon _ ⟨mu⟩ (fun x => x = mu ∨ x = mu.transpose)

lemma rep_spec (mu : YoungDiagram) : rep mu = mu ∨ rep mu = mu.transpose :=
  Classical.epsilon_spec (p := fun x => x = mu ∨ x = mu.transpose) ⟨mu, Or.inl rfl⟩

lemma rep_tr (mu : YoungDiagram) : rep mu.transpose = rep mu := by
  have : (fun x => x = mu.transpose ∨ x = mu.transpose.transpose) =
      (fun x => x = mu ∨ x = mu.transpose) := by
    funext x; rw [YoungDiagram.transpose_transpose]; exact propext or_comm
  unfold rep; rw [this]

lemma rep_eq {mu nu : YoungDiagram} (h : rep mu = nu) : mu = nu ∨ mu.transpose = nu := by
  rcases rep_spec mu with e | e
  · left; rw [← h, e]
  · right; rw [← h, e]

lemma rep_sc {mu : YoungDiagram} (h : mu.transpose = mu) : rep mu = mu := by
  rcases rep_spec mu with e | e
  · exact e
  · rw [e, h]

lemma rep_rep (mu : YoungDiagram) : rep (rep mu) = rep mu := by
  rcases rep_spec mu with e | e
  · conv_lhs => rw [e]
  · conv_lhs => rw [e]
    exact rep_tr mu

noncomputable def Ps (lam nu : YoungDiagram) : V lam →ₗ[ℂ] V nu :=
  if rep nu = nu then Q nu lam else 0

noncomputable def tsc (a : Label) (nu : YoungDiagram) (p : List Label) : List Label :=
  if (p.headD a).shape = nu then p.tail else p.tail.map trL

lemma head_sc (lam : YoungDiagram) (hl : lam.transpose = lam) (s : Bool) {nu : YoungDiagram}
    (hsc : nu.transpose = nu) (b : Label) (hD : Dagger (Label.sc lam hl s) b)
    (hg : rep b.shape = nu) : b = Label.sc nu hsc s := by
  cases b with
  | sc mu hm t =>
    change rep mu = nu at hg
    rw [rep_sc hm] at hg
    subst hg
    have ht : s = t := hD.2
    subst ht; rfl
  | nsc mu hm =>
    exfalso
    change rep mu = nu at hg
    rcases rep_eq hg with e | e
    · subst e; exact hm hsc
    · apply hm
      rw [← e, YoungDiagram.transpose_transpose] at hsc
      exact hsc.symm

lemma head_nsc {nu : YoungDiagram} (hsc : nu.transpose ≠ nu) (b : Label) (hg : rep b.shape = nu) :
    b = Label.nsc nu hsc ∨ ∃ h', b = Label.nsc nu.transpose h' := by
  cases b with
  | sc mu hm t =>
    exfalso
    change rep mu = nu at hg
    rw [rep_sc hm] at hg
    subst hg; exact hsc hm
  | nsc mu hm =>
    change rep mu = nu at hg
    rcases rep_eq hg with e | e
    · left; subst e; rfl
    · right
      have : mu = nu.transpose := by rw [← e, YoungDiagram.transpose_transpose]
      subst this; exact ⟨hm, rfl⟩

lemma nsc_pair_equiv {nu : YoungDiagram} (hsc : nu.transpose ≠ nu) {b b' : Label}
    (hb : b = Label.nsc nu hsc ∨ ∃ h', b = Label.nsc nu.transpose h')
    (hb' : b' = Label.nsc nu hsc ∨ ∃ h', b' = Label.nsc nu.transpose h') : Label.Equiv b b' := by
  rcases hb with rfl | ⟨h, rfl⟩ <;> rcases hb' with rfl | ⟨h', rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl, (YoungDiagram.transpose_transpose nu).symm⟩
  · exact Or.inl rfl

theorem ind_sc (lam : YoungDiagram) (hl : lam.transpose = lam) (s : Bool) (R : Set (List Label))
    (hR : PNE (Label.sc lam hl s) R) (hne : ∀ p ∈ R, p ≠ [])
    (hIH : ∀ b, Dagger (Label.sc lam hl s) b → ∀ R : Set (List Label), PNE b R →
      LinearIndependent ℂ (fun p : R => uVec b p.1)) :
    LinearIndependent ℂ (fun p : R => uVec (Label.sc lam hl s) p.1) := by
  have hcons : ∀ p ∈ R, ∃ b r, p = b :: r := by
    intro p hp
    cases p with
    | nil => exact absurd rfl (hne _ hp)
    | cons b r => exact ⟨b, r, rfl⟩
  apply linInd_of_proj (fun p : R => uVec (Label.sc lam hl s) p.1)
    (fun p : R => rep (p.1.headD (Label.sc lam hl s)).shape) (fun nu : YoungDiagram => V nu)
    (fun nu => Ps lam nu)
  · rintro ⟨p, hp⟩ nu hnu
    obtain ⟨b, r, rfl⟩ := hcons p hp
    have hpath := hR.1 _ hp
    change rep b.shape ≠ nu at hnu
    show Ps lam nu (uVec (Label.sc lam hl s) (b :: r)) = 0
    by_cases hrep : rep nu = nu
    · rw [Ps, if_pos hrep]
      have hD : YoungEdge b.shape lam := hpath.1.1
      cases b with
      | sc mu hm t =>
        change YoungEdge mu lam at hD
        change rep mu ≠ nu at hnu
        rw [uVec_cons_sc_sc]
        exact Q_embed_other hD (fun e => hnu (by rw [rep_sc hm]; exact e)) _
      | nsc mu hm =>
        change rep mu ≠ nu at hnu
        change YoungEdge mu lam at hD
        rw [uVec_cons_sc_nsc]
        exact Q_pm_other hl hD s (fun e => hnu (by rw [e]; exact hrep))
          (fun e => hnu (by rw [← rep_tr mu, e, hrep])) _
    · rw [Ps, if_neg hrep]; rfl
  · intro nu
    by_cases hrep : rep nu = nu
    swap
    · have : IsEmpty {i : R // rep (i.1.headD (Label.sc lam hl s)).shape = nu} :=
        ⟨fun ⟨i, hg⟩ => hrep (by
          have hg' : rep (i.1.headD (Label.sc lam hl s)).shape = nu := hg
          rw [← hg', rep_rep])⟩
      exact linearIndependent_empty_type
    have hP : Ps lam nu = Q nu lam := by rw [Ps, if_pos hrep]
    rw [hP]
    by_cases hsc : nu.transpose = nu
    · have hhead : ∀ i : {i : R // rep (i.1.headD (Label.sc lam hl s)).shape = nu},
          ∃ r, i.1.1 = Label.sc nu hsc s :: r ∧ IsPath (Label.sc nu hsc s) r := by
        rintro ⟨⟨p, hp⟩, hg⟩
        obtain ⟨b, r, rfl⟩ := hcons p hp
        have hpath := hR.1 _ hp
        have hb := head_sc lam hl s hsc b hpath.1 hg
        subst hb
        exact ⟨r, rfl, hpath.2⟩
      by_cases hD : Dagger (Label.sc lam hl s) (Label.sc nu hsc s)
      · have hE : YoungEdge nu lam := hD.1
        apply fiber_ind (Label.sc nu hsc s) (hIH _ hD) _ (fun i => i.1.1.tail)
        · intro i
          obtain ⟨r, e, hr⟩ := hhead i
          refine ⟨1, one_ne_zero, ?_⟩
          show Q nu lam (uVec (Label.sc lam hl s) i.1.1) = 1 • uVec (Label.sc nu hsc s) i.1.1.tail
          rw [e, uVec_cons_sc_sc]
          exact (Q_embed_self hE _).trans (one_smul ℂ _).symm
        · intro i
          obtain ⟨r, e, hr⟩ := hhead i
          show IsPath _ i.1.1.tail
          rw [e]; exact hr
        · intro i i' hF
          obtain ⟨r, e, hr⟩ := hhead i
          obtain ⟨r', e', hr'⟩ := hhead i'
          have hF' : List.Forall₂ Label.Equiv r r' := by
            have h0 : List.Forall₂ Label.Equiv i.1.1.tail i'.1.1.tail := hF
            rw [e, e'] at h0
            exact h0
          have := hR.2 _ i.1.2 _ i'.1.2 (by rw [e, e']; exact List.Forall₂.cons (Or.inl rfl) hF')
          exact Subtype.ext (Subtype.ext this)
      · have : IsEmpty {i : R // rep (i.1.headD (Label.sc lam hl s)).shape = nu} :=
          ⟨fun i => hD (by
            obtain ⟨r, e, hr⟩ := hhead i
            have := hR.1 _ i.1.2
            rw [e] at this
            exact this.1)⟩
        exact linearIndependent_empty_type
    · have hhead : ∀ i : {i : R // rep (i.1.headD (Label.sc lam hl s)).shape = nu},
          ∃ b r, i.1.1 = b :: r ∧ IsPath b r ∧ Dagger (Label.sc lam hl s) b ∧
            (b = Label.nsc nu hsc ∨ ∃ h', b = Label.nsc nu.transpose h') := by
        rintro ⟨⟨p, hp⟩, hg⟩
        obtain ⟨b, r, rfl⟩ := hcons p hp
        have hpath := hR.1 _ hp
        exact ⟨b, r, rfl, hpath.2, hpath.1, head_nsc hsc b hg⟩
      by_cases hE : YoungEdge nu lam
      · have hkey : ∀ i : {i : R // rep (i.1.headD (Label.sc lam hl s)).shape = nu},
            ∃ b r, i.1.1 = b :: r ∧ (b = Label.nsc nu hsc ∨ ∃ h', b = Label.nsc nu.transpose h') ∧
              List.Forall₂ Label.Equiv r (tsc (Label.sc lam hl s) nu i.1.1) ∧
              IsPath (Label.nsc nu hsc) (tsc (Label.sc lam hl s) nu i.1.1) ∧
              ∃ c : ℂ, c ≠ 0 ∧ Q nu lam (uVec (Label.sc lam hl s) i.1.1) =
                c • uVec (Label.nsc nu hsc) (tsc (Label.sc lam hl s) nu i.1.1) := by
          intro i
          obtain ⟨b, r, e, hr, hDb, hb⟩ := hhead i
          refine ⟨b, r, e, hb, ?_⟩
          rw [e]
          rcases hb with rfl | ⟨h', rfl⟩
          · have htr : tsc (Label.sc lam hl s) nu (Label.nsc nu hsc :: r) = r := by
              show (if (Label.nsc nu hsc).shape = nu then r else List.map trL r) = r
              exact if_pos rfl
            rw [htr, uVec_cons_sc_nsc]
            refine ⟨forall2_refl r, hr, 1, one_ne_zero, ?_⟩
            exact (Q_pm_self hl hE hsc s _).trans (one_smul ℂ _).symm
          · have htr : tsc (Label.sc lam hl s) nu (Label.nsc nu.transpose h' :: r) = r.map trL := by
              show (if (Label.nsc nu.transpose h').shape = nu then r else List.map trL r) =
                List.map trL r
              exact if_neg hsc
            have hE' : YoungEdge nu.transpose lam := hDb.1
            have hq : IsPath (Label.nsc nu hsc) (r.map trL) := by
              have := isPath_trL r _ hr
              rwa [show trL (Label.nsc nu.transpose h') = Label.nsc nu hsc from
                nsc_eq _ _ (YoungDiagram.transpose_transpose nu)] at this
            rw [htr, uVec_cons_sc_nsc]
            obtain ⟨d, hd0, hd⟩ := Q_pm_tr hl hE hE' hsc s (uVec (Label.nsc nu.transpose h') r)
            obtain ⟨κ, hκ⟩ := (E12 r).2 (Label.nsc nu.transpose h') (Label.nsc nu hsc) (r.map trL)
              rfl rfl (by show nu = nu.transpose.transpose; rw [YoungDiagram.transpose_transpose])
              hr hq (forall2_trL r)
            have hκ' : uVec (Label.nsc nu hsc) (r.map trL) =
                κ • Cinto nu (uVec (Label.nsc nu.transpose h') r) := hκ
            have hκ0 : κ ≠ 0 := by
              intro h0; exact (part1 _ _ hq).1 (by rw [hκ', h0]; exact zero_smul ℂ _)
            refine ⟨forall2_trL r, hq, d * κ⁻¹, mul_ne_zero hd0 (inv_ne_zero hκ0), ?_⟩
            exact hd.trans (smul_inv_aux d κ hκ0 _ _ hκ')
        apply fiber_ind (Label.nsc nu hsc) (hIH (Label.nsc nu hsc) ⟨hE, trivial⟩) _
          (fun i => tsc (Label.sc lam hl s) nu i.1.1)
        · intro i
          obtain ⟨b, r, -, -, -, -, hc⟩ := hkey i
          exact hc
        · intro i
          obtain ⟨b, r, -, -, -, hp, -⟩ := hkey i
          exact hp
        · intro i i' hF
          obtain ⟨b, r, e, hb, hFr, -, -⟩ := hkey i
          obtain ⟨b', r', e', hb', hFr', -, -⟩ := hkey i'
          have := hR.2 _ i.1.2 _ i'.1.2 (by
            rw [e, e']
            exact List.Forall₂.cons (nsc_pair_equiv hsc hb hb')
              (forall2_trans (forall2_trans hFr hF) (forall2_symm hFr')))
          exact Subtype.ext (Subtype.ext this)
      · have : IsEmpty {i : R // rep (i.1.headD (Label.sc lam hl s)).shape = nu} :=
          ⟨fun i => hE (by
            obtain ⟨b, r, -, -, hDb, hb⟩ := hhead i
            rcases hb with rfl | ⟨h', rfl⟩
            · exact hDb.1
            · exact edge_tr' hl hDb.1)⟩
        exact linearIndependent_empty_type

/-! ### The induction -/

theorem Ind : ∀ (n : ℕ) (a : Label), a.size = n + 2 → ∀ R : Set (List Label), PNE a R →
    LinearIndependent ℂ (fun p : R => uVec a p.1) := by
  intro n
  induction n with
  | zero => intro a ha R hR; exact ind_base a ha R hR
  | succ n ih =>
    intro a ha R hR
    have hne : ∀ p ∈ R, p ≠ [] := by
      intro p hp e
      have := path_length p a (hR.1 p hp)
      rw [e, List.length_nil] at this
      omega
    have hIH : ∀ b, Dagger a b → ∀ R : Set (List Label), PNE b R →
        LinearIndependent ℂ (fun p : R => uVec b p.1) := by
      intro b hD
      apply ih b
      have := edge_card hD.1
      have ha' : a.shape.cells.card = n + 1 + 2 := ha
      show b.shape.cells.card = n + 2
      omega
    cases a with
    | nsc lam hl => exact ind_nsc lam hl R hR hne hIH
    | sc lam hl s => exact ind_sc lam hl s R hR hne hIH

end Lib
end GTAlternating.Bases


set_option autoImplicit false

open GTAlternating.Bases in
theorem solution (n : ℕ) (hn : 2 ≤ n) (a : Label) (ha : a.size = n) :
    (∀ p : List Label, IsPath a p → IsGTVector a p (uVec a p)) ∧
    (∀ R : Set (List Label), (∀ p ∈ R, IsPath a p) →
      (∀ q, IsPath a q → ∃! p, p ∈ R ∧ List.Forall₂ Label.Equiv p q) →
      LinearIndependent ℂ (fun p : R => uVec a p.1) ∧
      Submodule.span ℂ (Set.range (fun p : R => uVec a p.1)) = a.space) := by
  refine ⟨fun p hp => ?_, fun R hRp hU => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := Lib.part1 p a hp
    refine ⟨h1, Submodule.mem_inf.2 ⟨h2, ?_⟩⟩
    simp only [Submodule.mem_iInf]
    exact h3
  · have ha' : a.size = (n - 2) + 2 := by omega
    have hPNE : Lib.PNE a R := by
      refine ⟨hRp, fun p hp q hq hF => ?_⟩
      obtain ⟨p0, -, huniq⟩ := hU q (hRp q hq)
      have e1 := huniq p ⟨hp, hF⟩
      have e2 := huniq q ⟨hq, Lib.forall2_refl q⟩
      rw [e1, e2]
    refine ⟨Lib.Ind (n - 2) a ha' R hPNE, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact (Lib.part1 p.1 a (hRp p.1 p.2)).2.1
    · rw [← Lib.spanAll (n - 2) a ha', Submodule.span_le]
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨p, ⟨hpR, hF⟩, -⟩ := hU q hq
      obtain ⟨κ, hκ⟩ := (Lib.E12 p).1 a q (hRp p hpR) hq hF
      rw [hκ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨p, hpR⟩, rfl⟩)

