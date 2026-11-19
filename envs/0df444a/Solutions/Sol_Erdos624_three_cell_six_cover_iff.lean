-- Prove2me | solution 1 for Erdos624.three_cell_six_cover_iff
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-18T10:25:49.458812+00:00
-- url     : https://prove2.me/submissions/249a9120-a510-48d6-9798-f1adbeb1a1ff

import Mathlib
open Finset Function

namespace E624R19T
open Finset Function

variable {U : Type*} [DecidableEq U]

abbrev Irow (P : Fin 3 → Finset U) (z : U) : Finset (Fin 3) :=
  univ.filter (fun i => z ∈ P i)

abbrev Jrow (E : Fin 3 → Finset U) (z : U) : Finset (Fin 3) :=
  univ.filter (fun j => z ∈ E j)

abbrev Hcell (R : Finset U) (P E : Fin 3 → Finset U) (i : Fin 3) : Finset (Fin 3) :=
  univ.filter (fun j => ∃ z ∈ R, Irow P z = univ.erase i ∧ j ∈ Jrow E z)

abbrev Lcell (R : Finset U) (P E : Fin 3 → Finset U) (i : Fin 3) : Finset (Fin 3) :=
  univ.filter (fun j => ∃ z ∈ R, Irow P z = {i} ∧ j ∉ Jrow E z)

abbrev criterion (R : Finset U) (P E : Fin 3 → Finset U) : Prop :=
  (∀ z ∈ R, Irow P z ≠ univ) ∧
  (∀ z ∈ R, #(Jrow E z) = 3 - #(Irow P z)) ∧
  (∀ i : Fin 3, Disjoint (Hcell R P E i) (Lcell R P E i))

abbrev sixFamily (P E : Fin 3 → Finset U) : Finset (Finset U) :=
  univ.image P ∪ univ.image E

lemma mem_sixFamily {P E : Fin 3 → Finset U} {A : Finset U} :
    A ∈ sixFamily P E ↔ (∃ i, P i = A) ∨ (∃ j, E j = A) := by
  simp [sixFamily, mem_union, mem_image]

lemma imageP_disjoint_imageE {R : Finset U} {x : U}
    {P E : Fin 3 → Finset U}
    (hP : ∀ i, P i ⊆ R) (hxE : ∀ i, x ∈ E i) (hx : x ∉ R) :
    Disjoint (univ.image P) (univ.image E) := by
  refine disjoint_left.2 ?_
  intro A hA hEim
  obtain ⟨i, _, hiA⟩ := mem_image.1 hA
  obtain ⟨j, _, hjA⟩ := mem_image.1 hEim
  exact hx (hP i (hiA ▸ (hjA ▸ hxE j)))

lemma filter_image_card_of_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) (p : β → Prop) [DecidablePred p]
    (hinj : Injective f) :
    #((s.image f).filter p) = #(s.filter (fun a => p (f a))) := by
  classical
  let s' := s.filter (fun a => p (f a))
  have himg : (s.image f).filter p = s'.image f := by
    ext b
    simp only [mem_image, mem_filter, s']
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hpb⟩
      exact ⟨a, ⟨ha, hpb⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hpb⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, hpb⟩
  rw [himg, card_image_of_injective _ hinj]

lemma degree_split {R : Finset U} {x : U} {P E : Fin 3 → Finset U} {z : U}
    (hP : ∀ i, P i ⊆ R) (hxE : ∀ i, x ∈ E i) (hx : x ∉ R)
    (hPinj : Injective P) (hEinj : Injective E) :
    #{A ∈ sixFamily P E | z ∈ A} = #(Irow P z) + #(Jrow E z) := by
  classical
  have hdis : Disjoint (univ.image P) (univ.image E) :=
    imageP_disjoint_imageE hP hxE hx
  have hdis' :
      Disjoint ((univ.image P).filter (fun A => z ∈ A))
        ((univ.image E).filter (fun A => z ∈ A)) :=
    disjoint_filter_filter hdis
  rw [sixFamily, filter_union, card_union_of_disjoint hdis',
    filter_image_card_of_injective _ P (fun A => z ∈ A) hPinj,
    filter_image_card_of_injective _ E (fun A => z ∈ A) hEinj]

lemma degree_at_x {R : Finset U} {x : U} {P E : Fin 3 → Finset U}
    (hP : ∀ i, P i ⊆ R) (hxE : ∀ i, x ∈ E i) (hx : x ∉ R)
    (hPinj : Injective P) (hEinj : Injective E) :
    #{A ∈ sixFamily P E | x ∈ A} = 3 := by
  classical
  have hxP : ∀ i, x ∉ P i := fun i h => hx (hP i h)
  have hI : Irow P x = ∅ := by ext i; simp [Irow, hxP]
  have hJ : Jrow E x = univ := by ext j; simp [Jrow, hxE]
  rw [degree_split (R := R) (x := x) hP hxE hx hPinj hEinj, hI, hJ]
  simp

lemma insert_card {R : Finset U} {x : U} (hx : x ∉ R) :
    #(insert x R) = #R + 1 :=
  card_insert_of_notMem hx

lemma card_sdiff_two {Z Y : Finset U} (hY : Y ⊆ Z) (hcard : #Y = #Z - 2)
    (hZ : 2 ≤ #Z) : #(Z \ Y) = 2 := by
  rw [card_sdiff_of_subset hY, hcard]; omega

lemma erase_erase_eq_sdiff (Z : Finset U) {z t : U} (hne : z ≠ t) :
    (Z.erase z).erase t = Z \ {z, t} := by
  ext y
  simp only [mem_erase, mem_sdiff, mem_insert, mem_singleton, not_or]
  tauto

lemma Irow_ne_univ_of_eligible {P : Fin 3 → Finset U} {z : U}
    (h : Irow P z ≠ univ) : #(Irow P z) ≤ 2 := by
  have hle : #(Irow P z) ≤ 3 := by simpa using card_le_card (subset_univ (Irow P z))
  rcases eq_or_lt_of_le hle with h3 | hlt
  · have : Irow P z = univ := eq_univ_of_card _ (by simpa using h3)
    exact (h this).elim
  · omega

lemma card_two_complement {s : Finset (Fin 3)} (h : #s = 2) :
    ∃ i, s = univ.erase i := by
  have : #(univ \ s) = 1 := by
    rw [card_sdiff_of_subset (subset_univ s), card_univ]; simp [h]
  obtain ⟨i, hi⟩ := card_eq_one.mp this
  refine ⟨i, ?_⟩
  have : s = univ \ {i} := by
    rw [← hi, Finset.sdiff_sdiff_eq_self (subset_univ s)]
  simpa [sdiff_singleton_eq_erase] using this

lemma erase_union_singleton (i : Fin 3) :
    univ.erase i ∪ {i} = (univ : Finset (Fin 3)) := by
  ext k
  by_cases hk : k = i
  · simp [hk]
  · simp [hk]

lemma singleton_union_erase (i : Fin 3) :
    ({i} : Finset (Fin 3)) ∪ univ.erase i = univ := by
  rw [union_comm]; exact erase_union_singleton i

/-- A face obtained by deleting `x` and `z ∈ R` is covered iff some pure row avoids `z`. -/
lemma covers_erase_x {R : Finset U} {x : U} {P E : Fin 3 → Finset U} {z : U}
    (hx : x ∉ R) (hz : z ∈ R) (hP : ∀ i, P i ⊆ R) (hxE : ∀ i, x ∈ E i) :
    (∃ A ∈ sixFamily P E, A ⊆ (R.erase z)) ↔ Irow P z ≠ univ := by
  classical
  constructor
  · rintro ⟨A, hA, hAY⟩ hI
    have hall : ∀ i, z ∈ P i := by
      intro i
      have : i ∈ Irow P z := by simp [hI]
      simpa [Irow] using this
    rcases (mem_sixFamily.1 hA) with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact (mem_erase.1 (hAY (hi ▸ hall i))).1 rfl
    · exact hx (mem_of_mem_erase (hAY (hj ▸ hxE j)))
  · intro hI
    obtain ⟨i, hi⟩ : ∃ i, z ∉ P i := by
      by_contra hall
      have : ∀ i, z ∈ P i := by
        intro i
        by_contra hni
        exact hall ⟨i, hni⟩
      have : Irow P z = univ := by ext j; simp [Irow, this]
      exact hI this
    refine ⟨P i, mem_union_left _ (mem_image.2 ⟨i, mem_univ i, rfl⟩), ?_⟩
    intro y hy
    exact mem_erase.2 ⟨fun e => hi (e ▸ hy), hP i hy⟩

/-- A face obtained by deleting two points of `R` is covered iff some pure
row avoids both or some exterior row avoids both. -/
lemma covers_pair_in_R {R : Finset U} {x : U} {P E : Fin 3 → Finset U} {z t : U}
    (hx : x ∉ R) (hz : z ∈ R) (ht : t ∈ R) (hne : z ≠ t)
    (hP : ∀ i, P i ⊆ R) (hE : ∀ i, E i ⊆ insert x R) (hxE : ∀ i, x ∈ E i) :
    (∃ A ∈ sixFamily P E, A ⊆ (insert x R) \ {z, t}) ↔
      Irow P z ∪ Irow P t ≠ univ ∨ Jrow E z ∪ Jrow E t ≠ univ := by
  classical
  constructor
  · rintro ⟨A, hA, hAY⟩
    have hzA : z ∉ A := fun h => by
      have := hAY h; simp [mem_sdiff] at this
    have htA : t ∉ A := fun h => by
      have := hAY h; simp [mem_sdiff] at this
    rcases (mem_sixFamily.1 hA) with ⟨i, hi⟩ | ⟨j, hj⟩
    · left
      intro hI
      have : i ∈ Irow P z ∪ Irow P t := by simp [hI]
      have : z ∈ P i ∨ t ∈ P i := by
        simpa [Irow, mem_union] using this
      rcases this with h | h
      · exact hzA (hi ▸ h)
      · exact htA (hi ▸ h)
    · right
      intro hJ
      have : j ∈ Jrow E z ∪ Jrow E t := by simp [hJ]
      have : z ∈ E j ∨ t ∈ E j := by
        simpa [Jrow, mem_union] using this
      rcases this with h | h
      · exact hzA (hj ▸ h)
      · exact htA (hj ▸ h)
  · intro h
    rcases h with hI | hJ
    · obtain ⟨i, hi⟩ : ∃ i, i ∉ Irow P z ∪ Irow P t := by
        by_contra hall
        have : ∀ i, i ∈ Irow P z ∪ Irow P t := by
          intro i; by_contra hni; exact hall ⟨i, hni⟩
        have : Irow P z ∪ Irow P t = univ := by ext i; simp [this]
        exact hI this
      have hzi : z ∉ P i ∧ t ∉ P i := by simpa [Irow, mem_union] using hi
      refine ⟨P i, mem_union_left _ (mem_image.2 ⟨i, mem_univ i, rfl⟩), ?_⟩
      intro y hy
      have hyR : y ∈ R := hP i hy
      have hyx : y ≠ x := fun e => hx (e ▸ hyR)
      refine mem_sdiff.2 ⟨mem_insert_of_mem hyR, ?_⟩
      simp [mem_insert, mem_singleton, hyx, hzi.1, hzi.2, fun e : y = z => hzi.1 (e ▸ hy),
        fun e : y = t => hzi.2 (e ▸ hy)]
      exact ⟨fun e => hzi.1 (e ▸ hy), fun e => hzi.2 (e ▸ hy)⟩
    · obtain ⟨j, hj⟩ : ∃ j, j ∉ Jrow E z ∪ Jrow E t := by
        by_contra hall
        have : ∀ j, j ∈ Jrow E z ∪ Jrow E t := by
          intro j; by_contra hnj; exact hall ⟨j, hnj⟩
        have : Jrow E z ∪ Jrow E t = univ := by ext j; simp [this]
        exact hJ this
      have hzj : z ∉ E j ∧ t ∉ E j := by simpa [Jrow, mem_union] using hj
      refine ⟨E j, mem_union_right _ (mem_image.2 ⟨j, mem_univ j, rfl⟩), ?_⟩
      intro y hy
      have hyZ : y ∈ insert x R := hE j hy
      refine mem_sdiff.2 ⟨hyZ, ?_⟩
      exact fun hym => by
        have : y = z ∨ y = t := by simpa [mem_insert, mem_singleton] using hym
        rcases this with e | e
        · exact hzj.1 (e ▸ hy)
        · exact hzj.2 (e ▸ hy)

lemma pair_ok_of_criterion {R : Finset U} {P E : Fin 3 → Finset U} {u v : U}
    (hu : u ∈ R) (hv : v ∈ R) (huv : u ≠ v)
    (helig : ∀ z ∈ R, Irow P z ≠ univ)
    (hbal : ∀ z ∈ R, #(Jrow E z) = 3 - #(Irow P z))
    (hHL : ∀ i : Fin 3, Disjoint (Hcell R P E i) (Lcell R P E i)) :
    Irow P u ∪ Irow P v ≠ univ ∨ Jrow E u ∪ Jrow E v ≠ univ := by
  classical
  by_cases hIu : Irow P u ∪ Irow P v = univ
  · right
    intro hJun
    have hIule : #(Irow P u) ≤ 2 := Irow_ne_univ_of_eligible (helig u hu)
    have hIvle : #(Irow P v) ≤ 2 := Irow_ne_univ_of_eligible (helig v hv)
    have hJu : #(Jrow E u) = 3 - #(Irow P u) := hbal u hu
    have hJv : #(Jrow E v) = 3 - #(Irow P v) := hbal v hv
    have hIcard : #(Irow P u ∪ Irow P v) = 3 := by simp [hIu]
    have hJcard : #(Jrow E u ∪ Jrow E v) = 3 := by simp [hJun]
    have hcases :
        (#(Irow P u) = 2 ∧ #(Irow P v) = 2) ∨
        (#(Irow P u) = 2 ∧ #(Irow P v) = 1) ∨
        (#(Irow P u) = 1 ∧ #(Irow P v) = 2) := by
      have := card_union_add_card_inter (Irow P u) (Irow P v)
      omega
    rcases hcases with h22 | h21 | h12
    · have : #(Jrow E u ∪ Jrow E v) ≤ 2 :=
        (card_union_le (Jrow E u) (Jrow E v)).trans (by omega)
      omega
    · obtain ⟨i, hiU⟩ := card_two_complement h21.1
      have hiV : Irow P v = {i} := by
        have hiNotU : i ∉ Irow P u := by simp [hiU]
        have hiVmem : i ∈ Irow P v := by
          have : i ∈ Irow P u ∪ Irow P v := by simp [hIu]
          simpa [mem_union, hiNotU] using this
        obtain ⟨k, hk⟩ := card_eq_one.mp h21.2
        have hik : i = k := by
          have : i ∈ ({k} : Finset _) := by simpa [hk] using hiVmem
          simpa using this
        simpa [hik] using hk
      have hJu1 : #(Jrow E u) = 1 := by omega
      have hJv2 : #(Jrow E v) = 2 := by omega
      obtain ⟨ju, hju⟩ := card_eq_one.mp hJu1
      obtain ⟨lv, hlv⟩ := card_two_complement hJv2
      have hH : ju ∈ Hcell R P E i := by
        refine mem_filter.2 ⟨mem_univ _, ⟨u, hu, hiU, ?_⟩⟩
        simp [hju]
      have hL : lv ∈ Lcell R P E i := by
        refine mem_filter.2 ⟨mem_univ _, ⟨v, hv, hiV, ?_⟩⟩
        simp [hlv]
      have hju_not : ju ∉ Jrow E v := by
        intro hmem
        have : Jrow E u ∪ Jrow E v = Jrow E v := by
          rw [hju]; exact union_eq_right.2 (singleton_subset_iff.2 hmem)
        have : #(Jrow E v) = 3 := by simpa [this] using hJcard
        omega
      have : ju = lv := by
        have hmem : ju ∈ univ \ Jrow E v := mem_sdiff.2 ⟨mem_univ _, hju_not⟩
        have heq : univ \ Jrow E v = {lv} := by
          rw [hlv, ← sdiff_singleton_eq_erase]
          exact Finset.sdiff_sdiff_eq_self (singleton_subset_iff.2 (mem_univ lv))
        simpa [heq] using hmem
      exact (not_disjoint_iff.2 ⟨ju, hH, by simpa [this] using hL⟩) (hHL i)
    · obtain ⟨i, hiV⟩ := card_two_complement h12.2
      have hiU : Irow P u = {i} := by
        have hiNotV : i ∉ Irow P v := by simp [hiV]
        have hiUmem : i ∈ Irow P u := by
          have : i ∈ Irow P u ∪ Irow P v := by simp [hIu]
          simpa [mem_union, hiNotV] using this
        obtain ⟨k, hk⟩ := card_eq_one.mp h12.1
        have hik : i = k := by
          have : i ∈ ({k} : Finset _) := by simpa [hk] using hiUmem
          simpa using this
        simpa [hik] using hk
      have hJu2 : #(Jrow E u) = 2 := by omega
      have hJv1 : #(Jrow E v) = 1 := by omega
      obtain ⟨jv, hjv⟩ := card_eq_one.mp hJv1
      obtain ⟨lu, hlu⟩ := card_two_complement hJu2
      have hH : jv ∈ Hcell R P E i := by
        refine mem_filter.2 ⟨mem_univ _, ⟨v, hv, hiV, ?_⟩⟩
        simp [hjv]
      have hL : lu ∈ Lcell R P E i := by
        refine mem_filter.2 ⟨mem_univ _, ⟨u, hu, hiU, ?_⟩⟩
        simp [hlu]
      have hjv_not : jv ∉ Jrow E u := by
        intro hmem
        have : Jrow E u ∪ Jrow E v = Jrow E u := by
          rw [hjv]; exact union_eq_left.2 (singleton_subset_iff.2 hmem)
        have : #(Jrow E u) = 3 := by simpa [this] using hJcard
        omega
      have : jv = lu := by
        have hmem : jv ∈ univ \ Jrow E u := mem_sdiff.2 ⟨mem_univ _, hjv_not⟩
        have heq : univ \ Jrow E u = {lu} := by
          rw [hlu, ← sdiff_singleton_eq_erase]
          exact Finset.sdiff_sdiff_eq_self (singleton_subset_iff.2 (mem_univ lu))
        simpa [heq] using hmem
      exact (not_disjoint_iff.2 ⟨jv, hH, by simpa [this] using hL⟩) (hHL i)
  · exact Or.inl hIu

theorem three_cell_six_cover_iff (R : Finset U) (x : U) (hx : x ∉ R)
    (P E : Fin 3 → Finset U)
    (hPinj : Injective P) (hEinj : Injective E)
    (hP : ∀ i, P i ⊆ R) (hE : ∀ i, E i ⊆ insert x R) (hxE : ∀ i, x ∈ E i)
    (hR : 1 ≤ #R) :
    criterion R P E ↔
      (∀ y ∈ insert x R, #{A ∈ sixFamily P E | y ∈ A} = 3) ∧
      (∀ Y ⊆ insert x R, #Y = #(insert x R) - 2 →
        ∃ A ∈ sixFamily P E, A ⊆ Y) := by
  classical
  constructor
  · intro hcr
    rcases hcr with ⟨helig, hbal, hHL⟩
    constructor
    · intro y hy
      by_cases hxy : y = x
      · rw [hxy]
        exact degree_at_x (R := R) (x := x) hP hxE hx hPinj hEinj
      · have hyR : y ∈ R := (mem_insert.1 hy).resolve_left hxy
        rw [degree_split (R := R) (x := x) hP hxE hx hPinj hEinj, hbal y hyR]
        have : #(Irow P y) ≤ 2 := Irow_ne_univ_of_eligible (helig y hyR)
        omega
    · intro Y hYsub hYcard
      have hZcard : 2 ≤ #(insert x R) := by rw [insert_card hx]; omega
      have hmiss : #((insert x R) \ Y) = 2 := card_sdiff_two hYsub hYcard hZcard
      obtain ⟨u, v, huv, hUV⟩ := card_eq_two.mp hmiss
      have hu : u ∈ insert x R ∧ u ∉ Y := mem_sdiff.1 (by simp [hUV])
      have hv : v ∈ insert x R ∧ v ∉ Y := mem_sdiff.1 (by simp [hUV])
      have hYeq : Y = (insert x R) \ {u, v} := by
        ext y
        constructor
        · intro hy
          refine mem_sdiff.2 ⟨hYsub hy, ?_⟩
          intro hym
          have : y ∈ (insert x R) \ Y := by simpa [hUV] using hym
          exact (mem_sdiff.1 this).2 hy
        · intro hy
          have hyZ : y ∈ insert x R := (mem_sdiff.1 hy).1
          have hynot : y ∉ ({u, v} : Finset U) := (mem_sdiff.1 hy).2
          by_contra hnot
          have : y ∈ (insert x R) \ Y := mem_sdiff.2 ⟨hyZ, hnot⟩
          have : y ∈ ({u, v} : Finset U) := by simpa [hUV] using this
          exact hynot this
      rcases mem_insert.1 hu.1 with hux | huR
      · -- u = x, so v ∈ R (do not subst, so the name `x` remains)
        have hvR : v ∈ R := by
          rcases mem_insert.1 hv.1 with hvx | hvR
          · exact (huv (hux.trans hvx.symm)).elim
          · exact hvR
        have hY' : Y = R.erase v := by
          rw [hYeq, hux]
          ext y
          constructor
          · intro hy
            have hyZ : y ∈ insert x R := (mem_sdiff.1 hy).1
            have hynot : y ∉ ({x, v} : Finset U) := (mem_sdiff.1 hy).2
            have hyx : y ≠ x := fun e => hynot (by simp [e])
            have hyv : y ≠ v := fun e => hynot (by simp [e])
            have hyR : y ∈ R := (mem_insert.1 hyZ).resolve_left hyx
            exact mem_erase.2 ⟨hyv, hyR⟩
          · intro hy
            have hyR : y ∈ R := mem_of_mem_erase hy
            have hyv : y ≠ v := (mem_erase.1 hy).1
            have hyx : y ≠ x := fun e => hx (e ▸ hyR)
            refine mem_sdiff.2 ⟨mem_insert_of_mem hyR, ?_⟩
            simp [mem_insert, mem_singleton, hyx, hyv]
        simpa [hY'] using
          (covers_erase_x (R := R) (x := x) (P := P) (E := E) (z := v)
            hx hvR hP hxE).2 (helig v hvR)
      · rcases mem_insert.1 hv.1 with hvx | hvR
        · have hY' : Y = R.erase u := by
            rw [hYeq, hvx]
            ext y
            constructor
            · intro hy
              have hyZ : y ∈ insert x R := (mem_sdiff.1 hy).1
              have hynot : y ∉ ({u, x} : Finset U) := (mem_sdiff.1 hy).2
              have hyx : y ≠ x := fun e => hynot (by simp [e])
              have hyu : y ≠ u := fun e => hynot (by simp [e])
              have hyR : y ∈ R := (mem_insert.1 hyZ).resolve_left hyx
              exact mem_erase.2 ⟨hyu, hyR⟩
            · intro hy
              have hyR : y ∈ R := mem_of_mem_erase hy
              have hyu : y ≠ u := (mem_erase.1 hy).1
              have hyx : y ≠ x := fun e => hx (e ▸ hyR)
              refine mem_sdiff.2 ⟨mem_insert_of_mem hyR, ?_⟩
              simp [mem_insert, mem_singleton, hyx, hyu]
          simpa [hY'] using
            (covers_erase_x (R := R) (x := x) (P := P) (E := E) (z := u)
              hx huR hP hxE).2 (helig u huR)
        · have hgoal := pair_ok_of_criterion huR hvR huv helig hbal hHL
          have hY' : Y = (insert x R) \ {u, v} := hYeq
          simpa [hY'] using
            (covers_pair_in_R (R := R) (x := x) (P := P) (E := E) (z := u) (t := v)
              hx huR hvR huv hP hE hxE).2 hgoal
  · intro h
    rcases h with ⟨hbalZ, hcov⟩
    refine And.intro ?_ (And.intro ?_ ?_)
    · intro z hz hI
      have hY : R.erase z ⊆ insert x R := (erase_subset z R).trans (subset_insert x R)
      have hYcard : #(R.erase z) = #(insert x R) - 2 := by
        rw [card_erase_of_mem hz, insert_card hx]; omega
      obtain ⟨A, hA, hAY⟩ := hcov _ hY hYcard
      exact (covers_erase_x (R := R) (x := x) (P := P) (E := E) (z := z)
        hx hz hP hxE).1 ⟨A, hA, hAY⟩ hI
    · intro z hz
      have := hbalZ z (mem_insert_of_mem hz)
      rw [degree_split (R := R) (x := x) hP hxE hx hPinj hEinj] at this
      have : #(Irow P z) ≤ 3 := by simpa using card_le_card (subset_univ (Irow P z))
      omega
    · intro i
      refine disjoint_left.2 ?_
      intro j hH hL
      obtain ⟨z, hz, hIz, hJz⟩ := (mem_filter.1 hH).2
      obtain ⟨t, ht, hIt, hJt⟩ := (mem_filter.1 hL).2
      have hzt : z ≠ t := by
        intro e
        have hIt' : univ.erase i = ({i} : Finset (Fin 3)) := by
          rw [← e, hIz] at hIt; exact hIt
        have : i ∈ univ.erase i := by simpa [hIt']
        simp at this
      have hIu : Irow P z ∪ Irow P t = univ := by
        rw [hIz, hIt]; exact erase_union_singleton i
      -- use already-proved balance on R
      have hbalz : #(Jrow E z) = 3 - #(Irow P z) := by
        have := hbalZ z (mem_insert_of_mem hz)
        rw [degree_split (R := R) (x := x) hP hxE hx hPinj hEinj] at this
        have : #(Irow P z) ≤ 3 := by simpa using card_le_card (subset_univ (Irow P z))
        omega
      have hbalt : #(Jrow E t) = 3 - #(Irow P t) := by
        have := hbalZ t (mem_insert_of_mem ht)
        rw [degree_split (R := R) (x := x) hP hxE hx hPinj hEinj] at this
        have : #(Irow P t) ≤ 3 := by simpa using card_le_card (subset_univ (Irow P t))
        omega
      have hJz1 : #(Jrow E z) = 1 := by simp [hIz] at hbalz; exact hbalz
      have hJt2 : #(Jrow E t) = 2 := by simp [hIt] at hbalt; exact hbalt
      have hJzsing : Jrow E z = {j} := by
        obtain ⟨j', hj'⟩ := card_eq_one.mp hJz1
        have : j = j' := by
          have : j ∈ ({j'} : Finset _) := by simpa [hj'] using hJz
          simpa using this
        simpa [this] using hj'
      have hJterase : Jrow E t = univ.erase j := by
        obtain ⟨k, hk⟩ := card_two_complement hJt2
        have heq : univ \ Jrow E t = {k} := by
          rw [hk, ← sdiff_singleton_eq_erase]
          exact Finset.sdiff_sdiff_eq_self (singleton_subset_iff.2 (mem_univ k))
        have : k = j := by
          have : j ∈ univ \ Jrow E t := mem_sdiff.2 ⟨mem_univ _, hJt⟩
          have : j = k := by simpa [heq] using this
          exact this.symm
        simpa [this] using hk
      have hJu : Jrow E z ∪ Jrow E t = univ := by
        rw [hJzsing, hJterase]; exact singleton_union_erase j
      have hYsub : (insert x R) \ {z, t} ⊆ insert x R := sdiff_subset
      have hYcard : #((insert x R) \ {z, t}) = #(insert x R) - 2 := by
        have hst : {z, t} ⊆ insert x R := by
          intro w hw
          have : w = z ∨ w = t := by simpa [mem_insert, mem_singleton] using hw
          rcases this with rfl | rfl
          · exact mem_insert_of_mem hz
          · exact mem_insert_of_mem ht
        have hcard2 : #({z, t} : Finset U) = 2 := by simp [hzt]
        rw [card_sdiff_of_subset hst, hcard2]
      obtain ⟨A, hA, hAY⟩ := hcov _ hYsub hYcard
      have hcov' := (covers_pair_in_R (R := R) (x := x) (P := P) (E := E) (z := z) (t := t)
        hx hz ht hzt hP hE hxE).1 ⟨A, hA, hAY⟩
      exact hcov'.elim (fun h => h hIu) (fun h => h hJu)

end E624R19T

namespace Erdos624

theorem three_cell_six_cover_iff {U : Type*} [DecidableEq U]
    (R : Finset U) (x : U) (hx : x ∉ R)
    (P E : Fin 3 → Finset U)
    (hPinj : Function.Injective P) (hEinj : Function.Injective E)
    (hP : ∀ i, P i ⊆ R) (hE : ∀ i, E i ⊆ insert x R) (hxE : ∀ i, x ∈ E i)
    (hR : 1 ≤ #R) :
    ((∀ z ∈ R, (univ.filter (fun i : Fin 3 => z ∈ P i) : Finset (Fin 3)) ≠ univ) ∧
      (∀ z ∈ R, #(univ.filter (fun j : Fin 3 => z ∈ E j)) =
        3 - #(univ.filter (fun i : Fin 3 => z ∈ P i))) ∧
      (∀ i : Fin 3,
        Disjoint
          (univ.filter (fun j : Fin 3 =>
            ∃ z ∈ R, univ.filter (fun k : Fin 3 => z ∈ P k) = univ.erase i ∧
              j ∈ univ.filter (fun k : Fin 3 => z ∈ E k)))
          (univ.filter (fun j : Fin 3 =>
            ∃ z ∈ R, univ.filter (fun k : Fin 3 => z ∈ P k) = {i} ∧
              j ∉ univ.filter (fun k : Fin 3 => z ∈ E k))))) ↔
    ((∀ y ∈ insert x R,
        #{A ∈ (univ.image P ∪ univ.image E) | y ∈ A} = 3) ∧
      (∀ Y ⊆ insert x R, #Y = #(insert x R) - 2 →
        ∃ A ∈ univ.image P ∪ univ.image E, A ⊆ Y)) :=
  E624R19T.three_cell_six_cover_iff R x hx P E hPinj hEinj hP hE hxE hR

end Erdos624

open Finset Function

theorem solution {U : Type*} [DecidableEq U]
    (R : Finset U) (x : U) (hx : x ∉ R)
    (P E : Fin 3 → Finset U)
    (hPinj : Injective P) (hEinj : Injective E)
    (hP : ∀ i, P i ⊆ R) (hE : ∀ i, E i ⊆ insert x R) (hxE : ∀ i, x ∈ E i)
    (hR : 1 ≤ #R) :
    ((∀ z ∈ R, (univ.filter (fun i : Fin 3 => z ∈ P i) : Finset (Fin 3)) ≠ univ) ∧
      (∀ z ∈ R, #(univ.filter (fun j : Fin 3 => z ∈ E j)) =
        3 - #(univ.filter (fun i : Fin 3 => z ∈ P i))) ∧
      (∀ i : Fin 3,
        Disjoint
          (univ.filter (fun j : Fin 3 =>
            ∃ z ∈ R, univ.filter (fun k : Fin 3 => z ∈ P k) = univ.erase i ∧
              j ∈ univ.filter (fun k : Fin 3 => z ∈ E k)))
          (univ.filter (fun j : Fin 3 =>
            ∃ z ∈ R, univ.filter (fun k : Fin 3 => z ∈ P k) = {i} ∧
              j ∉ univ.filter (fun k : Fin 3 => z ∈ E k))))) ↔
    ((∀ y ∈ insert x R,
        #{A ∈ (univ.image P ∪ univ.image E) | y ∈ A} = 3) ∧
      (∀ Y ⊆ insert x R, #Y = #(insert x R) - 2 →
        ∃ A ∈ univ.image P ∪ univ.image E, A ⊆ Y)) :=
  Erdos624.three_cell_six_cover_iff R x hx P E hPinj hEinj hP hE hxE hR
