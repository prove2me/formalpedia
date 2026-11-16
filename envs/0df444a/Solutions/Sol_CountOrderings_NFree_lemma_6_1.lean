-- Prove2me | solution 1 for CountOrderings.NFree.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @bersubs
-- created : 2026-11-15T17:19:16.047787+00:00
-- url     : https://prove2.me/submissions/3ed650ff-667c-4041-99aa-d25624917cad

import Definitions.Def_CountOrderings_NFree_Reduction

namespace CountOrderings.NFree

private def rootEdge (I : X3CInstance) (s : Fin I.n) : OrigEdge I :=
  ⟨.rootSet s, trivial⟩

private def incidenceEdge (I : X3CInstance) (s : Fin I.n) (j : Fin (3 * I.h))
    (hsj : j ∈ I.S s) : OrigEdge I := ⟨.setElem s j, hsj⟩

private noncomputable def incomingPositions {I : X3CInstance}
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) : Finset (Fin (4 * I.n)) := by
  classical
  exact Finset.univ.filter (fun p => ∃ s : Fin I.n, (σ p).1 = .setElem s j)

private theorem mem_incomingPositions {I : X3CInstance}
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) (p : Fin (4 * I.n)) :
    p ∈ incomingPositions σ j ↔ ∃ s : Fin I.n, (σ p).1 = .setElem s j := by
  classical
  simp [incomingPositions]

private theorem incomingPositions_nonempty {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) :
    (incomingPositions σ j).Nonempty := by
  obtain ⟨s, hsj⟩ := hI.1 j
  refine ⟨σ.symm (incidenceEdge I s j hsj), (mem_incomingPositions ..).mpr ⟨s, ?_⟩⟩
  rw [Equiv.apply_symm_apply]
  rfl

private noncomputable def lastPosition {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) : Fin (4 * I.n) :=
  (incomingPositions σ j).max' (incomingPositions_nonempty hI σ j)

private theorem lastPosition_spec {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) :
    ∃ s : Fin I.n, (σ (lastPosition hI σ j)).1 = .setElem s j :=
  (mem_incomingPositions ..).mp (Finset.max'_mem _ _)

private theorem le_lastPosition {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) {p : Fin (4 * I.n)}
    (hp : ∃ s : Fin I.n, (σ p).1 = .setElem s j) : p ≤ lastPosition hI σ j :=
  Finset.le_max' _ _ ((mem_incomingPositions ..).mpr hp)

private theorem rho_eq_lastPosition {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (j : Fin (3 * I.h)) :
    rho σ j = (lastPosition hI σ j).val + 1 := by
  change (incomingPositions σ j).sup (fun p => p.val + 1) = _
  apply le_antisymm
  · refine Finset.sup_le_iff.mpr fun p hp => Nat.succ_le_succ ?_
    exact le_lastPosition hI σ j ((mem_incomingPositions ..).mp hp)
  · exact Finset.le_sup (f := fun p : Fin (4 * I.n) => p.val + 1) (Finset.max'_mem _ _)

/-- The marked positions are the set-root edges and the last incidence into each universe
element. The two kinds of marks occupy distinct positions. -/
private noncomputable def marker {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) : Fin (3 * I.h) ⊕ Fin I.n ↪ Fin (4 * I.n) where
  toFun := Sum.elim (lastPosition hI σ) (fun s => σ.symm (rootEdge I s))
  inj' := by
    rintro (j | s) (k | t) h
    · change lastPosition hI σ j = lastPosition hI σ k at h
      obtain ⟨s, hs⟩ := lastPosition_spec hI σ j
      obtain ⟨t, ht⟩ := lastPosition_spec hI σ k
      rw [h, ht] at hs
      cases hs
      rfl
    · change lastPosition hI σ j = σ.symm (rootEdge I t) at h
      obtain ⟨s, hs⟩ := lastPosition_spec hI σ j
      rw [h, Equiv.apply_symm_apply] at hs
      cases hs
    · change σ.symm (rootEdge I s) = lastPosition hI σ k at h
      obtain ⟨t, ht⟩ := lastPosition_spec hI σ k
      rw [← h, Equiv.apply_symm_apply] at ht
      cases ht
    · change σ.symm (rootEdge I s) = σ.symm (rootEdge I t) at h
      have hs := congrArg Subtype.val (σ.symm.injective h)
      cases hs
      rfl

private noncomputable def marked {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) : Finset (Fin (4 * I.n)) :=
  Finset.univ.map (marker hI σ)

private def suffix (I : X3CInstance) (i : ℕ) : Finset (Fin (4 * I.n)) :=
  Finset.univ.filter (fun p => 4 * I.n ≤ p.val + i)

private theorem mem_suffix {I : X3CInstance} (i : ℕ) (p : Fin (4 * I.n)) :
    p ∈ suffix I i ↔ 4 * I.n ≤ p.val + i := by
  simp [suffix]

private theorem rootPosition_iff {I : X3CInstance}
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (p : Fin (4 * I.n)) (s : Fin I.n) :
    p = σ.symm (rootEdge I s) ↔ (σ p).1 = .rootSet s := by
  constructor
  · rintro rfl
    rw [Equiv.apply_symm_apply]
    rfl
  · intro hp
    apply σ.injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext hp


private noncomputable def suffixTargets {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) : Finset (Fin (3 * I.h)) := by
  classical
  exact Finset.univ.filter (fun j => lastPosition hI σ j ∈ suffix I i)

private def suffixRoots {I : X3CInstance}
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) : Finset (Fin I.n) :=
  Finset.univ.filter (fun s => σ.symm (rootEdge I s) ∈ suffix I i)

private theorem mem_suffixTargets {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) (j : Fin (3 * I.h)) :
    j ∈ suffixTargets hI σ i ↔ lastPosition hI σ j ∈ suffix I i := by
  classical
  simp [suffixTargets]

private theorem mem_suffixRoots {I : X3CInstance}
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) (s : Fin I.n) :
    s ∈ suffixRoots σ i ↔ σ.symm (rootEdge I s) ∈ suffix I i := by
  simp [suffixRoots]

private theorem Ccount_split {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) (hi : i ≤ 4 * I.n) :
    Ccount σ i = (suffixTargets hI σ i).card + (suffixRoots σ i).card := by
  classical
  unfold Ccount
  apply congrArg₂ (· + ·) <;> apply congrArg Finset.card
  · ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_suffixTargets,
      rho_eq_lastPosition hI, mem_suffix]
    omega
  · ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_suffixRoots,
      ← rootPosition_iff σ, mem_suffix]
    constructor
    · rintro ⟨p, hp, rfl⟩
      omega
    · intro hp
      exact ⟨_, by omega, rfl⟩

private theorem Ccount_eq_marked {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) (hi : i ≤ 4 * I.n) :
    Ccount σ i = ((suffix I i).filter (fun p => p ∈ marked hI σ)).card := by
  classical
  rw [Ccount_split hI σ i hi]
  have hmem (z : Fin (3 * I.h) ⊕ Fin I.n) :
      z ∈ (suffixTargets hI σ i).disjSum (suffixRoots σ i) ↔
        marker hI σ z ∈ suffix I i := by
    cases z with
    | inl j => exact Finset.inl_mem_disjSum.trans (mem_suffixTargets hI σ i j)
    | inr s => exact Finset.inr_mem_disjSum.trans (mem_suffixRoots σ i s)
  rw [← Finset.card_disjSum, ← Finset.card_map (f := marker hI σ)]
  apply congrArg Finset.card
  ext p
  simp only [marked, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, hmem]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hz, z, rfl⟩
  · rintro ⟨hp, z, rfl⟩
    exact ⟨z, hp, rfl⟩

private theorem suffix_step {I : X3CInstance} (i : ℕ) (hi : i < 4 * I.n) :
    suffix I (i + 1) =
      insert (⟨4 * I.n - (i + 1), by omega⟩ : Fin (4 * I.n)) (suffix I i) := by
  ext p
  simp only [mem_suffix, Finset.mem_insert, Fin.ext_iff]
  omega

private theorem suffix_card {I : X3CInstance} (i : ℕ) (hi : i ≤ 4 * I.n) :
    (suffix I i).card = i := by
  induction i with
  | zero =>
    have he : suffix I 0 = ∅ := by
      ext p
      simp [mem_suffix, Nat.not_le_of_gt p.isLt]
    simp [he]
  | succ i ih =>
    rw [suffix_step i (by omega), Finset.card_insert_of_notMem, ih (by omega)]
    rw [mem_suffix]
    simp only
    omega

private theorem Ccount_le_index {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) (hi : i ≤ 4 * I.n) :
    Ccount σ i ≤ i := by
  classical
  calc
    Ccount σ i = ((suffix I i).filter (fun p => p ∈ marked hI σ)).card :=
      Ccount_eq_marked hI σ i hi
    _ ≤ (suffix I i).card := Finset.card_filter_le _ _
    _ = i := suffix_card i hi

private theorem suffix_target_iff_exists {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) (j : Fin (3 * I.h)) :
    j ∈ suffixTargets hI σ i ↔
      ∃ p ∈ suffix I i, ∃ s : Fin I.n, (σ p).val = .setElem s j := by
  rw [mem_suffixTargets]
  constructor
  · intro hp
    exact ⟨lastPosition hI σ j, hp, lastPosition_spec hI σ j⟩
  · rintro ⟨p, hp, he⟩
    have hle : p.val ≤ (lastPosition hI σ j).val := le_lastPosition hI σ j he
    rw [mem_suffix] at hp ⊢
    omega

private theorem root_before_incidence {I : X3CInstance}
    {σ : Fin (4 * I.n) ≃ OrigEdge I} (hσ : σ ∈ omegaLE I)
    {s : Fin I.n} {j : Fin (3 * I.h)} (hsj : j ∈ I.S s) :
    σ.symm (rootEdge I s) < σ.symm (incidenceEdge I s j hsj) := by
  have hLE : ∀ e f : OrigEdge I, (baseDAG I).EdgeLE e f → σ.symm e ≤ σ.symm f := by
    simpa only [omegaLE, Finset.mem_filter, Finset.mem_univ, true_and] using hσ
  apply lt_of_le_of_ne (hLE _ _ (Relation.ReflTransGen.single (by rfl)))
  intro he
  have hv := congrArg Subtype.val (σ.symm.injective he)
  cases hv

private theorem mem_edgesOf_iff {I : X3CInstance} {X : Finset (Fin I.n)}
    {e : OrigEdge I} : e ∈ edgesOf I X ↔ e.setIdx ∈ X := by
  classical
  simp [edgesOf]

private def coverIncidences (I : X3CInstance) (X : Finset (Fin I.n)) : Type :=
  Σ s : ↥X, ↥(I.S s.val)

private instance coverIncidencesFintype (I : X3CInstance) (X : Finset (Fin I.n)) :
    Fintype (coverIncidences I X) :=
  inferInstanceAs (Fintype (Σ s : ↥X, ↥(I.S s.val)))

private theorem card_coverIncidences (I : X3CInstance) (X : Finset (Fin I.n)) :
    Fintype.card (coverIncidences I X) = 3 * X.card := by
  change Fintype.card (Σ s : ↥X, ↥(I.S s.val)) = _
  rw [Fintype.card_sigma]
  simp [I.card_S, Nat.mul_comm]

private noncomputable def edgeSetEquiv (I : X3CInstance) (X : Finset (Fin I.n)) :
    ↥(edgesOf I X) ≃ ↥X ⊕ coverIncidences I X where
  toFun e := match e with
    | ⟨⟨.rootSet s, _⟩, hs⟩ => .inl ⟨s, mem_edgesOf_iff.mp hs⟩
    | ⟨⟨.setElem s j, hj⟩, hs⟩ => .inr ⟨⟨s, mem_edgesOf_iff.mp hs⟩, j, hj⟩
  invFun e := match e with
    | .inl s => ⟨rootEdge I s.val, mem_edgesOf_iff.mpr s.prop⟩
    | .inr ⟨s, j, hj⟩ => ⟨incidenceEdge I s.val j hj, mem_edgesOf_iff.mpr s.prop⟩
  left_inv := by
    rintro ⟨⟨e, _⟩, _⟩
    cases e <;> rfl
  right_inv := by
    rintro (⟨s, hs⟩ | ⟨⟨s, hs⟩, j, hj⟩) <;> rfl

private theorem card_edgesOf (I : X3CInstance) (X : Finset (Fin I.n)) :
    (edgesOf I X).card = 4 * X.card := by
  have he := Fintype.card_congr (edgeSetEquiv I X)
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe, card_coverIncidences] at he
  omega

private def coverTarget {I : X3CInstance} {X : Finset (Fin I.n)}
    (a : coverIncidences I X) : Fin (3 * I.h) := a.2.val

private theorem coverTarget_surj {I : X3CInstance} {X : Finset (Fin I.n)}
    (hX : I.IsExactCover X) : Function.Surjective (coverTarget (I := I) (X := X)) := by
  intro j
  have hmem : j ∈ X.biUnion I.S := hX.2.symm ▸ Finset.mem_univ j
  obtain ⟨s, hs, hj⟩ := Finset.mem_biUnion.mp hmem
  exact ⟨⟨⟨s, hs⟩, j, hj⟩, rfl⟩

private theorem coverTarget_inj {I : X3CInstance} {X : Finset (Fin I.n)}
    (hX : I.IsExactCover X) : Function.Injective (coverTarget (I := I) (X := X)) := by
  have hc : Fintype.card (coverIncidences I X) = Fintype.card (Fin (3 * I.h)) := by
    rw [card_coverIncidences, hX.1, Fintype.card_fin]
  exact (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hc)).mpr
    (coverTarget_surj hX)

private theorem mem_marked_iff {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (p : Fin (4 * I.n)) :
    p ∈ marked hI σ ↔ (∃ j, lastPosition hI σ j = p) ∨
      (∃ s, σ.symm (rootEdge I s) = p) := by
  simp only [marked, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j | s, h⟩
    · exact Or.inl ⟨j, h⟩
    · exact Or.inr ⟨s, h⟩
  · rintro (⟨j, h⟩ | ⟨s, h⟩)
    · exact ⟨Sum.inl j, h⟩
    · exact ⟨Sum.inr s, h⟩

private theorem Ccount_eq_index_iff {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (i : ℕ) (hi : i ≤ 4 * I.n) :
    Ccount σ i = i ↔ suffix I i ⊆ marked hI σ := by
  classical
  rw [Ccount_eq_marked hI σ i hi]
  conv_lhs => rhs; rw [← suffix_card i hi]
  exact Finset.card_filter_eq_iff

private theorem omegaXC_iff_suffix {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) (X : Finset (Fin I.n)) :
    σ ∈ omegaXC I X ↔ σ ∈ omegaLE I ∧
      (suffix I (4 * I.h)).image σ = edgesOf I X := by
  classical
  have he : ((Finset.univ : Finset (Fin (4 * I.n))).filter
      (fun p => 4 * I.n - 4 * I.h ≤ p.val)) = suffix I (4 * I.h) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_suffix]
    have hhn := hI.2
    omega
  rw [omegaXC, Finset.mem_filter, he]

private theorem mem_image_suffix_iff {I : X3CInstance}
    (σ : Fin (4 * I.n) ≃ OrigEdge I) {i : ℕ} {e : OrigEdge I} :
    e ∈ (suffix I i).image σ ↔ σ.symm e ∈ suffix I i := by
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
    simpa only [Equiv.symm_apply_apply] using hp
  · intro h
    exact Finset.mem_image.mpr ⟨σ.symm e, h, σ.apply_symm_apply e⟩

private theorem marked_on_cover_suffix {I : X3CInstance} (hI : I.Standing)
    (σ : Fin (4 * I.n) ≃ OrigEdge I) {X : Finset (Fin I.n)} (hX : I.IsExactCover X)
    (hTail : (suffix I (4 * I.h)).image σ = edgesOf I X) :
    suffix I (4 * I.h) ⊆ marked hI σ := by
  intro p hp
  have hpEdge : (σ p).setIdx ∈ X := by
    apply mem_edgesOf_iff.mp
    rw [← hTail]
    exact Finset.mem_image_of_mem σ hp
  apply (mem_marked_iff ..).mpr
  cases he : (σ p).val with
  | rootSet s =>
    exact Or.inr ⟨s, ((rootPosition_iff σ p s).mpr he).symm⟩
  | setElem s j =>
    apply Or.inl
    refine ⟨j, ?_⟩
    have hle : p.val ≤ (lastPosition hI σ j).val := le_lastPosition hI σ j ⟨s, he⟩
    have hlast : lastPosition hI σ j ∈ suffix I (4 * I.h) := by
      rw [mem_suffix] at hp ⊢
      omega
    have hlastEdge : (σ (lastPosition hI σ j)).setIdx ∈ X := by
      apply mem_edgesOf_iff.mp
      rw [← hTail]
      exact Finset.mem_image_of_mem σ hlast
    obtain ⟨t, ht⟩ := lastPosition_spec hI σ j
    have hs : s ∈ X := by simpa only [OrigEdge.setIdx, he] using hpEdge
    have htX : t ∈ X := by simpa only [OrigEdge.setIdx, ht] using hlastEdge
    have hsj := (σ p).prop
    have htj := (σ (lastPosition hI σ j)).prop
    rw [he] at hsj
    rw [ht] at htj
    have hs_eq : s = t := by
      have heq : (⟨⟨s, hs⟩, j, hsj⟩ : coverIncidences I X) = ⟨⟨t, htX⟩, j, htj⟩ :=
        coverTarget_inj hX (show coverTarget _ = coverTarget _ from rfl)
      exact congrArg (fun a : coverIncidences I X => a.1.val) heq
    exact σ.injective (Subtype.ext (ht.trans (by simpa only [hs_eq] using he.symm)))

/-- The edge immediately before the exact-cover suffix cannot be the last incidence into
a universe element. It also cannot be a set-root edge, since each of that set’s incidences
would then lie inside the suffix. -/
private theorem unmarked_before_cover_suffix {I : X3CInstance} (hI : I.Standing)
    {σ : Fin (4 * I.n) ≃ OrigEdge I} (hσ : σ ∈ omegaLE I)
    {X : Finset (Fin I.n)} (hX : I.IsExactCover X)
    (hTail : (suffix I (4 * I.h)).image σ = edgesOf I X) :
    ∃ p ∈ suffix I (4 * I.h + 1), p ∉ marked hI σ := by
  have hhn := hI.2
  let p : Fin (4 * I.n) := ⟨4 * I.n - (4 * I.h + 1), by omega⟩
  have hpBefore : p ∉ suffix I (4 * I.h) := by rw [mem_suffix]; dsimp [p]; omega
  refine ⟨p, (mem_suffix ..).mpr (by dsimp [p]; omega), ?_⟩
  intro hmark
  rcases (mem_marked_iff ..).mp hmark with ⟨j, hj⟩ | ⟨s, hs⟩
  · have hcover : j ∈ X.biUnion I.S := hX.2.symm ▸ Finset.mem_univ j
    obtain ⟨s, hsX, hsj⟩ := Finset.mem_biUnion.mp hcover
    let e := incidenceEdge I s j hsj
    have he : e ∈ edgesOf I X := mem_edgesOf_iff.mpr hsX
    rw [← hTail] at he
    have heSuffix := (mem_image_suffix_iff σ).mp he
    have hle : (σ.symm e).val ≤ p.val := by
      rw [← hj]
      exact le_lastPosition hI σ j ⟨s, by rw [Equiv.apply_symm_apply]; rfl⟩
    apply hpBefore
    rw [mem_suffix] at heSuffix ⊢
    omega
  · have hsNot : s ∉ X := by
      intro hsX
      have hr : rootEdge I s ∈ edgesOf I X := mem_edgesOf_iff.mpr hsX
      rw [← hTail] at hr
      exact hpBefore (hs ▸ (mem_image_suffix_iff σ).mp hr)
    have hS : (I.S s).Nonempty := Finset.card_pos.mp (by rw [I.card_S]; decide)
    obtain ⟨j, hsj⟩ := hS
    let e := incidenceEdge I s j hsj
    have hlt : p.val < (σ.symm e).val := by
      rw [← hs]
      exact root_before_incidence hσ hsj
    have he : σ.symm e ∈ suffix I (4 * I.h) := by
      rw [mem_suffix]
      dsimp [p] at hlt
      omega
    have ho := (mem_image_suffix_iff σ).mpr he
    rw [hTail] at ho
    exact hsNot (mem_edgesOf_iff.mp ho)

/-- If every position in the suffix is marked, the set roots in the suffix and all their
incidences exhaust its positions. Their targets exhaust the universe. -/
private theorem exactCover_of_saturated_suffix {I : X3CInstance} (hI : I.Standing)
    {σ : Fin (4 * I.n) ≃ OrigEdge I} (hσ : σ ∈ omegaLE I)
    (heq : Ccount σ (4 * I.h) = 4 * I.h) :
    ∃ X ∈ I.exactCovers, σ ∈ omegaXC I X := by
  classical
  let X := suffixRoots σ (4 * I.h)
  let Y := suffixTargets hI σ (4 * I.h)
  have hhn := hI.2
  have hh : 4 * I.h ≤ 4 * I.n := by omega
  have hSub : edgesOf I X ⊆ (suffix I (4 * I.h)).image σ := by
    intro e he
    have hs : e.setIdx ∈ X := mem_edgesOf_iff.mp he
    apply (mem_image_suffix_iff σ).mpr
    rcases e with ⟨e, hv⟩
    cases e with
    | rootSet s => exact (mem_suffixRoots ..).mp hs
    | setElem s j =>
      have hroot := (mem_suffixRoots σ (4 * I.h) s).mp hs
      have hlt : (σ.symm (rootEdge I s)).val < (σ.symm (incidenceEdge I s j hv)).val :=
        root_before_incidence hσ hv
      rw [mem_suffix] at hroot ⊢
      change 4 * I.n ≤ (σ.symm (incidenceEdge I s j hv)).val + 4 * I.h
      omega
  have hcardTail : ((suffix I (4 * I.h)).image σ).card = 4 * I.h := by
    rw [Finset.card_image_of_injective _ σ.injective, suffix_card _ hh]
  have hXle : 4 * X.card ≤ 4 * I.h := by
    simpa only [card_edgesOf, hcardTail] using Finset.card_le_card hSub
  have hBoth : Y.card + X.card = 4 * I.h := (Ccount_split hI σ _ hh).symm.trans heq
  have hYle : Y.card ≤ 3 * I.h := by simpa using Finset.card_le_univ Y
  have hXcard : X.card = I.h := by omega
  have hYcard : Y.card = 3 * I.h := by omega
  have hYall : Y = Finset.univ := Y.eq_univ_of_card (by simpa using hYcard)
  have hTail := (Finset.eq_of_subset_of_card_le hSub (by
    rw [hcardTail, card_edgesOf, hXcard])).symm
  have hcover : I.IsExactCover X := by
    refine ⟨hXcard, Finset.eq_univ_iff_forall.mpr fun j => ?_⟩
    have hj : j ∈ Y := hYall.symm ▸ Finset.mem_univ j
    obtain ⟨p, hp, s, hs⟩ := (suffix_target_iff_exists hI σ _ j).mp hj
    have he : σ p ∈ edgesOf I X := hTail ▸ Finset.mem_image_of_mem σ hp
    have hidx := mem_edgesOf_iff.mp he
    have hv := (σ p).prop
    rw [hs] at hv
    exact Finset.mem_biUnion.mpr ⟨s, by simpa only [OrigEdge.setIdx, hs] using hidx, hv⟩
  refine ⟨X, ?_, (omegaXC_iff_suffix hI σ X).mpr ⟨hσ, hTail⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ X, hcover⟩

private theorem h_pos_of_standing {I : X3CInstance} (hI : I.Standing) : 0 < I.h := by
  let s : Fin I.n := ⟨0, Nat.zero_lt_of_lt hI.2⟩
  have hle : (I.S s).card ≤ 3 * I.h := by simpa using Finset.card_le_univ (I.S s)
  rw [I.card_S] at hle
  omega

end CountOrderings.NFree

open CountOrderings.NFree in
theorem solution (I : X3CInstance) (hI : I.Standing) (σ : Fin (4 * I.n) ≃ OrigEdge I)
    (hσ : σ ∈ omegaLE I) :
    (∀ X ∈ I.exactCovers, σ ∈ omegaXC I X →
        (∀ i ∈ Finset.Icc 1 (4 * I.h), Ccount σ i = i) ∧
          ∀ i ∈ Finset.Icc (4 * I.h + 1) (4 * I.n), Ccount σ i < i) ∧
      ((¬ ∃ X ∈ I.exactCovers, σ ∈ omegaXC I X) →
        ((Finset.Icc 1 (4 * I.h)).filter (fun i => Ccount σ i < i)).Nonempty) := by
  classical
  have hhn := hI.2
  constructor
  · intro X hX hσX
    have heX : I.IsExactCover X := (Finset.mem_filter.mp hX).2
    have hTail := ((omegaXC_iff_suffix hI σ X).mp hσX).2
    have hMarked := marked_on_cover_suffix hI σ heX hTail
    obtain ⟨p, hp, hpm⟩ := unmarked_before_cover_suffix hI hσ heX hTail
    constructor
    · intro i hi
      have hi' := Finset.mem_Icc.mp hi
      apply (Ccount_eq_index_iff hI σ i (by omega)).mpr
      intro a ha
      apply hMarked
      rw [mem_suffix] at ha ⊢
      omega
    · intro i hi
      have hi' := Finset.mem_Icc.mp hi
      refine lt_of_le_of_ne (Ccount_le_index hI σ i hi'.2) fun he => ?_
      apply hpm
      apply (Ccount_eq_index_iff hI σ i hi'.2).mp he
      rw [mem_suffix] at hp ⊢
      omega
  · intro hnone
    have hhi : 4 * I.h ≤ 4 * I.n := by omega
    have hhle : 1 ≤ 4 * I.h := by have := h_pos_of_standing hI; omega
    have hlt : Ccount σ (4 * I.h) < 4 * I.h :=
      lt_of_le_of_ne (Ccount_le_index hI σ _ hhi) fun he =>
        hnone (exactCover_of_saturated_suffix hI hσ he)
    exact ⟨4 * I.h, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hhle, le_rfl⟩, hlt⟩⟩
