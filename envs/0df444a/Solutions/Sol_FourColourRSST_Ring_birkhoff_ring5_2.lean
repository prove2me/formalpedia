-- Prove2me | solution 2 for FourColourRSST.Ring.birkhoff_ring5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:54:44.471827+00:00
-- url     : https://prove2.me/submissions/04612474-610c-49bd-b4d1-d7c13e216ef2

import Mathlib
import Definitions.Def_FourColourRSST_Ring_Setting
import Theorems.Thm_FourColourRSST_Ring_claim_1
import Theorems.Thm_FourColourRSST_Ring_claim_2

-- carved verbatim out of submission 8e9243b1-7569-477b-a62a-7dbd345abc2a, lines 590-597

section
open FourColourRSST
open FourColourRSST.Ring

lemma fits_perm_fixed {k : ℕ} {θ : SignType} {κ : EdgeColouring k}
    {M : Set (SignedMatch k)} (h : Fits θ κ M) (σ : Equiv.Perm SignType)
    (hσ : σ θ = θ) : Fits θ (fun e => σ (κ e)) M := by
  constructor
  · rw [h.1]
    ext e
    change (κ e ≠ θ) ↔ (σ (κ e) ≠ θ)
    simpa only [hσ] using (σ.injective.ne_iff (x := κ e) (y := θ)).symm
  · intro p hp e f hef
    rw [σ.injective.eq_iff]
    exact h.2 p hp e f hef

lemma swap_mem {k : ℕ} [NeZero k] {C : Set (EdgeColouring k)}
    (hC : Consistent C) {κ : EdgeColouring k} (hκ : κ ∈ C) (a b : SignType) :
    (fun e => Equiv.swap a b (κ e)) ∈ C := by
  have hex : ∀ a b : SignType, ∃ θ : SignType, θ ≠ a ∧ θ ≠ b := by decide
  obtain ⟨θ, hθa, hθb⟩ := hex a b
  obtain ⟨M, _, hfit, hclosed⟩ := hC κ hκ θ
  exact hclosed _ (fits_perm_fixed hfit (Equiv.swap a b)
    (Equiv.swap_apply_of_ne_of_ne hθa hθb))

lemma perm_mem {k : ℕ} [NeZero k] {C : Set (EdgeColouring k)}
    (hC : Consistent C) {κ : EdgeColouring k} (hκ : κ ∈ C)
    (σ : Equiv.Perm SignType) : (fun e => σ (κ e)) ∈ C := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simpa using hκ
  | swap_mul σ a b _ ih => exact swap_mem hC ih a b

lemma eqClass_subset_of_mem {k : ℕ} [NeZero k] {C : Set (EdgeColouring k)}
    (hC : Consistent C) {κ : EdgeColouring k} (hκ : κ ∈ C) : eqClass κ ⊆ C := by
  rintro κ' ⟨σ, hσ⟩
  have heq : κ' = fun e => σ (κ e) := funext hσ
  rw [heq]
  exact perm_mem hC hκ σ

lemma mem_eqClass_self {k : ℕ} (κ : EdgeColouring k) : κ ∈ eqClass κ :=
  ⟨Equiv.refl _, fun _ => rfl⟩

lemma base5_mem (i j : Fin 5) : base5 i j ∈ A i j := mem_eqClass_self _

lemma base5_subset_iff {C : Set (EdgeColouring 5)} (hC : Consistent C)
    (i j : Fin 5) : A i j ⊆ C ↔ base5 i j ∈ C := by
  constructor
  · exact fun h => h (base5_mem i j)
  · exact fun h => eqClass_subset_of_mem hC h

lemma A_symm (i j : Fin 5) : A i j = A j i := by
  by_cases hij : i = j
  · subst j; rfl
  have hs (i j : Fin 5) (hij : i ≠ j) (e : Fin 5) :
      Equiv.swap (1 : SignType) (-1) (base5 i j e) = base5 j i e := by
    by_cases hei : e = i
    · subst e; simp [base5, hij]
    by_cases hej : e = j
    · subst e; simp [base5, Ne.symm hij]
    simp [base5, hei, hej, Equiv.swap_apply_of_ne_of_ne]
  have hincl (i j : Fin 5) (hij : i ≠ j) : A i j ⊆ A j i := by
    rintro κ ⟨σ, hσ⟩
    refine ⟨(Equiv.swap (1 : SignType) (-1)).trans σ, ?_⟩
    intro e
    change κ e = σ (Equiv.swap (1 : SignType) (-1) (base5 j i e))
    rw [hs j i (Ne.symm hij)]
    exact hσ e
  exact Set.Subset.antisymm (hincl i j hij) (hincl j i (Ne.symm hij))

private lemma rotation_adj_finite : ∀ i a b x y : Fin 5,
    (ringMinus s(a + i, b + i)).Adj (x + i) (y + i) ↔
      (ringMinus s(a, b)).Adj x y := by
  simp only [ringMinus, SimpleGraph.deleteEdges_adj, SimpleGraph.cycleGraph_adj,
    Set.mem_ofPred_eq, Sym2.mem_iff, edge, Sym2.eq]
  decide

noncomputable def rotateIndex (i : Fin 5) : Equiv.Perm (Fin 5) := Equiv.addRight i

def rotatePair (i : Fin 5) (p : Sym2 (Fin 5)) : Sym2 (Fin 5) :=
  p.map (fun e => e + i)

lemma rotatePair_mem (i : Fin 5) (p : Sym2 (Fin 5)) (e : Fin 5) :
    e + i ∈ rotatePair i p ↔ e ∈ p := by
  rw [rotatePair, Sym2.mem_map]
  simp only [add_left_inj, exists_eq_right]

noncomputable def rotateDeletedIso (i : Fin 5) (p : Sym2 (Fin 5)) :
    ringMinus p ≃g ringMinus (rotatePair i p) where
  toEquiv := rotateIndex i
  map_rel_iff' := by
    intro x y
    induction p using Sym2.ind with
    | _ a b => exact rotation_adj_finite i a b x y

lemma rotate_reachable (i : Fin 5) (p : Sym2 (Fin 5)) {e f : Fin 5}
    (h : (ringMinus p).Reachable e f) :
    (ringMinus (rotatePair i p)).Reachable (e+i) (f+i) :=
  h.map (rotateDeletedIso i p).toHom

def rotateColour (i : Fin 5) (κ : EdgeColouring 5) : EdgeColouring 5 :=
  fun e => κ (e - i)

def rotateSigned (i : Fin 5) (p : SignedMatch 5) : SignedMatch 5 :=
  (rotatePair i p.1, p.2)

def rotateMatching (i : Fin 5) (M : Set (SignedMatch 5)) : Set (SignedMatch 5) :=
  rotateSigned i '' M

lemma rotateColour_neg (i : Fin 5) (κ : EdgeColouring 5) :
    rotateColour (-i) (rotateColour i κ) = κ := by
  funext e
  simp [rotateColour]

lemma rotatePair_neg (i : Fin 5) (p : Sym2 (Fin 5)) :
    rotatePair (-i) (rotatePair i p) = p := by
  simp [rotatePair, Sym2.map_map]

lemma rotateMatching_neg (i : Fin 5) (M : Set (SignedMatch 5)) :
    rotateMatching (-i) (rotateMatching i M) = M := by
  rw [rotateMatching, rotateMatching, ← Set.image_comp]
  have h : (rotateSigned (-i)) ∘ (rotateSigned i) = id := by
    funext p
    simp [rotateSigned, rotatePair_neg]
  rw [h, Set.image_id]

lemma matching_rotate {M : Set (SignedMatch 5)} (hM : IsSignedMatching M)
    (i : Fin 5) : IsSignedMatching (rotateMatching i M) := by
  constructor
  · rintro p ⟨q, hq, rfl⟩
    change ¬(rotatePair i q.1).IsDiag
    intro hdiag
    apply hM.1 q hq
    have h := hdiag.map (f := fun e : Fin 5 => e - i)
    simpa [rotatePair, Sym2.map_map, Function.comp_def] using h
  · rintro p ⟨p', hp', rfl⟩ q ⟨q', hq', rfl⟩ hne
    have hpq : p' ≠ q' := fun h => hne (congrArg (rotateSigned i) h)
    obtain ⟨hdis, hreach⟩ := hM.2 p' hp' q' hq' hpq
    constructor
    · intro e he hqe
      obtain ⟨a, ha, rfl⟩ := Sym2.mem_map.mp he
      exact hdis a ha ((rotatePair_mem i q'.1 a).mp hqe)
    · intro e he f hf
      obtain ⟨a, ha, rfl⟩ := Sym2.mem_map.mp he
      obtain ⟨b, hb, rfl⟩ := Sym2.mem_map.mp hf
      exact rotate_reachable i q'.1 (hreach a ha b hb)

lemma fits_rotate {θ : SignType} {κ : EdgeColouring 5} {M : Set (SignedMatch 5)}
    (h : Fits θ κ M) (i : Fin 5) :
    Fits θ (rotateColour i κ) (rotateMatching i M) := by
  constructor
  · ext e
    change (∃ p ∈ rotateMatching i M, e ∈ p.1) ↔ κ (e-i) ≠ θ
    constructor
    · rintro ⟨p, ⟨q, hq, rfl⟩, he⟩
      have he' : e-i ∈ q.1 := (rotatePair_mem i q.1 (e-i)).mp (by simpa [rotateSigned] using he)
      have : e-i ∈ edgesOf M := ⟨q,hq,he'⟩
      rwa [h.1] at this
    · intro he
      have : e-i ∈ edgesOf M := by rwa [h.1]
      obtain ⟨p,hp,hep⟩ := this
      refine ⟨rotateSigned i p, ⟨p,hp,rfl⟩, ?_⟩
      simpa [rotateSigned] using (rotatePair_mem i p.1 (e-i)).mpr hep
  · rintro p ⟨q,hq,rfl⟩ e f hef
    have heq : q.1 = s(e-i,f-i) := by
      have hh := congrArg (Sym2.map (fun a : Fin 5 => a-i)) hef
      simpa [rotateSigned, rotatePair, Sym2.map_map, Function.comp_def] using hh
    exact h.2 q hq (e-i) (f-i) heq

lemma consistent_rotate {C : Set (EdgeColouring 5)} (hC : Consistent C) (i : Fin 5) :
    Consistent (rotateColour i '' C) := by
  rintro κ ⟨κ₀,hκ₀,rfl⟩ θ
  obtain ⟨M,hM,hfit,hclosed⟩ := hC κ₀ hκ₀ θ
  refine ⟨rotateMatching i M, matching_rotate hM i, fits_rotate hfit i, ?_⟩
  intro κ' hκ'
  have hinv := fits_rotate hκ' (-i)
  rw [rotateMatching_neg] at hinv
  refine ⟨rotateColour (-i) κ', hclosed _ hinv, ?_⟩
  simpa using rotateColour_neg (-i) κ'

lemma rotate_mem_A_iff (i a b : Fin 5) (κ : EdgeColouring 5) :
    rotateColour i κ ∈ A (a+i) (b+i) ↔ κ ∈ A a b := by
  constructor
  · rintro ⟨σ,hσ⟩
    refine ⟨σ,fun e => ?_⟩
    simpa [rotateColour, base5] using hσ (e+i)
  · rintro ⟨σ,hσ⟩
    refine ⟨σ,fun e => ?_⟩
    simpa [rotateColour, base5, sub_eq_iff_eq_add] using hσ (e-i)

lemma rotate_A (i a b : Fin 5) : rotateColour i '' A a b = A (a+i) (b+i) := by
  ext κ
  constructor
  · rintro ⟨κ₀,hκ₀,rfl⟩
    exact (rotate_mem_A_iff i a b κ₀).mpr hκ₀
  · intro hκ
    refine ⟨rotateColour (-i) κ, ?_, ?_⟩
    · have h := (rotate_mem_A_iff (-i) (a+i) (b+i) κ).mpr hκ
      simpa using h
    · simpa using rotateColour_neg (-i) κ

lemma rotate_subset_iff (i : Fin 5) (S C : Set (EdgeColouring 5)) :
    rotateColour i '' S ⊆ rotateColour i '' C ↔ S ⊆ C := by
  constructor
  · intro h κ hκ
    obtain ⟨κ₀,hκ₀,heq⟩ := h ⟨κ,hκ,rfl⟩
    have := congrArg (rotateColour (-i)) heq
    simp only [rotateColour_neg] at this
    exact this ▸ hκ₀
  · exact Set.image_mono

lemma A_subset_rotated_iff (i a b : Fin 5) (C : Set (EdgeColouring 5)) :
    A a b ⊆ rotateColour (-i) '' C ↔ A (a+i) (b+i) ⊆ C := by
  rw [← rotate_subset_iff i (A a b) (rotateColour (-i) '' C), rotate_A]
  have h : rotateColour i '' (rotateColour (-i) '' C) = C := by
    rw [← Set.image_comp]
    have hf : rotateColour i ∘ rotateColour (-i) = id := by
      funext κ
      simpa using rotateColour_neg (-i) κ
    rw [hf, Set.image_id]
  rw [h]

lemma claim_one (C : Set (EdgeColouring 5)) (hC : Consistent C)
    (i : Fin 5) (h01 : A i (i+1) ⊆ C) :
    (A i (i+2) ⊆ C ∨ A i (i+4) ⊆ C) ∧
    (A (i+1) (i+2) ⊆ C ∨ A (i+1) (i+4) ⊆ C) := by
  have hbase : A 0 1 ⊆ rotateColour (-i) '' C := by
    rw [A_subset_rotated_iff]
    simpa [add_comm] using h01
  have h := FourColourRSST.Ring.claim_1 _ (consistent_rotate hC (-i)) hbase
  simpa only [A_subset_rotated_iff, zero_add, add_comm, add_zero] using h

lemma claim_two (C : Set (EdgeColouring 5)) (hC : Consistent C)
    (i : Fin 5) (h02 : A i (i+2) ⊆ C) :
    A (i+1) (i+2) ⊆ C ∨ A (i+2) (i+4) ⊆ C := by
  have hbase : A 0 2 ⊆ rotateColour (-i) '' C := by
    rw [A_subset_rotated_iff]
    simpa [add_comm] using h02
  have h := FourColourRSST.Ring.claim_2 _ (consistent_rotate hC (-i)) hbase
  simpa only [A_subset_rotated_iff, add_comm] using h

lemma cyclic_boundary (P : Fin 5 → Prop) (hyes : ∃ i, P i) (hno : ¬ ∀ i, P i) :
    ∃ i, P i ∧ ¬ P (i+1) := by
  by_contra! h
  obtain ⟨i, hi⟩ := hyes
  have h1 := h i hi
  have h2 : P (i+2) := by simpa [add_assoc] using h (i+1) h1
  have h3 : P (i+3) := by simpa [add_assoc] using h (i+2) h2
  have h4 : P (i+4) := by simpa [add_assoc] using h (i+3) h3
  apply hno
  intro j
  have hex : ∀ i j : Fin 5, j=i ∨ j=i+1 ∨ j=i+2 ∨ j=i+3 ∨ j=i+4 := by decide
  rcases hex i j with rfl | rfl | rfl | rfl | rfl <;> assumption

lemma class_subset_of_inter {C : Set (EdgeColouring 5)} (hC : Consistent C)
    {i j : Fin 5} {κ : EdgeColouring 5} (hκ : κ ∈ C) (hA : κ ∈ A i j) :
    A i j ⊆ C := by
  obtain ⟨σ,hσ⟩ := hA
  apply (base5_subset_iff hC i j).mpr
  have hh := perm_mem hC hκ σ.symm
  have heq : (fun e => σ.symm (κ e)) = base5 i j := by
    funext e
    rw [hσ e, σ.symm_apply_apply]
  rwa [heq] at hh

lemma adjacent_class_exists {C : Set (EdgeColouring 5)} (hC : Consistent C)
    (hmeet : (C ∩ E5).Nonempty) : ∃ i : Fin 5, A i (i+1) ⊆ C := by
  obtain ⟨κ,hκ,hE⟩ := hmeet
  rcases hE with (((h01 | h12) | h23) | h34) | h04
  · exact ⟨0, class_subset_of_inter hC hκ h01⟩
  · exact ⟨1, class_subset_of_inter hC hκ h12⟩
  · exact ⟨2, class_subset_of_inter hC hκ h23⟩
  · exact ⟨3, class_subset_of_inter hC hκ h34⟩
  · refine ⟨4, ?_⟩
    rw [show (4 : Fin 5)+1=0 by decide, A_symm]
    exact class_subset_of_inter hC hκ h04

lemma E5_subset_of_adjacent {C : Set (EdgeColouring 5)}
    (h : ∀ i : Fin 5, A i (i+1) ⊆ C) : E5 ⊆ C := by
  intro κ hκ
  rcases hκ with (((h01 | h12) | h23) | h34) | h04
  · exact h 0 h01
  · exact h 1 h12
  · exact h 2 h23
  · exact h 3 h34
  · have hh := h 4
    rw [show (4 : Fin 5)+1=0 by decide, A_symm] at hh
    exact hh h04

lemma C5_of_three {C : Set (EdgeColouring 5)} (i : Fin 5)
    (h01 : A i (i+1) ⊆ C) (h04 : A i (i+4) ⊆ C)
    (h14 : A (i+1) (i+4) ⊆ C) : C5 i ⊆ C := by
  have heq : i-1=i+4 := by fin_cases i <;> decide
  rw [C5, heq, A_symm (i+4) (i+1)]
  exact Set.union_subset (Set.union_subset h04 h01) h14

lemma D5_of_four {C : Set (EdgeColouring 5)} (i : Fin 5)
    (h01 : A i (i+1) ⊆ C) (h02 : A i (i+2) ⊆ C)
    (h14 : A (i+1) (i+4) ⊆ C) (h24 : A (i+2) (i+4) ⊆ C) :
    D5 (i+3) ⊆ C := by
  have h31 : (3 : Fin 5)+1=4 := by decide
  have h32 : (3 : Fin 5)+2=0 := by decide
  have h33 : (3 : Fin 5)+3=1 := by decide
  have h34 : (3 : Fin 5)+4=2 := by decide
  simp only [D5, add_assoc, h31, h32, h33, h34, add_zero]
  rw [A_symm (i+4) (i+1), A_symm (i+4) (i+2)]
  exact Set.union_subset (Set.union_subset (Set.union_subset h14 h24) h01) h02

lemma ring5_conclusion (C : Set (EdgeColouring 5)) (hC : Consistent C)
    (hmeet : (C ∩ E5).Nonempty) :
    (∃ i, C5 i ⊆ C) ∨ (∃ i, D5 i ⊆ C) ∨ E5 ⊆ C := by
  by_cases hE : ∀ i : Fin 5, A i (i+1) ⊆ C
  · exact Or.inr (Or.inr (E5_subset_of_adjacent hE))
  obtain ⟨i,h01,h12⟩ := cyclic_boundary (fun i => A i (i+1) ⊆ C)
    (adjacent_class_exists hC hmeet) hE
  have h12' : ¬ A (i+1) (i+2) ⊆ C := by simpa [add_assoc] using h12
  obtain ⟨hleft,hright⟩ := claim_one C hC i h01
  have h14 := hright.resolve_left h12'
  by_cases h04 : A i (i+4) ⊆ C
  · exact Or.inl ⟨i, C5_of_three i h01 h04 h14⟩
  have h02 := hleft.resolve_right h04
  have h24 := (claim_two C hC i h02).resolve_left h12'
  exact Or.inr (Or.inl ⟨i+3, D5_of_four i h01 h02 h14 h24⟩)

theorem birkhoff_ring5 (C : Set (EdgeColouring 5)) (hC : Consistent C)
    (hne : C.Nonempty) (hmeet : (C ∩ E5).Nonempty) :
    (∃ i, C5 i ⊆ C) ∨ (∃ i, D5 i ⊆ C) ∨ E5 ⊆ C := by
  have _nonempty := hne
  exact ring5_conclusion C hC hmeet

end

section
open FourColourRSST.Ring

theorem solution (C : Set (EdgeColouring 5)) (hC : Consistent C)
    (hne : C.Nonempty) (hmeet : (C ∩ E5).Nonempty) :
    (∃ i, C5 i ⊆ C) ∨ (∃ i, D5 i ⊆ C) ∨ E5 ⊆ C := by
  exact birkhoff_ring5 C hC hne hmeet

end
