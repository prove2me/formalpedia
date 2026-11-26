-- Prove2me | solution 1 for FixedMachinePrec.generateFamily_extensional
-- status  : ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T12:36:21.918935+00:00
-- url     : https://prove2.me/submissions/372e964c-e7e0-47e1-a7d0-d6c2d6332e26

import Definitions.Def_FixedMachinePrec_GenerateFamily

open FixedMachinePrec

private theorem subsets_spec {N m : ℕ} (A : Finset (Fin N)) : A ∈ mSubsetsLex N m ↔ A.card = m := by
  classical
  simp only [mSubsetsLex, List.mem_map, List.mem_mergeSort, List.mem_sublistsLen]
  constructor
  · rintro ⟨l,⟨hsub,hlen⟩,rfl⟩
    rw [List.toFinset_card_of_nodup ((List.nodup_finRange N).sublist hsub), hlen]
  · intro h
    let l := (List.finRange N).filter (fun x => decide (x ∈ A))
    have he : l.toFinset = A := by ext x; simp [l]
    have hd : l.Nodup := (List.nodup_finRange N).filter _
    exact ⟨l,⟨List.filter_sublist,by rwa [← List.toFinset_card_of_nodup hd, he]⟩,he⟩

section
variable {N : ℕ} (p : Fin N → Fin N → Prop) [DecidableRel p] (r : Fin N → ℕ) (m : ℕ)

private theorem atoms_spec (X : Finset (Fin N)) : X ∈ atomList p r m ↔
    ∃ a : Atom N, a.Valid m ∧ a.eval p r = X := by
  simp only [atomList,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map,
    List.mem_range,List.mem_flatMap,subsets_spec]
  constructor
  · rintro (((rfl | rfl) | ⟨i, hi, rfl⟩) | ⟨A,hA,ha⟩)
    · exact ⟨.univ,trivial,rfl⟩
    · exact ⟨.empty,trivial,rfl⟩
    · exact ⟨.rankSuffix (i+1),⟨by omega,by omega⟩,rfl⟩
    · rcases ha with rfl | rfl | rfl | rfl | rfl
      · exact ⟨.boundary _,hA,rfl⟩
      · exact ⟨.pred _,hA,rfl⟩
      · exact ⟨.succ _,hA,rfl⟩
      · exact ⟨.weakPred _,hA,rfl⟩
      · exact ⟨.weakSucc _,hA,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    cases a with
    | univ => exact Or.inl (Or.inl (Or.inl rfl))
    | empty => exact Or.inl (Or.inl (Or.inr rfl))
    | rankSuffix h =>
      obtain ⟨lo,hi⟩ := ha
      exact Or.inl (Or.inr ⟨h-1,by omega, by simp [Atom.eval, Nat.sub_add_cancel lo]⟩)
    | boundary A | pred A | succ A | weakPred A | weakSucc A =>
      right; exact ⟨A,ha,by simp [Atom.eval]⟩

private theorem fold_mem {α β : Type*} (X : α) (f : List α → β → List α) (P : β → Prop)
    (hf : ∀ b a, X ∈ f b a ↔ X ∈ b ∨ P a) (l : List β) (b : List α) :
    X ∈ l.foldl f b ↔ X ∈ b ∨ ∃ a ∈ l, P a := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp only [List.foldl_cons,ih,hf,List.mem_cons]; grind

private theorem insert_mem (U V : Finset (Fin N)) (l : List (Finset (Fin N))) :
    U ∈ insertNew l V ↔ U ∈ l ∨ U = V := by unfold insertNew; split <;> simp_all

private theorem first_layer_mem (X : Finset (Fin N)) : X ∈ layerOne p r m ↔
    ∃ a : Atom N, a.Valid m ∧ (X = a.eval p r ∨ X = Finset.univ \ a.eval p r) := by
  unfold layerOne
  rw [fold_mem X _ (fun A => X = A ∨ X = Finset.univ \ A) (by intros; simp only [insert_mem]; tauto)]
  simp only [List.not_mem_nil,false_or,atoms_spec]
  grind

private theorem next_mem (layers : List (List (Finset (Fin N)))) (X : Finset (Fin N)) : X ∈ nextLayer layers ↔
    X ∈ layers.getD (layers.length-1) [] ∨ ∃ i < layers.length, ∃ A ∈ layers.getD i [],
      ∃ B ∈ layers.getD (layers.length-1-i) [], X = A ∪ B ∨ X = A ∩ B := by
  unfold nextLayer
  dsimp only
  rw [fold_mem X _ (fun i => ∃ A ∈ layers.getD i [], ∃ B ∈ layers.getD (layers.length-1-i) [], X = A ∪ B ∨ X = A ∩ B)]
  · simp
  · intro b i
    apply fold_mem
    intro b A
    apply fold_mem
    intro b B
    simp only [insert_mem]; tauto

private theorem leaves_pos (φ : Formula N) : 0 < φ.leaves := by
  induction φ <;> simp_all [Formula.leaves]

-- Strip leading complements. Pushing one past a binary root preserves the leaf budget.
private theorem head_form (φ : Formula N) (hv : φ.Valid m) :
    (∃ a : Atom N, a.Valid m ∧ (φ.eval p r = a.eval p r ∨ φ.eval p r = Finset.univ \ a.eval p r)) ∨
    ∃ u v : Formula N, u.Valid m ∧ v.Valid m ∧ u.leaves + v.leaves = φ.leaves ∧
      (φ.eval p r = u.eval p r ∪ v.eval p r ∨ φ.eval p r = u.eval p r ∩ v.eval p r) := by
  induction φ with
  | atom a => exact Or.inl ⟨a,hv,Or.inl rfl⟩
  | union u v _ _ => exact Or.inr ⟨u,v,hv.1,hv.2,rfl,Or.inl rfl⟩
  | inter u v _ _ => exact Or.inr ⟨u,v,hv.1,hv.2,rfl,Or.inr rfl⟩
  | compl φ ih =>
    rcases ih hv with ⟨a,ha,he | he⟩ | ⟨u,v,hu,hv',hl,he | he⟩
    · exact Or.inl ⟨a,ha,Or.inr (by simp [Formula.eval,he])⟩
    · exact Or.inl ⟨a,ha,Or.inl (by ext; simp [Formula.eval,he])⟩
    · exact Or.inr ⟨u.compl,v.compl,hu,hv',hl,Or.inr (by ext; simp [Formula.eval,he])⟩
    · exact Or.inr ⟨u.compl,v.compl,hu,hv',hl,Or.inl (by ext; simp [Formula.eval,he]; tauto)⟩

private def RepresentableAt (k : ℕ) (X : Finset (Fin N)) : Prop :=
  ∃ φ : Formula N, φ.Valid m ∧ φ.leaves ≤ k ∧ φ.eval p r = X

private theorem literal_rep {X : Finset (Fin N)} {k : ℕ} (hk : 1 ≤ k) (a : Atom N) (ha : a.Valid m)
    (he : X = a.eval p r ∨ X = Finset.univ \ a.eval p r) : RepresentableAt p r m k X := by
  rcases he with rfl | rfl
  · exact ⟨.atom a,ha,hk,rfl⟩
  · exact ⟨(.atom a : Formula N).compl,ha,hk,rfl⟩

private theorem first_exact (X : Finset (Fin N)) : X ∈ layerOne p r m ↔ RepresentableAt p r m 1 X := by
  rw [first_layer_mem]; constructor
  · rintro ⟨a,h,he⟩; exact literal_rep p r m le_rfl a h he
  · rintro ⟨φ,hv,hl,rfl⟩
    rcases head_form p r m φ hv with ha | ⟨u,v,_,_,e,_⟩
    · exact ha
    · have := leaves_pos u; have := leaves_pos v; omega

private theorem next_exact (ls : List (List (Finset (Fin N)))) (n : ℕ) (hn : ls.length = n)
    (hp : 0 < n) (ih : ∀ i < n, ∀ X, X ∈ ls.getD i [] ↔ RepresentableAt p r m (i+1) X) (X) :
    X ∈ nextLayer ls ↔ RepresentableAt p r m (n+1) X := by
  rw [next_mem,hn]
  have hlast := ih (n-1) (by omega)
  have eq : n-1+1 = n := by omega
  rw [eq] at hlast
  constructor
  · rintro (hold | ⟨i,hi,A,hA,B,hB,he⟩)
    · obtain ⟨φ,hv,hl,he⟩ := (hlast X).mp hold
      exact ⟨φ,hv,by omega,he⟩
    · obtain ⟨u,hu,hlu,rfl⟩ := (ih i hi A).mp hA
      obtain ⟨v,hv,hlv,rfl⟩ := (ih _ (by omega) B).mp hB
      rcases he with rfl | rfl
      · exact ⟨.union u v,⟨hu,hv⟩,show u.leaves + v.leaves ≤ n+1 by omega,rfl⟩
      · exact ⟨.inter u v,⟨hu,hv⟩,show u.leaves + v.leaves ≤ n+1 by omega,rfl⟩
  · rintro ⟨φ,hv,hl,rfl⟩
    rcases head_form p r m φ hv with ⟨a,ha,he⟩ | ⟨u,v,hu,hv',hle,he⟩
    · exact Or.inl ((hlast _).mpr (literal_rep p r m hp a ha he))
    · have hpu := leaves_pos u; have hpv := leaves_pos v
      have hi : u.leaves-1 < n := by omega
      exact Or.inr ⟨_,hi,_,(ih _ hi _).mpr ⟨u,hu,by omega,rfl⟩,_,
        (ih _ (by omega) _).mpr ⟨v,hv',by omega,rfl⟩,he⟩

private theorem all_layers (k : ℕ) :
    let ls := genLayers p r m k
    ls.length = k ∧ ∀ i < k, ∀ X, X ∈ ls.getD i [] ↔ RepresentableAt p r m (i+1) X := by
  induction k with
  | zero => simp [genLayers]
  | succ k ih =>
    cases k with
    | zero =>
      refine ⟨rfl,?_⟩
      intro i hi X
      have : i = 0 := by omega
      subst i; exact first_exact p r m X
    | succ k =>
      let ls := genLayers p r m (k+1)
      obtain ⟨hlen, hs⟩ := ih
      change ls.length = k+1 at hlen
      change (ls ++ [nextLayer ls]).length = k+2 ∧ _
      refine ⟨by simp [hlen],?_⟩
      intro i hi X
      change X ∈ (ls ++ [nextLayer ls]).getD i [] ↔ _
      by_cases h : i < ls.length
      · simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left h] using hs i (by omega) X
      · have e : i = ls.length := by omega
        subst i
        simpa [List.getD_eq_getElem?_getD,List.getElem?_append_right,hlen] using next_exact p r m ls (k+1) hlen (by omega) hs X

end

theorem solution {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec] (rank : Fin N → ℕ) (k : ℕ) (hk : 1 ≤ k) : (generateFamily prec rank m k).toFinset = family prec rank m k := by
  classical
  ext X
  obtain ⟨_,hs⟩ := all_layers prec rank m k
  have h := hs (k-1) (by omega) X
  rw [Nat.sub_add_cancel hk] at h
  simpa [generateFamily,family,RepresentableAt] using h
