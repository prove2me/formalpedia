-- Prove2me | solution 1 for BergerSchwichtenberg1991V2.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T05:01:04.167287+00:00
-- url     : https://prove2.me/submissions/d43000fc-f0bd-424c-afab-1e2325e6e772

import Definitions.Def_BergerSchwichtenberg1991V2_Syntax

set_option autoImplicit false

open BergerSchwichtenberg1991V2

private def mapScope (k : Index) : List (Var × Index) → List (Var × Index)
  | [] => []
  | (x, q) :: rest => (indexedVar x.ty (k ++ q), q) :: mapScope k rest

private def ScopeBelow : List (Var × Index) → Nat → Prop
  | [], _ => True
  | (_, q) :: rest, n => q.length < n ∧ ScopeBelow rest q.length

private theorem scopeBelow_mono {scope : List (Var × Index)} {n m : Nat}
    (h : ScopeBelow scope n) (hnm : n ≤ m) : ScopeBelow scope m := by
  cases scope with
  | nil => trivial
  | cons xq rest =>
    cases xq with
    | mk x q => exact ⟨Nat.lt_of_lt_of_le h.1 hnm, h.2⟩

private theorem binderPath_mapScope_of_some (k : Index) {v : Var}
    {scope : List (Var × Index)} {q : Index} {n : Nat}
    (hscope : ScopeBelow scope n)
    (hb : binderPath v scope = some q) :
    q.length < n ∧ binderPath (indexedVar v.ty (k ++ q)) (mapScope k scope) = some q := by
  induction scope generalizing n with
  | nil => cases hb
  | cons xq rest ih =>
    cases xq with
    | mk x p₀ =>
      rcases hscope with ⟨hp₀, hrest⟩
      simp only [binderPath] at hb
      split at hb
      · next hvx =>
        injection hb with hq
        subst hvx
        subst hq
        refine ⟨hp₀, ?_⟩
        simp [mapScope, binderPath]
      · next hvx =>
        obtain ⟨hq_lt, hmap⟩ := ih hrest hb
        refine ⟨Nat.lt_trans hq_lt hp₀, ?_⟩
        have hne : indexedVar v.ty (k ++ q) ≠ indexedVar x.ty (k ++ p₀) := by
          intro heq
          injection heq with hname _
          injection hname with hidx
          have hlen : (k ++ q).length = (k ++ p₀).length := congrArg List.length hidx
          rw [List.length_append, List.length_append] at hlen
          omega
        simp only [mapScope, binderPath, hne, ite_false]
        exact hmap

private theorem binderPath_mapScope_of_not_prefix (k : Index) (v : Var)
    (scope : List (Var × Index))
    (hnot : ∀ m : Index, v.name = .indexed m → ¬ IsPrefixOf k m) :
    binderPath v (mapScope k scope) = none := by
  induction scope with
  | nil => rfl
  | cons xq rest ih =>
    cases xq with
    | mk x p₀ =>
      have hne : v ≠ indexedVar x.ty (k ++ p₀) := by
        intro heq
        have hname : v.name = .indexed (k ++ p₀) := by
          rw [heq]
          rfl
        exact hnot (k ++ p₀) hname ⟨p₀, rfl⟩
      simp only [mapScope, binderPath, hne, ite_false]
      exact ih

private theorem abstract_name_abstract (k : Index) (r : Term)
    (scope : List (Var × Index)) (p : Index)
    (hscope : ScopeBelow scope p.length)
    (hfree : ∀ v ∈ freeVarOccurrences r, binderPath v scope = none →
      ∀ m : Index, v.name = .indexed m → ¬ IsPrefixOf k m) :
    abstractBindings (mapScope k scope) p (nameBindings k p (abstractBindings scope p r)) =
      abstractBindings scope p r := by
  induction r generalizing scope p with
  | var v =>
    simp only [abstractBindings]
    cases hb : binderPath v scope with
    | none =>
      have hnot : ∀ m : Index, v.name = .indexed m → ¬ IsPrefixOf k m :=
        hfree v (by simp [freeVarOccurrences]) hb
      have hmap : binderPath v (mapScope k scope) = none :=
        binderPath_mapScope_of_not_prefix k v scope hnot
      simp only [nameBindings, abstractBindings, hmap]
    | some q =>
      have hmap : binderPath (indexedVar v.ty (k ++ q)) (mapScope k scope) = some q :=
        (binderPath_mapScope_of_some k hscope hb).2
      simp only [nameBindings, abstractBindings, hmap]
      rfl
  | app t s iht ihs =>
    have hlen0 : p.length ≤ (p ++ zeroIdx).length := by simp
    have hlen1 : p.length ≤ (p ++ oneIdx).length := by simp
    have ht := iht scope (p ++ zeroIdx) (scopeBelow_mono hscope hlen0) (fun v hv hb =>
      hfree v (List.mem_append_left _ hv) hb)
    have hs := ihs scope (p ++ oneIdx) (scopeBelow_mono hscope hlen1) (fun v hv hb =>
      hfree v (List.mem_append_right _ hv) hb)
    simp only [abstractBindings, nameBindings, ht, hs]
  | lam x body ih =>
    have hscope' : ScopeBelow ((x, p) :: scope) (p ++ zeroIdx).length := by
      refine ⟨?_, hscope⟩
      simp [zeroIdx]
    have hfree' : ∀ v ∈ freeVarOccurrences body, binderPath v ((x, p) :: scope) = none →
        ∀ m : Index, v.name = .indexed m → ¬ IsPrefixOf k m := by
      intro v hv hb
      simp only [binderPath] at hb
      split at hb
      · cases hb
      · next hvx =>
        apply hfree v _ hb
        rw [freeVarOccurrences, List.mem_filter]
        exact ⟨hv, by simpa using hvx⟩
    have hbody := ih ((x, p) :: scope) (p ++ zeroIdx) hscope' hfree'
    simp only [abstractBindings, nameBindings, mapScope] at hbody ⊢
    exact congrArg (BindingTerm.lam x.ty) hbody

private theorem alphaRename_alphaEq_of_not_prefix (k : Index) (r : Term)
    (h : ∀ m ∈ freeIndices r, ¬ IsPrefixOf k m) :
    AlphaEq (alphaRename k r) r := by
  apply abstract_name_abstract k r [] [] trivial
  intro v hv _ m hname
  have hv_free : v ∈ freeVars r := List.mem_eraseDups.2 hv
  have hm : m ∈ freeIndices r := by
    rw [freeIndices, List.mem_filterMap]
    exact ⟨v, hv_free, by rw [hname]⟩
  exact h m hm

private theorem mem_allVars_name_abstract {k : Index} {r : Term}
    {scope : List (Var × Index)} {p : Index} {v : Var}
    (hv : v ∈ freeVarOccurrences r) (hb : binderPath v scope = none) :
    v ∈ allVars (nameBindings k p (abstractBindings scope p r)) := by
  induction r generalizing scope p with
  | var x =>
    simp [freeVarOccurrences] at hv
    subst hv
    simp [abstractBindings, hb, nameBindings, allVars]
  | app t s iht ihs =>
    simp [freeVarOccurrences] at hv
    simp only [abstractBindings, nameBindings, allVars]
    cases hv with
    | inl hvt => exact List.mem_append_left _ (iht hvt hb)
    | inr hvs => exact List.mem_append_right _ (ihs hvs hb)
  | lam x body ih =>
    rw [freeVarOccurrences, List.mem_filter] at hv
    rcases hv with ⟨hv_body, hvx⟩
    have hvx' : v ≠ x := by simpa using hvx
    have hb' : binderPath v ((x, p) :: scope) = none := by
      simp [binderPath, hvx', hb]
    simp only [abstractBindings, nameBindings, allVars]
    exact List.Mem.tail _ (ih hv_body hb')

private theorem nat_le_max_left (a b : Nat) : a ≤ Nat.max a b := by
  change a ≤ if a ≤ b then b else a
  split <;> omega

private theorem nat_le_max_right (a b : Nat) : b ≤ Nat.max a b := by
  change b ≤ if a ≤ b then b else a
  split <;> omega

private theorem length_le_maxIdxLength {m : Index} {ls : List Index} (hm : m ∈ ls) :
    m.length ≤ maxIdxLength ls := by
  induction ls with
  | nil => cases hm
  | cons l rest ih =>
    simp only [maxIdxLength]
    cases hm with
    | head => exact nat_le_max_left _ _
    | tail _ hrest => exact Nat.le_trans (ih hrest) (nat_le_max_right _ _)

private theorem extract_emb_alphaEq (r : Term) : AlphaEq (EXTRACT (EMB r)) r := by
  apply alphaRename_alphaEq_of_not_prefix (canonicalFreshIndex (EMB r)) r
  intro m hm
  rw [freeIndices, List.mem_filterMap] at hm
  rcases hm with ⟨v, hv_free, hmatch⟩
  cases hname : v.name with
  | named _ =>
    rw [hname] at hmatch
    cases hmatch
  | indexed l =>
    rw [hname] at hmatch
    injection hmatch with hl
    subst l
    have hv_occ : v ∈ freeVarOccurrences r := List.mem_eraseDups.1 hv_free
    have hv_all : v ∈ allVars (EMB r epsIdx) :=
      mem_allVars_name_abstract hv_occ rfl
    have hm_all : m ∈ allIndices (EMB r epsIdx) := by
      rw [allIndices, List.mem_filterMap]
      exact ⟨v, hv_all, by rw [hname]⟩
    have hm_le : m.length ≤ maxIdxLength (allIndices (EMB r epsIdx)) :=
      length_le_maxIdxLength hm_all
    have hfresh_len :
        maxIdxLength (allIndices (EMB r epsIdx)) < (canonicalFreshIndex (EMB r)).length := by
      have hmax := nat_le_max_left
        (maxIdxLength (allIndices (EMB r epsIdx)))
        (maxIdxLength (allIndices (EMB r zeroIdx)))
      simp only [canonicalFreshIndex, List.length_replicate]
      omega
    rintro ⟨tail, hpre⟩
    have hlen : m.length = (canonicalFreshIndex (EMB r)).length + tail.length := by
      rw [hpre, List.length_append]
    omega

private theorem binderPath_mem {v : Var} {scope : List (Var × Index)} {q : Index}
    (h : binderPath v scope = some q) : (v, q) ∈ scope := by
  induction scope with
  | nil => cases h
  | cons xq rest ih =>
    cases xq with
    | mk x p =>
      simp only [binderPath] at h
      split at h
      · next hvx =>
        injection h with hp
        subst hvx
        subst hp
        exact List.Mem.head _
      · exact List.Mem.tail _ (ih h)

private theorem name_abstract_var (k p : Index) (scope : List (Var × Index)) (v : Var)
    (hscope : ∀ xq ∈ scope, xq.1 = indexedVar xq.1.ty (k ++ xq.2)) :
    nameBindings k p (abstractBindings scope p (.var v)) = .var v := by
  simp only [abstractBindings]
  cases hb : binderPath v scope with
  | none => rfl
  | some q =>
    have hmem : (v, q) ∈ scope := binderPath_mem hb
    have hv : v = indexedVar v.ty (k ++ q) := hscope (v, q) hmem
    simp only [nameBindings]
    exact congrArg Term.var hv.symm

private theorem name_abstract_name (k : Index) (B : BindingTerm)
    (scope : List (Var × Index)) (p : Index)
    (hscope : ∀ xq ∈ scope, xq.1 = indexedVar xq.1.ty (k ++ xq.2)) :
    nameBindings k p (abstractBindings scope p (nameBindings k p B)) = nameBindings k p B := by
  induction B generalizing scope p with
  | free v =>
    exact name_abstract_var k p scope v hscope
  | bound ρ q =>
    exact name_abstract_var k p scope (indexedVar ρ (k ++ q)) hscope
  | app B₁ B₂ ih₁ ih₂ =>
    simp only [nameBindings, abstractBindings]
    rw [ih₁ scope (p ++ zeroIdx) hscope, ih₂ scope (p ++ oneIdx) hscope]
  | lam ρ B₁ ih =>
    simp only [nameBindings, abstractBindings]
    have hscope' : ∀ xq ∈ (indexedVar ρ (k ++ p), p) :: scope,
        xq.1 = indexedVar xq.1.ty (k ++ xq.2) := by
      intro xq hmem
      cases hmem with
      | head => rfl
      | tail _ hrest => exact hscope xq hrest
    exact congrArg (Term.lam (indexedVar ρ (k ++ p)))
      (ih ((indexedVar ρ (k ++ p), p) :: scope) (p ++ zeroIdx) hscope')

theorem solution :
    (∀ r s : Term, AlphaEq r s ↔ EMB r = EMB s) ∧
    (∀ r : Term, AlphaEq (EXTRACT (EMB r)) r) ∧
    (∀ (r : Term) (k : Index), EMB (EMB r k) k = EMB r k) := by
  refine ⟨fun r s => ⟨?_, ?_⟩, extract_emb_alphaEq, fun r k => ?_⟩
  · intro h
    funext k
    exact congrArg (nameBindings k []) h
  · intro h
    have hr : AlphaEq (EXTRACT (EMB r)) r := extract_emb_alphaEq r
    have hs : AlphaEq (EXTRACT (EMB s)) s := extract_emb_alphaEq s
    unfold AlphaEq at hr hs ⊢
    rw [← hr, ← hs, h]
  · exact name_abstract_name k (abstractBindings [] [] r) [] [] (fun _ h => by cases h)
