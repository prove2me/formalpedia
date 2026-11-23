-- Prove2me | solution 1 for BergerSchwichtenberg1991V2.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:59:54.052804+00:00
-- url     : https://prove2.me/submissions/abd5a463-36e5-4d95-9096-fd16ce70b32b

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

theorem solution (k : Index) :
    (∀ r s : Term, AlphaEq r s → alphaRename k r = alphaRename k s) ∧
    (∀ r : Term, (∀ m ∈ freeIndices r, ¬ IsPrefixOf k m) → AlphaEq (alphaRename k r) r) := by
  refine ⟨fun r s h => congrArg (nameBindings k []) h, fun r h => ?_⟩
  apply abstract_name_abstract k r [] [] trivial
  intro v hv _ m hname
  have hv_free : v ∈ freeVars r := List.mem_eraseDups.2 hv
  have hm : m ∈ freeIndices r := by
    rw [freeIndices, List.mem_filterMap]
    exact ⟨v, hv_free, by rw [hname]⟩
  exact h m hm
