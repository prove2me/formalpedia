-- Prove2me | solution 1 for FixedMachinePrec.lemma_5_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T12:24:12.708566+00:00
-- url     : https://prove2.me/submissions/08a29996-f6a7-4ac1-9987-ed9af428e218
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_FixedMachinePrec_generateFamily_extensional
import Theorems.Thm_FixedMachinePrec_bounded_layer_union_witness

open FixedMachinePrec

private theorem fold_preserves {α β : Type*} {P : β → Prop} (f : β → α → β)
    (step : ∀ b a, P b → P (f b a)) (xs : List α) (b : β) (hb : P b) : P (xs.foldl f b) := by
  induction xs generalizing b with
  | nil => exact hb
  | cons a xs ih => exact ih _ (step _ _ hb)

private theorem insert_nodup {N} (l : List (Finset (Fin N))) (X) (hl : l.Nodup) : (insertNew l X).Nodup := by
  unfold insertNew
  split <;> simp_all [List.nodup_append] <;> grind

private theorem layers_nodup {N} (m) (p : Fin N → Fin N → Prop) [DecidableRel p] (r) (k) :
    ∀ l ∈ genLayers p r m k, l.Nodup := by
  induction k with
  | zero => simp [genLayers]
  | succ k ih =>
    cases k with
    | zero =>
      simp only [genLayers, List.mem_singleton, forall_eq]
      unfold layerOne
      exact fold_preserves (P := List.Nodup) _ (fun _ _ h => insert_nodup _ _ (insert_nodup _ _ h)) _ _ (by simp)
    | succ k =>
      simp only [genLayers, List.mem_append, List.mem_singleton]
      intro l hl
      rcases hl with hl | rfl
      · exact ih l hl
      · unfold nextLayer
        apply fold_preserves (P := List.Nodup)
        · intro b i hb
          apply fold_preserves (P := List.Nodup) _ _ _ _ hb
          intro d X hd
          exact fold_preserves (P := List.Nodup) _ (fun _ _ h => insert_nodup _ _ (insert_nodup _ _ h)) _ _ hd
        · change ((genLayers p r m (k+1)).getD ((genLayers p r m (k+1)).length-1) []).Nodup
          rw [List.getD_eq_getElem?_getD]
          generalize he : (genLayers p r m (k+1))[(genLayers p r m (k+1)).length - 1]? = o
          cases o with
          | none => simp
          | some a => exact ih a (List.mem_of_getElem? he)

private theorem family_compl {N} (m k) (p : Fin N → Fin N → Prop) [DecidableRel p] (r) (X) (hx : X ∈ family p r m k) : Finset.univ \ X ∈ family p r m k := by
  classical
  simp only [family, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨φ, hv, hl, rfl⟩ := hx
  exact ⟨φ.compl, hv, hl, rfl⟩

theorem solution {N : ℕ} (m : ℕ) (hm : 1 ≤ m) (prec : Fin N → Fin N → Prop) [DecidableRel prec]
    (hprec : IsStrictOrder' prec) (rank : Fin N → ℕ) (hrank : IsTopoRank prec rank) (k : ℕ)
    (hk : 1 ≤ k) :
    (generateFamily prec rank m k).Nodup ∧
    (generateFamily prec rank m k).toFinset = family prec rank m k ∧
    (∀ S ∈ family prec rank m k, Finset.univ \ S ∈ family prec rank m k) ∧
    (∃ (N' : ℕ) (prec' : Fin N' → Fin N' → Prop) (_ : DecidableRel prec') (rank' : Fin N' → ℕ),
      IsStrictOrder' prec' ∧ IsTopoRank prec' rank' ∧
      ∃ X ∈ family prec' rank' m k, ∃ Y ∈ family prec' rank' m k,
        X ∪ Y ∉ family prec' rank' m k) ∧
    (∃ (N' : ℕ) (prec' : Fin N' → Fin N' → Prop) (_ : DecidableRel prec') (rank' : Fin N' → ℕ),
      IsStrictOrder' prec' ∧ IsTopoRank prec' rank' ∧
      ∃ X ∈ family prec' rank' m k, ∃ Y ∈ family prec' rank' m k,
        X ∩ Y ∉ family prec' rank' m k) := by
  classical
  refine ⟨?_, generateFamily_extensional m prec rank k hk, family_compl m k prec rank, ?_, ?_⟩
  · unfold generateFamily
    rw [List.getD_eq_getElem?_getD]
    generalize he : (genLayers prec rank m k)[k-1]? = o
    cases o with
    | none => simp
    | some l => exact layers_nodup m prec rank k l (List.mem_of_getElem? he)
  · exact bounded_layer_union_witness m k hm hk
  · obtain ⟨n,p,d,r,hp,hr,X,hX,Y,hY,hbad⟩ := bounded_layer_union_witness m k hm hk
    letI := d
    refine ⟨n,p,d,r,hp,hr,_,family_compl m k p r X hX,_,family_compl m k p r Y hY,?_⟩
    intro hi
    apply hbad
    have h := family_compl m k p r _ hi
    convert h using 1 <;> ext x <;> simp <;> tauto
