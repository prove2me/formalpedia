-- Prove2me | solution 1 for FixedMachinePrec.corollary_7_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T17:03:07.100021+00:00
-- url     : https://prove2.me/submissions/5a3fdad6-4161-4c2a-a9cd-fa747a3af28b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FixedMachinePrec_Separator
import Theorems.Thm_FixedMachinePrec_normalized_prefix_separator
import Theorems.Thm_FixedMachinePrec_ideal_priority_extension

open FixedMachinePrec

private theorem full_count {N m} {p : Fin N → Fin N → Prop} {W S} (hs : IsFullSchedule p m W S) : W.card = m*S.length := by
  obtain ⟨hslot,hdis,hu,horder⟩ := hs
  clear horder
  rw [← hu]; clear hu
  induction S with
  | nil => simp
  | cons a s ih =>
    have hd := List.pairwise_cons.mp hdis
    have dj : Disjoint a (s.foldr (· ∪ ·) ∅) := by
      have aux (l : List (Finset (Fin N))) (h : ∀ b ∈ l, Disjoint a b) : Disjoint a (l.foldr (· ∪ ·) ∅) := by
        induction l with
        | nil => simp
        | cons b l ih => simp [h b (by simp),ih (fun c hc => h c (by simp [hc]))]
      exact aux _ hd.1
    simp only [List.foldr_cons,Finset.card_union_of_disjoint dj,List.length_cons,Nat.mul_add,Nat.mul_one]
    rw [(hslot a (by simp)).1,ih (fun b hb => hslot b (by simp [hb])) hd.2,Nat.add_comm]

private theorem normalized_exists {N} (p : Fin N → Fin N → Prop) (m : ℕ) (U : Finset (Fin N)) (pri : List (Fin N))
    (hm : 3 ≤ m) (hf : ∃ S, IsFullSchedule p m U S) : ∃ S, IsNormalized p m U pri S := by
  classical
  let enum := ((Finset.range (U.card+1)).biUnion fun n => (Finset.univ : Finset (Fin n → Finset (Fin N))).image List.ofFn).filter (IsFullSchedule p m U)
  have mem (S) (hs : IsFullSchedule p m U S) : S ∈ enum := by
    have h := full_count hs
    have hlen : S.length < U.card+1 := by nlinarith
    exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨S.length,Finset.mem_range.mpr hlen,Finset.mem_image.mpr ⟨S.get,Finset.mem_univ _,by simp⟩⟩,hs⟩
  obtain ⟨S,hs⟩ := hf
  obtain ⟨Z,hZ,hmin⟩ := Finset.exists_min_image enum (priEnc pri) ⟨S,mem S hs⟩
  exact ⟨Z,(Finset.mem_filter.mp hZ).2,fun T hT => hmin T (mem T hT)⟩

theorem solution {N : ℕ} (m : ℕ) (hm : 3 ≤ m) (prec : Fin N → Fin N → Prop)
    [DecidableRel prec] (hprec : IsStrictOrder' prec) (U : Finset (Fin N)) (hU : U.Nonempty) :
    (∀ (pri : List (Fin N)) (Zs : List (Finset (Fin N))), IsPriorityList prec U pri →
      IsNormalized prec m U pri Zs →
      ∀ k ≤ U.card, ∃ r : ℕ, Separates prec Zs (priorityPrefix pri k) r) ∧
    ((∃ Zs : List (Finset (Fin N)), IsFullSchedule prec m U Zs) →
      ∀ I : Finset (Fin N), IsIdealIn prec U I →
        ∃ Zs : List (Finset (Fin N)), IsFullSchedule prec m U Zs ∧ ∃ r : ℕ, Separates prec Zs I r) := by
  have first := normalized_prefix_separator m prec hm hprec U hU
  refine ⟨fun pri Zs hp hz k hk => first pri hp Zs hz k hk,?_⟩
  intro hf I hI
  obtain ⟨pri,hp,he⟩ := ideal_priority_extension prec hprec U I hI
  obtain ⟨Z,hZ⟩ := normalized_exists prec m U pri hm hf
  obtain ⟨r,hr⟩ := first pri hp Z hZ I.card (Finset.card_le_card hI.1)
  exact ⟨Z,hZ.1,r,he ▸ hr⟩
