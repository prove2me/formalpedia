-- Prove2me | solution 1 for DirKECC1549.Main.unit_flow_add_trail
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T10:48:43.399552+00:00
-- url     : https://prove2.me/submissions/83e6d74c-74b6-4933-8642-07c667bfe462

import Definitions.Def_DirKECC1549_Main_Alg3
set_option autoImplicit false
open DirKECC1549.Main

private theorem trail_balance {n m : ℕ} (D : Fin m → Fin n × Fin n)
    {u v : Fin n} {p : List (Fin m)} (hw : IsWalk D u p v) (hn : p.Nodup) :
    IsUnitFlow D p.toFinset u v 1 := by
  classical
  induction hw with
  | nil =>
    intro x
    simp [IsUnitFlow]
  | @cons u v e p ht hw ih =>
    have hnot : e ∉ p := (List.nodup_cons.mp hn).1
    have hnodup : p.Nodup := (List.nodup_cons.mp hn).2
    have hrec := ih hnodup
    intro x
    have hr := hrec x
    have hnF : e ∉ p.toFinset := by simpa using hnot
    by_cases htail : (D e).1 = x <;> by_cases hhead : (D e).2 = x
    all_goals simp [IsUnitFlow, List.toFinset_cons, Finset.filter_insert, htail, hhead,
      hnF, Finset.card_insert_of_notMem] at hr ⊢
    all_goals subst_vars <;> simp_all <;> omega

theorem solution {n m : ℕ} (D : Fin m → Fin n × Fin n)
    (u v : Fin n) (q : ℕ) (F : Finset (Fin m)) (p : List (Fin m))
    (hF : IsUnitFlow D F u v q) (hp : IsTrail D u p v)
    (hdis : Disjoint F p.toFinset) : IsUnitFlow D (F ∪ p.toFinset) u v (q + 1) := by
  classical
  have htrail := trail_balance D hp.1 hp.2
  intro x
  have htail : Disjoint (F.filter (fun e ↦ (D e).1 = x))
      (p.toFinset.filter (fun e ↦ (D e).1 = x)) :=
    hdis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hhead : Disjoint (F.filter (fun e ↦ (D e).2 = x))
      (p.toFinset.filter (fun e ↦ (D e).2 = x)) :=
    hdis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have h1 := hF x
  have h2 := htrail x
  simp only [Finset.filter_union, Finset.card_union_of_disjoint htail,
    Finset.card_union_of_disjoint hhead, Nat.cast_add, Nat.cast_one]
  split_ifs at h1 h2 ⊢ <;> omega
