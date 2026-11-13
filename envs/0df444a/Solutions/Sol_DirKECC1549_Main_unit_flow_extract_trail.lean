-- Prove2me | solution 1 for DirKECC1549.Main.unit_flow_extract_trail
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T10:58:46.058907+00:00
-- url     : https://prove2.me/submissions/4520306b-6727-4809-9889-bafba19a4722

import Theorems.Thm_DirKECC1549_Main_positive_flow_trail
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
    (u v : Fin n) (huv : u ≠ v) (q : ℕ) (F : Finset (Fin m))
    (hF : IsUnitFlow D F u v (q + 1)) :
    ∃ p : List (Fin m), IsTrail D u p v ∧ p.toFinset ⊆ F ∧
      IsUnitFlow D (F \ p.toFinset) u v q := by
  classical
  obtain ⟨p, hp, hsub⟩ := positive_flow_trail D u v huv q F hF
  refine ⟨p, hp, hsub, ?_⟩
  have htrail := trail_balance D hp.1 hp.2
  have heq : (F \ p.toFinset) ∪ p.toFinset = F := Finset.sdiff_union_of_subset hsub
  have hdis : Disjoint (F \ p.toFinset) p.toFinset := Finset.sdiff_disjoint
  intro x
  have htail : Disjoint ((F \ p.toFinset).filter (fun e ↦ (D e).1 = x))
      (p.toFinset.filter (fun e ↦ (D e).1 = x)) :=
    hdis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hhead : Disjoint ((F \ p.toFinset).filter (fun e ↦ (D e).2 = x))
      (p.toFinset.filter (fun e ↦ (D e).2 = x)) :=
    hdis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have h1 := hF x
  have h2 := htrail x
  rw [← heq] at h1
  simp only [Finset.filter_union, Finset.card_union_of_disjoint htail,
    Finset.card_union_of_disjoint hhead, Nat.cast_add, Nat.cast_one] at h1
  split_ifs at h1 h2 ⊢ <;> omega
