-- Prove2me | solution 1 for DirKECC1549.Main.walks_in_scc
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T09:44:16.508677+00:00
-- url     : https://prove2.me/submissions/5c750d0b-bb44-4c29-b69d-ce0dffd9d4ce

import Definitions.Def_DirKECC1549_Main_Graph
set_option autoImplicit false
open DirKECC1549.Main

private theorem walk_append {n m : ℕ} {G : Fin m → Fin n × Fin n}
    {u v w : Fin n} {p q : List (Fin m)} (hp : IsWalk G u p v) (hq : IsWalk G v q w) :
    IsWalk G u (p ++ q) w := by
  induction hp with
  | nil => simpa using hq
  | cons e p he hw ih => exact IsWalk.cons e (p ++ q) he (ih hq)

private theorem reach_trans {n m : ℕ} {G : Fin m → Fin n × Fin n} {u v w : Fin n}
    (h : Reach G u v) (h' : Reach G v w) : Reach G u w := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := h'
  exact ⟨p ++ q, walk_append hp hq⟩

private theorem walk_scc {n m : ℕ} {G : Fin m → Fin n × Fin n} {a x y : Fin n}
    {p : List (Fin m)} (hw : IsWalk G x p y) (hax : Reach G a x) (hya : Reach G y a) :
    ∀ e ∈ p, (G e).1 ∈ sccOf G a ∧ (G e).2 ∈ sccOf G a := by
  induction hw with
  | nil => simp
  | @cons u v e p he hw ih =>
    have hedge : Reach G u (G e).2 := ⟨[e], IsWalk.cons e [] he (IsWalk.nil _)⟩
    have htail : Reach G u v := ⟨e :: p, IsWalk.cons e p he hw⟩
    have hhead : Reach G (G e).2 v := ⟨p, hw⟩
    have hax' := reach_trans hax hedge
    have hu : StronglyConn G a u := ⟨hax, reach_trans htail hya⟩
    have hv : StronglyConn G a (G e).2 := ⟨hax', reach_trans hhead hya⟩
    intro f hf
    simp only [List.mem_cons] at hf
    rcases hf with rfl | hf
    · constructor <;> simp [sccOf, he, hu, hv]
    · exact ih hax' hya f hf

theorem solution {n m : ℕ} (G : Fin m → Fin n × Fin n) (a x y : Fin n)
    (hx : StronglyConn G a x) (hy : StronglyConn G a y) :
    ∀ p, IsWalk G x p y → ∀ e ∈ p, (G e).1 ∈ sccOf G a ∧ (G e).2 ∈ sccOf G a := by
  intro p hp
  exact walk_scc hp hx.1 hy.2
