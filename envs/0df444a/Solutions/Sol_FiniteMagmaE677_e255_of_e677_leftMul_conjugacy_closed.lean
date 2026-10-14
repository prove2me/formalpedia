-- Prove2me | solution 1 for FiniteMagmaE677.e255_of_e677_leftMul_conjugacy_closed
-- status  : ACCEPTED   (prove)
-- author  : @omegaestable
-- created : 2026-10-14T00:35:25.901301+00:00
-- url     : https://prove2.me/submissions/a25cbc33-da85-4027-9db1-e80708840395

import Theorems.Thm_FiniteMagmaE677_left_bijective
import Theorems.Thm_FiniteMagmaE677_e677_implies_e255_of_existential_row_transport
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
universe u

theorem solution {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (hconj : ∀ a b : α, ∃ c : α, ∀ z : α,
      op c (op a z) = op a (op b z)) : FiniteMagmaE677.E255 op := by
  classical
  have inj (a : α) : Function.Injective (op a) :=
    (FiniteMagmaE677.left_bijective op h a).1
  let d (a x : α) := op x (op (op a x) a)
  have hd (a x : α) : op a (d a x) = x := (h x a).symm
  have hright (a x : α) : d a (op a x) = x := inj a (hd a (op a x))
  have dinj (a : α) : Function.Injective (d a) := by
    intro s t heq
    have he := congrArg (op a) heq
    simpa only [hd] using he
  have master (x a : α) : op (op a x) a = d x (d a x) := by
    apply inj x
    have he : op x (op (op a x) a) = d a x :=
      inj a ((h x a).symm.trans (hd a x).symm)
    exact he.trans (hd x (d a x)).symm
  have lc (u v : α) : ∃ c : α, op c (op u v) = d v u := by
    obtain ⟨c, hc⟩ := hconj u (op v u)
    refine ⟨c, inj v ?_⟩
    rw [hc, hd]
  apply FiniteMagmaE677.e677_implies_e255_of_existential_row_transport op h
  intro x
  refine ⟨x, ?_⟩
  let Q : Finset α := Finset.univ.image (fun a => d a x)
  have closed : Set.MapsTo (d x) (↑Q) (↑Q) := by
    intro z hz
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hz
    obtain ⟨c, hc⟩ := lc (op a x) a
    have hct : op c (d x z) = x := calc
      op c (d x z) = op c (d x (d a x)) := congrArg (fun t => op c (d x t)) ha.symm
      _ = op c (op (op a x) a) := congrArg (op c) (master x a).symm
      _ = d a (op a x) := hc
      _ = x := hright a x
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, inj c ((hd c x).trans hct.symm)⟩
  have onto : Set.SurjOn (d x) (↑Q) (↑Q) :=
    Finset.surjOn_of_injOn_of_card_le (d x) closed
      (fun _ _ _ _ heq => dinj x heq) (by rfl)
  intro a
  have ha : d a x ∈ Q := Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  obtain ⟨z, hz, heq⟩ := onto ha
  obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hz
  refine ⟨c, ?_⟩
  change op c (op x (d a x)) = x
  rw [← heq, hd, ← hc, hd]
