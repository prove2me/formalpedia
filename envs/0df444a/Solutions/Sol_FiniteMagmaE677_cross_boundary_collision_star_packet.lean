-- Prove2me | solution 1 for FiniteMagmaE677.cross_boundary_collision_star_packet
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-15T03:05:04.015042+00:00
-- url     : https://prove2.me/submissions/301ee9b1-c997-4ac7-ada9-183a6f2c621b

import Definitions.Def_FiniteMagmaE677
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

universe u

open FiniteMagmaE677

private theorem starPacket_left_bijective
    {α : Type u} [Fintype α] (op : α → α → α) (h : E677 op) (y : α) :
    Function.Bijective (op y) := by
  apply Finite.surjective_iff_bijective.mp
  intro x
  exact ⟨op x (op (op y x) y), (h x y).symm⟩

private theorem starPacket_backward_recurrence
    {α : Type u} [Fintype α] (op : α → α → α) (h : E677 op) (x y : α) :
    x = op (op y x) (op (op y (op y x)) y) := by
  exact (starPacket_left_bijective op h y).1 (h (op y x) y)

private theorem starPacket_fixer_unique
    {α : Type u} [Fintype α] (op : α → α → α) (h : E677 op)
    (x y : α) (hfix : op y x = x) :
    y = op (op x x) x := by
  have hinj (z : α) : Function.Injective (op z) :=
    (starPacket_left_bijective op h z).1
  have inv_at_x : op y (op x (op x y)) = x := by
    have hi := (h x y).symm
    rwa [hfix] at hi
  have hx_xy := hinj y (hfix.trans inv_at_x.symm)
  exact hinj x (hinj x (hx_xy.symm.trans (h x x)))

theorem solution
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x A c : α)
    (hnofix : ¬ FiniteMagmaE677.HasFixerAt op x)
    (hA_notin : ¬ FiniteMagmaE677.InLeftOrbit op x A)
    (hA_unique : ∀ a : α, ¬ FiniteMagmaE677.InLeftOrbit op x a → a = A)
    (hc : FiniteMagmaE677.InLeftOrbit op x c)
    (hcollision : op c x = op A x) :
    FiniteMagmaE677.InLeftOrbit op x (op A x) ∧
      op A x ≠ x ∧
      op A x ≠ A ∧
      FiniteMagmaE677.InLeftOrbit op x (op A A) ∧
      op A A ≠ x ∧
      op A A ≠ op A x ∧
      op A A ≠ A ∧
      op x A = A ∧
      op A (op A x) = A ∧
      op (op A A) A = x ∧
      op (op c (op A x)) c = op A A ∧
      FiniteMagmaE677.InLeftOrbit op x (op c (op A x)) ∧
      op c (op A x) ≠ op A x ∧
      FiniteMagmaE677.InLeftOrbit op x (op A (op c (op A x))) ∧
      op A (op c (op A x)) ≠ A ∧
      op A (op c (op A x)) ≠ op A A ∧
      (op A (op c (op A x)) = op A x →
        op c (op A x) = x ∧
          op x (op (op A x) c) = op A x ∧
          op (op A x) (op x c) = x) := by
  have hleft_bij : ∀ y : α, Function.Bijective (op y) :=
    fun y => starPacket_left_bijective op h y
  have hxA : op x A = A := by
    obtain ⟨B, hB⟩ := (hleft_bij x).2 A
    have hB_notin : ¬ InLeftOrbit op x B := by
      rintro ⟨k, hk⟩
      apply hA_notin
      refine ⟨k + 1, ?_⟩
      rw [Function.iterate_succ_apply']
      exact hB ▸ congrArg (op x) hk
    simpa [hA_unique B hB_notin] using hB
  have hPhi : op (op A A) A = x :=
    (starPacket_fixer_unique op h A x hxA).symm
  have hA_Ax : op A (op A x) = A := by
    have hE := h A A
    rw [hPhi] at hE
    exact hE.symm
  have hA_ne_x : A ≠ x := by
    intro hAx
    apply hA_notin
    exact ⟨0, by simpa using hAx⟩
  have hd_ne_x : op A x ≠ x := by
    intro hdx
    exact hnofix ⟨A, hdx⟩
  have hd_ne_A : op A x ≠ A := by
    intro hdA
    have hAA : op A A = A := by simpa [hdA] using hA_Ax
    have hxAeq : x = A := by simpa [hAA] using hPhi.symm
    exact hA_ne_x hxAeq.symm
  have hd_orbit : InLeftOrbit op x (op A x) := by
    by_contra hd_notin
    exact hd_ne_A (hA_unique _ hd_notin)
  have hb_ne_A : op A A ≠ A := by
    intro hbA
    have hAx : A = x := by simpa [hbA] using hPhi
    exact hA_ne_x hAx
  have hb_orbit : InLeftOrbit op x (op A A) := by
    by_contra hb_notin
    exact hb_ne_A (hA_unique _ hb_notin)
  have hb_ne_x : op A A ≠ x := by
    intro hbx
    have hfixx : op x A = x := by simpa [hbx] using hPhi
    exact hA_ne_x (hxA.symm.trans hfixx)
  have hb_ne_d : op A A ≠ op A x := by
    intro hbd
    exact hA_ne_x ((hleft_bij A).1 hbd)
  have hstar : op (op c (op A x)) c = op A A := by
    have hc_rec := starPacket_backward_recurrence op h x c
    have hA_rec := starPacket_backward_recurrence op h x A
    rw [hcollision] at hc_rec
    rw [hA_Ax] at hA_rec
    exact (hleft_bij (op A x)).1 (hc_rec.symm.trans hA_rec)
  have hu_ne_A : op c (op A x) ≠ A := by
    intro huA
    have hAcAA : op A c = op A A := by simpa [huA] using hstar
    have hcA : c = A := (hleft_bij A).1 hAcAA
    exact hA_notin (hcA ▸ hc)
  have hu_orbit : InLeftOrbit op x (op c (op A x)) := by
    by_contra hnot
    exact hu_ne_A (hA_unique _ hnot)
  have hu_ne_d : op c (op A x) ≠ op A x := by
    intro hud
    have hdx : op A x = x := by
      apply (hleft_bij c).1
      calc
        op c (op A x) = op A x := hud
        _ = op c x := hcollision.symm
    exact hnofix ⟨A, hdx⟩
  have hv_orbit : InLeftOrbit op x (op A (op c (op A x))) := by
    by_contra hv_notin
    have hvA : op A (op c (op A x)) = A := hA_unique _ hv_notin
    apply hu_ne_d
    apply (hleft_bij A).1
    calc
      op A (op c (op A x)) = A := hvA
      _ = op A (op A x) := hA_Ax.symm
  have hv_ne_b : op A (op c (op A x)) ≠ op A A := by
    intro hvb
    have huA : op c (op A x) = A := (hleft_bij A).1 hvb
    exact hu_ne_A huA
  have hv_ne_A : op A (op c (op A x)) ≠ A := by
    intro hvA
    exact hA_notin (hvA ▸ hv_orbit)
  refine
    ⟨hd_orbit, hd_ne_x, hd_ne_A,
      hb_orbit, hb_ne_x, hb_ne_d, hb_ne_A,
      hxA, hA_Ax, hPhi, hstar,
      hu_orbit, hu_ne_d, hv_orbit, hv_ne_A, hv_ne_b, ?_⟩
  intro hvd
  have hux : op c (op A x) = x := by
    apply (hleft_bij A).1
    exact hvd
  have hx_dc : op x (op (op A x) c) = op A x := by
    apply (hleft_bij c).1
    calc
      op c (op x (op (op A x) c)) = x := by
        simpa [hcollision] using (h x c).symm
      _ = op c (op A x) := hux.symm
  have hd_xc : op (op A x) (op x c) = x := by
    apply (hleft_bij c).1
    calc
      op c (op (op A x) (op x c)) = op A x := by
        simpa [hux] using (h (op A x) c).symm
      _ = op c x := hcollision.symm
  exact ⟨hux, hx_dc, hd_xc⟩
