-- Prove2me | solution 1 for CondC.finiteness
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T17:40:45.736671+00:00
-- url     : https://prove2.me/submissions/5ea475ad-b8bf-46be-9ef7-d0bbfa718ab8

import Mathlib
import Definitions.Def_CondC_liq
import Definitions.Def_CondC_geo

open CondC

theorem solution : ¬ (∀ (w : CompactCxWorld) (F : Type), w.coherent F → ∀ i : ℕ,
    Nonempty (BundledFiniteDim (w.Coh F i) (w.add F i) (w.zero F i) (w.smul F i))) := by
  intro h
  let w : CompactCxWorld :=
    { pts := Unit, top := ⊥, compact := by infer_instance, dim := 0,
      Coh := fun _ _ => Bool, add := fun _ _ x _ => x, zero := fun _ _ => false,
      smul := fun _ _ _ x => x, coherent := fun _ => True, dualF := id }
  obtain ⟨B⟩ := h w Unit trivial 0
  -- span is a bijection (Fin dim → ℂ) ≃ Bool, impossible
  have hinj := B.span_inj
  have hsurj : Function.Surjective B.span := fun v => ⟨B.coord v, B.span_coord v⟩
  rcases Nat.eq_zero_or_pos B.dim with h0 | hpos
  · obtain ⟨x, hx⟩ := hsurj true
    obtain ⟨y, hy⟩ := hsurj false
    have : x = y := by
      funext i; exact absurd i.2 (by omega)
    rw [this] at hx; rw [hx] at hy; exact Bool.noConfusion hy
  · have e1 := hinj (fun _ => 0) (fun _ => 1)
    have e2 := hinj (fun _ => 0) (fun _ => 2)
    have e3 := hinj (fun _ => 1) (fun _ => 2)
    have n1 : (fun _ : Fin B.dim => (0:ℂ)) ≠ (fun _ => 1) := fun h => by
      have := congrFun h ⟨0, hpos⟩; norm_num at this
    have n2 : (fun _ : Fin B.dim => (0:ℂ)) ≠ (fun _ => 2) := fun h => by
      have := congrFun h ⟨0, hpos⟩; norm_num at this
    have n3 : (fun _ : Fin B.dim => (1:ℂ)) ≠ (fun _ => 2) := fun h => by
      have := congrFun h ⟨0, hpos⟩; norm_num at this
    generalize B.span (fun _ => 0) = a at e1 e2
    generalize B.span (fun _ => 1) = b at e1 e3
    generalize B.span (fun _ => 2) = c at e2 e3
    cases a <;> cases b <;> cases c <;> simp_all
