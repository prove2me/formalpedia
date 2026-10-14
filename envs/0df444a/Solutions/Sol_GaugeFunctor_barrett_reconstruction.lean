-- Prove2me | solution 1 for GaugeFunctor.barrett_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-11T20:18:28.271657+00:00
-- url     : https://prove2.me/submissions/d0b17ec7-b209-418d-9fd3-10d137bb2d7e

import Mathlib
import Definitions.Def_GaugeFunctor_defs

open CategoryTheory

namespace GaugeFunctor

theorem brc_isPath_append (X : Graph) : ∀ (w w' : List X.Step) (x y z : Fin X.nV),
    X.IsPath x w y → X.IsPath y w' z → X.IsPath x (w ++ w') z
  | [], w', x, y, z, h, h' => by
      simp only [Graph.IsPath] at h; subst h; simpa using h'
  | s :: w, w', x, y, z, h, h' => by
      simp only [Graph.IsPath] at h
      exact ⟨h.1, brc_isPath_append X w w' _ y z h.2 h'⟩

theorem brc_isPath_rev (X : Graph) : ∀ (w : List X.Step) (x y : Fin X.nV),
    X.IsPath x w y → X.IsPath y (w.reverse.map X.flip) x
  | [], x, y, h => by
      simp only [Graph.IsPath] at h; subst h; simp [Graph.IsPath]
  | s :: w, x, y, h => by
      simp only [Graph.IsPath] at h
      obtain ⟨hs, hw⟩ := h
      have ih := brc_isPath_rev X w _ y hw
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
      refine brc_isPath_append X _ _ y _ x ih ?_
      subst hs
      rcases s with ⟨e, b⟩
      cases b <;> simp [Graph.IsPath, Graph.flip, Graph.stepSrc, Graph.stepTgt]

theorem brc_flip_flip (X : Graph) (s : X.Step) : X.flip (X.flip s) = s := by
  rcases s with ⟨e, b⟩; simp [Graph.flip]

theorem brc_flip_src (X : Graph) (s : X.Step) : X.stepSrc (X.flip s) = X.stepTgt s := by
  rcases s with ⟨e, b⟩; cases b <;> simp [Graph.flip, Graph.stepSrc, Graph.stepTgt]

theorem brc_rev_rev (X : Graph) (w : List X.Step) :
    (w.reverse.map X.flip).reverse.map X.flip = w := by
  simp [List.map_reverse, List.map_map, Function.comp_def, brc_flip_flip]

/-- Cancelling `rev w ++ w` inside a loop at `x`. -/
theorem brc_cancel (X : Graph) (G : Type) [Group G] (x : Fin X.nV) (H : HolMap X G x) :
    ∀ (w : List X.Step) (v z : Fin X.nV) (p q : List X.Step), X.IsPath v w z →
      X.IsPath x p z → X.IsPath z q x →
        H.toFun (p ++ (w.reverse.map X.flip ++ (w ++ q))) = H.toFun (p ++ q)
  | [], v, z, p, q, _, _, _ => by simp
  | s :: w, v, z, p, q, h, hp, hq => by
      obtain ⟨_, hw⟩ := h
      have hrw := brc_isPath_rev X w _ z hw
      have key : p ++ ((s :: w).reverse.map X.flip ++ (s :: w ++ q))
          = (p ++ w.reverse.map X.flip) ++ X.flip s :: X.flip (X.flip s) :: (w ++ q) := by
        simp [brc_flip_flip]
      rw [key, H.backtrack _ _ _ (X.stepTgt s)
        (brc_isPath_append X _ _ x z _ hp hrw) (brc_flip_src X s)
        (brc_isPath_append X _ _ _ z x hw hq), List.append_assoc]
      exact brc_cancel X G x H w _ z p q hw hp hq

/-- Cancelling `w ++ rev w` inside a loop at `x`. -/
theorem brc_cancel' (X : Graph) (G : Type) [Group G] (x : Fin X.nV) (H : HolMap X G x)
    (w : List X.Step) (v z : Fin X.nV) (p q : List X.Step) (h : X.IsPath v w z)
    (hp : X.IsPath x p v) (hq : X.IsPath v q x) :
    H.toFun (p ++ (w ++ (w.reverse.map X.flip ++ q))) = H.toFun (p ++ q) := by
  have := brc_cancel X G x H (w.reverse.map X.flip) z v p q (brc_isPath_rev X w v z h) hp hq
  rwa [brc_rev_rev] at this

theorem brc_one (X : Graph) (G : Type) [Group G] (x : Fin X.nV) (H : HolMap X G x) :
    H.toFun [] = 1 := by
  have h := H.mul [] [] rfl rfl
  simp only [List.append_nil] at h
  exact mul_left_cancel (a := H.toFun []) (by rw [mul_one]; exact h.symm)

theorem brc_main (X : Graph) (G : Type) [Group G] (x : Fin X.nV)
    (hX : X.Connected x) (H : HolMap X G x) :
    ∃ A : Fin X.nE → G, ∀ γ, X.IsPath x γ x → hol X G A γ = H.toFun γ := by
  classical
  choose w0 hw0 using (hX : ∀ y, ∃ w, X.IsPath x w y)
  let w : Fin X.nV → List X.Step := fun y => if y = x then [] else w0 y
  have hw : ∀ y, X.IsPath x (w y) y := by
    intro y
    by_cases h : y = x
    · subst h; simp [w, Graph.IsPath]
    · simp only [w, h, if_false]; exact hw0 y
  have hwx : w x = [] := by simp [w]
  let A : Fin X.nE → G := fun e => H.toFun (w (X.src e) ++ (e, true) :: (w (X.tgt e)).reverse.map X.flip)
  -- each step's transport is the holonomy-map value of a "lollipop" loop
  have hS : ∀ s : X.Step, stepHol X G A s
      = H.toFun (w (X.stepSrc s) ++ s :: (w (X.stepTgt s)).reverse.map X.flip) := by
    rintro ⟨e, b⟩
    cases b
    · simp only [stepHol, Graph.stepSrc, Graph.stepTgt, Bool.false_eq_true, if_false]
      refine (eq_inv_of_mul_eq_one_right ?_).symm
      have p1 : X.IsPath x (w (X.src e) ++ (e, true) :: (w (X.tgt e)).reverse.map X.flip) x :=
        brc_isPath_append X _ _ x (X.src e) x (hw _)
          ⟨by simp [Graph.stepSrc], by
            exact brc_isPath_rev X _ x _ (hw (X.tgt e))⟩
      have p2 : X.IsPath x (w (X.tgt e) ++ (e, false) :: (w (X.src e)).reverse.map X.flip) x :=
        brc_isPath_append X _ _ x (X.tgt e) x (hw _)
          ⟨by simp [Graph.stepSrc], by
            exact brc_isPath_rev X _ x _ (hw (X.src e))⟩
      rw [← H.mul _ _ p1 p2]
      have hpe : X.IsPath x (w (X.src e) ++ [(e, true)]) (X.tgt e) :=
        brc_isPath_append X _ _ x (X.src e) _ (hw _)
          ⟨by simp [Graph.stepSrc], by simp [Graph.IsPath, Graph.stepTgt]⟩
      have hqe : X.IsPath (X.tgt e) ((e, false) :: (w (X.src e)).reverse.map X.flip) x :=
        ⟨by simp [Graph.stepSrc], by
          exact brc_isPath_rev X _ x _ (hw (X.src e))⟩
      have e1 : (w (X.src e) ++ (e, true) :: (w (X.tgt e)).reverse.map X.flip) ++
          (w (X.tgt e) ++ (e, false) :: (w (X.src e)).reverse.map X.flip)
          = (w (X.src e) ++ [(e, true)]) ++ ((w (X.tgt e)).reverse.map X.flip ++
              (w (X.tgt e) ++ (e, false) :: (w (X.src e)).reverse.map X.flip)) := by simp
      rw [e1, brc_cancel X G x H _ x _ _ _ (hw _) hpe hqe]
      have e2 : (w (X.src e) ++ [(e, true)]) ++ (e, false) :: (w (X.src e)).reverse.map X.flip
          = w (X.src e) ++ (e, true) :: X.flip (e, true) :: (w (X.src e)).reverse.map X.flip := by
        simp [Graph.flip]
      rw [e2, H.backtrack _ _ _ (X.src e) (hw _) (by simp [Graph.stepSrc])
        (brc_isPath_rev X _ x _ (hw _))]
      have e3 := brc_cancel' X G x H (w (X.src e)) x _ [] [] (hw _) rfl rfl
      simp only [List.nil_append, List.append_nil] at e3
      rw [e3, brc_one]
    · rfl
  have hmain : ∀ (γ : List X.Step) (y : Fin X.nV), X.IsPath y γ x →
      hol X G A γ = H.toFun (w y ++ γ) := by
    intro γ
    induction γ with
    | nil =>
        intro y hy
        simp only [Graph.IsPath] at hy; subst hy
        simp [hol, hwx, brc_one]
    | cons s γ ih =>
        intro y hy
        obtain ⟨hs, hγ⟩ := hy
        have h1 : hol X G A (s :: γ) = stepHol X G A s * hol X G A γ := by simp [hol]
        rw [h1, hS s, ih _ hγ, hs]
        have hrv := brc_isPath_rev X _ x _ (hw (X.stepTgt s))
        have p1 : X.IsPath x (w y ++ s :: (w (X.stepTgt s)).reverse.map X.flip) x :=
          brc_isPath_append X _ _ x y x (hw _) ⟨hs, hrv⟩
        have p2 : X.IsPath x (w (X.stepTgt s) ++ γ) x :=
          brc_isPath_append X _ _ x _ x (hw _) hγ
        rw [← H.mul _ _ p1 p2]
        have e1 : (w y ++ s :: (w (X.stepTgt s)).reverse.map X.flip) ++ (w (X.stepTgt s) ++ γ)
            = (w y ++ [s]) ++ ((w (X.stepTgt s)).reverse.map X.flip ++
                (w (X.stepTgt s) ++ γ)) := by simp
        rw [e1, brc_cancel X G x H _ x _ _ _ (hw _)
          (brc_isPath_append X _ _ x y _ (hw _) (show X.IsPath y [s] (X.stepTgt s) from ⟨hs, rfl⟩)) hγ]
        simp
  refine ⟨A, fun γ hγ => ?_⟩
  rw [hmain γ x hγ, hwx, List.nil_append]

end GaugeFunctor

open GaugeFunctor in
theorem solution (X : Graph) (G : Type) [Group G] (x : Fin X.nV)
    (hX : X.Connected x) (H : HolMap X G x) :
    ∃ A : Fin X.nE → G, ∀ γ, X.IsPath x γ x → hol X G A γ = H.toFun γ :=
  brc_main X G x hX H
