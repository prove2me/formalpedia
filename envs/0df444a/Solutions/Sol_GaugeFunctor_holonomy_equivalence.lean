-- Prove2me | solution 1 for GaugeFunctor.holonomy_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-14T20:35:03.487605+00:00
-- url     : https://prove2.me/submissions/65e4b154-08f0-423c-8aaa-473ce7475817

import Mathlib
import Definitions.Def_GaugeFunctor_defs

open CategoryTheory

namespace GaugeFunctor

theorem hff_main (X : Graph) (G : Type) [Group G] (x : Fin X.nV)
    (hX : X.Connected x) : (holF X G x).Faithful := by
  refine ⟨fun {A B} {g g'} hgg => ?_⟩
  have hx : g.1 x = g'.1 x := congrArg Subtype.val hgg
  apply Subtype.ext
  funext y
  obtain ⟨w, hw⟩ := hX y
  have h1 := hol_gaugeAct (X := X) (G := G) g.1 A.conn w x y hw
  have h2 := hol_gaugeAct (X := X) (G := G) g'.1 A.conn w x y hw
  rw [g.2] at h1
  rw [g'.2, ← hx, h1] at h2
  have := mul_left_cancel h2
  exact inv_injective this

theorem hfu_isPath_append (X : Graph) : ∀ (w w' : List X.Step) (x y z : Fin X.nV),
    X.IsPath x w y → X.IsPath y w' z → X.IsPath x (w ++ w') z
  | [], w', x, y, z, h, h' => by
      simp only [Graph.IsPath] at h; subst h; simpa using h'
  | s :: w, w', x, y, z, h, h' => by
      simp only [Graph.IsPath] at h
      exact ⟨h.1, hfu_isPath_append X w w' _ y z h.2 h'⟩

theorem hfu_isPath_rev (X : Graph) : ∀ (w : List X.Step) (x y : Fin X.nV),
    X.IsPath x w y → X.IsPath y (w.reverse.map X.flip) x
  | [], x, y, h => by
      simp only [Graph.IsPath] at h; subst h; simp [Graph.IsPath]
  | s :: w, x, y, h => by
      simp only [Graph.IsPath] at h
      obtain ⟨hs, hw⟩ := h
      have ih := hfu_isPath_rev X w _ y hw
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
      refine hfu_isPath_append X _ _ y _ x ih ?_
      subst hs
      rcases s with ⟨e, b⟩
      cases b <;> simp [Graph.IsPath, Graph.flip, Graph.stepSrc, Graph.stepTgt]

theorem hfu_hol_rev (X : Graph) (G : Type) [Group G] (A : Fin X.nE → G) :
    ∀ w : List X.Step, hol X G A (w.reverse.map X.flip) = (hol X G A w)⁻¹
  | [] => by simp [hol]
  | s :: w => by
      have ih := hfu_hol_rev X G A w
      have hs : stepHol X G A (X.flip s) = (stepHol X G A s)⁻¹ := by
        rcases s with ⟨e, b⟩; cases b <;> simp [stepHol, Graph.flip]
      have h1 : hol X G A (s :: w) = stepHol X G A s * hol X G A w := by simp [hol]
      have h2 : hol X G A [X.flip s] = stepHol X G A (X.flip s) := by simp [hol]
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, hol_append]
      rw [ih, h1, h2, hs, mul_inv_rev]

theorem hfu_main (X : Graph) (G : Type) [Group G] (x : Fin X.nV)
    (hX : X.Connected x) : (holF X G x).Full := by
  refine ⟨fun {A B} f => ?_⟩
  choose w hw using (hX : ∀ y, ∃ w, X.IsPath x w y)
  have hf : ∀ γ, X.IsPath x γ x →
      hol X G B.conn γ = f.1 * hol X G A.conn γ * (f.1)⁻¹ := f.2
  let g : Fin X.nV → G := fun y =>
    (hol X G B.conn (w y))⁻¹ * f.1 * hol X G A.conn (w y)
  have hgx : g x = f.1 := by
    show (hol X G B.conn (w x))⁻¹ * f.1 * hol X G A.conn (w x) = f.1
    rw [hf (w x) (hw x)]; group
  have hg : gaugeAct X G g A.conn = B.conn := by
    funext e
    have hstep : X.IsPath (X.src e) [(e, true)] (X.tgt e) := by
      simp [Graph.IsPath, Graph.stepSrc, Graph.stepTgt]
    have hp : X.IsPath x
        (w (X.src e) ++ [(e, true)] ++ (w (X.tgt e)).reverse.map X.flip) x :=
      hfu_isPath_append X _ _ x (X.tgt e) x
        (hfu_isPath_append X _ _ x (X.src e) (X.tgt e) (hw _) hstep)
        (hfu_isPath_rev X _ x _ (hw _))
    have key := hf _ hp
    have he : ∀ C : Fin X.nE → G, hol X G C [(e, true)] = C e := by
      intro C; simp [hol, stepHol]
    simp only [hol_append, hfu_hol_rev, he] at key
    show (hol X G B.conn (w (X.src e)))⁻¹ * f.1 * hol X G A.conn (w (X.src e)) * A.conn e *
      ((hol X G B.conn (w (X.tgt e)))⁻¹ * f.1 * hol X G A.conn (w (X.tgt e)))⁻¹ = B.conn e
    generalize hol X G B.conn (w (X.src e)) = bu at key ⊢
    generalize hol X G B.conn (w (X.tgt e)) = bv at key ⊢
    generalize hol X G A.conn (w (X.src e)) = au at key ⊢
    generalize hol X G A.conn (w (X.tgt e)) = av at key ⊢
    generalize f.1 = k at key ⊢
    rw [show B.conn e = bu⁻¹ * (bu * B.conn e * bv⁻¹) * bv by group, key]
    group
  exact ⟨⟨g, hg⟩, Subtype.ext hgx⟩

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

theorem heq_essSurj (X : Graph) (G : Type) [Group G] (x : Fin X.nV)
    (hX : X.Connected x) : (holF X G x).EssSurj := by
  refine ⟨fun H => ?_⟩
  obtain ⟨A, hA⟩ := brc_main X G x hX H
  have h1 : ∀ γ, X.IsPath x γ x →
      H.toFun γ = 1 * ((holF X G x).obj ⟨A⟩).toFun γ * 1⁻¹ := by
    intro γ hγ
    show H.toFun γ = 1 * hol X G A γ * 1⁻¹
    rw [hA γ hγ]; group
  have h2 : ∀ γ, X.IsPath x γ x →
      ((holF X G x).obj ⟨A⟩).toFun γ = 1 * H.toFun γ * 1⁻¹ := by
    intro γ hγ
    show hol X G A γ = 1 * H.toFun γ * 1⁻¹
    rw [hA γ hγ]; group
  let f : (holF X G x).obj ⟨A⟩ ⟶ H := ⟨1, h1⟩
  let k : H ⟶ (holF X G x).obj ⟨A⟩ := ⟨1, h2⟩
  exact ⟨⟨A⟩, ⟨Iso.mk f k (Subtype.ext (mul_one _)) (Subtype.ext (mul_one _))⟩⟩

theorem heq_main (X : Graph) (G : Type) [Group G] (x : Fin X.nV)
    (hX : X.Connected x) :
    (holF X G x).Full ∧ (holF X G x).Faithful ∧ (holF X G x).EssSurj :=
  ⟨hfu_main X G x hX, hff_main X G x hX, heq_essSurj X G x hX⟩

end GaugeFunctor

open GaugeFunctor

theorem solution (X : Graph) (G : Type) [Group G] (x : Fin X.nV)
    (hX : X.Connected x) :
    (holF X G x).Full ∧ (holF X G x).Faithful ∧ (holF X G x).EssSurj :=
  heq_main X G x hX
