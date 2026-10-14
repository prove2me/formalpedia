-- Prove2me | solution 1 for GaugeFunctor.holF_full
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-11T20:06:57.18519+00:00
-- url     : https://prove2.me/submissions/d2d2b1ae-97eb-487d-86fe-cb32faaebe93

import Mathlib
import Definitions.Def_GaugeFunctor_defs

open CategoryTheory

namespace GaugeFunctor

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

end GaugeFunctor

open GaugeFunctor

theorem solution (X : Graph) (G : Type) [Group G] (x : Fin X.nV)
    (hX : X.Connected x) : (holF X G x).Full := hfu_main X G x hX
