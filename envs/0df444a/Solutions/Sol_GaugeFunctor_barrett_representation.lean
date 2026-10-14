-- Prove2me | solution 1 for GaugeFunctor.barrett_representation
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-11T20:25:56.04802+00:00
-- url     : https://prove2.me/submissions/08c224e0-0743-4287-879f-5b93162d9eac

import Mathlib
import Definitions.Def_GaugeFunctor_defs

open CategoryTheory

namespace GaugeFunctor

theorem brp_isPath_append (X : Graph) : ∀ (w w' : List X.Step) (x y z : Fin X.nV),
    X.IsPath x w y → X.IsPath y w' z → X.IsPath x (w ++ w') z
  | [], w', x, y, z, h, h' => by
      simp only [Graph.IsPath] at h; subst h; simpa using h'
  | s :: w, w', x, y, z, h, h' => by
      simp only [Graph.IsPath] at h
      exact ⟨h.1, brp_isPath_append X w w' _ y z h.2 h'⟩

theorem brp_isPath_rev (X : Graph) : ∀ (w : List X.Step) (x y : Fin X.nV),
    X.IsPath x w y → X.IsPath y (w.reverse.map X.flip) x
  | [], x, y, h => by
      simp only [Graph.IsPath] at h; subst h; simp [Graph.IsPath]
  | s :: w, x, y, h => by
      simp only [Graph.IsPath] at h
      obtain ⟨hs, hw⟩ := h
      have ih := brp_isPath_rev X w _ y hw
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
      refine brp_isPath_append X _ _ y _ x ih ?_
      subst hs
      rcases s with ⟨e, b⟩
      cases b <;> simp [Graph.IsPath, Graph.flip, Graph.stepSrc, Graph.stepTgt]

theorem brp_hol_rev (X : Graph) (G : Type) [Group G] (A : Fin X.nE → G) :
    ∀ w : List X.Step, hol X G A (w.reverse.map X.flip) = (hol X G A w)⁻¹
  | [] => by simp [hol]
  | s :: w => by
      have ih := brp_hol_rev X G A w
      have hs : stepHol X G A (X.flip s) = (stepHol X G A s)⁻¹ := by
        rcases s with ⟨e, b⟩; cases b <;> simp [stepHol, Graph.flip]
      have h1 : hol X G A (s :: w) = stepHol X G A s * hol X G A w := by simp [hol]
      have h2 : hol X G A [X.flip s] = stepHol X G A (X.flip s) := by simp [hol]
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, hol_append]
      rw [ih, h1, h2, hs, mul_inv_rev]

theorem brp_main (X : Graph) (G : Type) [Group G] (x : Fin X.nV)
    (hX : X.Connected x) (A B : Fin X.nE → G) :
    (∀ γ, X.IsPath x γ x → hol X G A γ = hol X G B γ) ↔
      ∃! g : Fin X.nV → G, g x = 1 ∧ gaugeAct X G g A = B := by
  constructor
  · intro hAB
    choose w hw using (hX : ∀ y, ∃ w, X.IsPath x w y)
    have hf : ∀ γ, X.IsPath x γ x → hol X G B γ = hol X G A γ :=
      fun γ h => (hAB γ h).symm
    let g : Fin X.nV → G := fun y => (hol X G B (w y))⁻¹ * hol X G A (w y)
    have hgx : g x = 1 := by
      show (hol X G B (w x))⁻¹ * hol X G A (w x) = 1
      rw [hf (w x) (hw x)]; group
    have hg : gaugeAct X G g A = B := by
      funext e
      have hstep : X.IsPath (X.src e) [(e, true)] (X.tgt e) := by
        simp [Graph.IsPath, Graph.stepSrc, Graph.stepTgt]
      have hp : X.IsPath x
          (w (X.src e) ++ [(e, true)] ++ (w (X.tgt e)).reverse.map X.flip) x :=
        brp_isPath_append X _ _ x (X.tgt e) x
          (brp_isPath_append X _ _ x (X.src e) (X.tgt e) (hw _) hstep)
          (brp_isPath_rev X _ x _ (hw _))
      have key := hf _ hp
      have he : ∀ C : Fin X.nE → G, hol X G C [(e, true)] = C e := by
        intro C; simp [hol, stepHol]
      simp only [hol_append, brp_hol_rev, he] at key
      show (hol X G B (w (X.src e)))⁻¹ * hol X G A (w (X.src e)) * A e *
        ((hol X G B (w (X.tgt e)))⁻¹ * hol X G A (w (X.tgt e)))⁻¹ = B e
      generalize hol X G B (w (X.src e)) = bu at key ⊢
      generalize hol X G B (w (X.tgt e)) = bv at key ⊢
      generalize hol X G A (w (X.src e)) = au at key ⊢
      generalize hol X G A (w (X.tgt e)) = av at key ⊢
      rw [show B e = bu⁻¹ * (bu * B e * bv⁻¹) * bv by group, key]
      group
    refine ⟨g, ⟨hgx, hg⟩, ?_⟩
    rintro g' ⟨hg'x, hg'⟩
    funext y
    have h1 := hol_gaugeAct (X := X) (G := G) g A (w y) x y (hw y)
    have h2 := hol_gaugeAct (X := X) (G := G) g' A (w y) x y (hw y)
    rw [hg] at h1
    rw [hg', hg'x, h1, hgx] at h2
    exact (inv_injective (mul_left_cancel h2)).symm
  · rintro ⟨g, ⟨hgx, hg⟩, -⟩ γ hγ
    have h := hol_gaugeAct (X := X) (G := G) g A γ x x hγ
    rw [hg, hgx] at h
    rw [h]; group

end GaugeFunctor

open GaugeFunctor

theorem solution (X : Graph) (G : Type) [Group G] (x : Fin X.nV)
    (hX : X.Connected x) (A B : Fin X.nE → G) :
    (∀ γ, X.IsPath x γ x → hol X G A γ = hol X G B γ) ↔
      ∃! g : Fin X.nV → G, g x = 1 ∧ gaugeAct X G g A = B := brp_main X G x hX A B
