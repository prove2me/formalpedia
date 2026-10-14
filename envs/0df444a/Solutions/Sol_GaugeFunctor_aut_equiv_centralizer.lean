-- Prove2me | solution 1 for GaugeFunctor.aut_equiv_centralizer
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-11T20:48:57.963519+00:00
-- url     : https://prove2.me/submissions/fa954ef7-0464-47fc-878e-379e7667b891

import Mathlib
import Definitions.Def_GaugeFunctor_defs

open CategoryTheory

namespace GaugeFunctor

theorem aec_isPath_append (X : Graph) : ∀ (w w' : List X.Step) (x y z : Fin X.nV),
    X.IsPath x w y → X.IsPath y w' z → X.IsPath x (w ++ w') z
  | [], w', x, y, z, h, h' => by
      simp only [Graph.IsPath] at h; subst h; simpa using h'
  | s :: w, w', x, y, z, h, h' => by
      simp only [Graph.IsPath] at h
      exact ⟨h.1, aec_isPath_append X w w' _ y z h.2 h'⟩

theorem aec_isPath_rev (X : Graph) : ∀ (w : List X.Step) (x y : Fin X.nV),
    X.IsPath x w y → X.IsPath y (w.reverse.map X.flip) x
  | [], x, y, h => by
      simp only [Graph.IsPath] at h; subst h; simp [Graph.IsPath]
  | s :: w, x, y, h => by
      simp only [Graph.IsPath] at h
      obtain ⟨hs, hw⟩ := h
      have ih := aec_isPath_rev X w _ y hw
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
      refine aec_isPath_append X _ _ y _ x ih ?_
      subst hs
      rcases s with ⟨e, b⟩
      cases b <;> simp [Graph.IsPath, Graph.flip, Graph.stepSrc, Graph.stepTgt]

theorem aec_hol_rev (X : Graph) (G : Type) [Group G] (A : Fin X.nE → G) :
    ∀ w : List X.Step, hol X G A (w.reverse.map X.flip) = (hol X G A w)⁻¹
  | [] => by simp [hol]
  | s :: w => by
      have ih := aec_hol_rev X G A w
      have hs : stepHol X G A (X.flip s) = (stepHol X G A s)⁻¹ := by
        rcases s with ⟨e, b⟩; cases b <;> simp [stepHol, Graph.flip]
      have h1 : hol X G A (s :: w) = stepHol X G A s * hol X G A w := by simp [hol]
      have h2 : hol X G A [X.flip s] = stepHol X G A (X.flip s) := by simp [hol]
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, hol_append]
      rw [ih, h1, h2, hs, mul_inv_rev]

theorem aec_main (X : Graph) (G : Type) [Group G] (x : Fin X.nV)
    (hX : X.Connected x) (A : Fin X.nE → G) :
    ∃ e : {g : Fin X.nV → G // gaugeAct X G g A = A} ≃
        {h : G // ∀ γ, X.IsPath x γ x → Commute h (hol X G A γ)},
      ∀ g, (e g).1 = g.1 x := by
  let F : {g : Fin X.nV → G // gaugeAct X G g A = A} →
      {h : G // ∀ γ, X.IsPath x γ x → Commute h (hol X G A γ)} := fun g =>
    ⟨g.1 x, fun γ hγ => by
      have h1 := hol_gaugeAct (X := X) (G := G) g.1 A γ x x hγ
      rw [g.2] at h1
      show g.1 x * hol X G A γ = hol X G A γ * g.1 x
      calc g.1 x * hol X G A γ = g.1 x * hol X G A γ * (g.1 x)⁻¹ * g.1 x := by group
        _ = hol X G A γ * g.1 x := by rw [← h1]⟩
  have hinj : Function.Injective F := by
    intro g g' hgg
    have hx : g.1 x = g'.1 x := congrArg Subtype.val hgg
    apply Subtype.ext
    funext y
    obtain ⟨w, hw⟩ := hX y
    have h1 := hol_gaugeAct (X := X) (G := G) g.1 A w x y hw
    have h2 := hol_gaugeAct (X := X) (G := G) g'.1 A w x y hw
    rw [g.2] at h1
    rw [g'.2, ← hx] at h2
    generalize hol X G A w = a at h1 h2
    calc g.1 y = (g.1 x * a * (g.1 y)⁻¹)⁻¹ * g.1 x * a := by group
      _ = (g.1 x * a * (g'.1 y)⁻¹)⁻¹ * g.1 x * a := by rw [← h1, ← h2]
      _ = g'.1 y := by group
  have hsurj : Function.Surjective F := by
    intro f
    choose w hw using (hX : ∀ y, ∃ w, X.IsPath x w y)
    have hf : ∀ γ, X.IsPath x γ x →
        hol X G A γ = f.1 * hol X G A γ * (f.1)⁻¹ := by
      intro γ hγ
      rw [(f.2 γ hγ).eq]; group
    let g : Fin X.nV → G := fun y =>
      (hol X G A (w y))⁻¹ * f.1 * hol X G A (w y)
    have hgx : g x = f.1 := by
      show (hol X G A (w x))⁻¹ * f.1 * hol X G A (w x) = f.1
      rw [mul_assoc, (f.2 (w x) (hw x)).eq, ← mul_assoc, inv_mul_cancel, one_mul]
    have hg : gaugeAct X G g A = A := by
      funext e
      have hstep : X.IsPath (X.src e) [(e, true)] (X.tgt e) := by
        simp [Graph.IsPath, Graph.stepSrc, Graph.stepTgt]
      have hp : X.IsPath x
          (w (X.src e) ++ [(e, true)] ++ (w (X.tgt e)).reverse.map X.flip) x :=
        aec_isPath_append X _ _ x (X.tgt e) x
          (aec_isPath_append X _ _ x (X.src e) (X.tgt e) (hw _) hstep)
          (aec_isPath_rev X _ x _ (hw _))
      have key := hf _ hp
      have he : ∀ C : Fin X.nE → G, hol X G C [(e, true)] = C e := by
        intro C; simp [hol, stepHol]
      simp only [hol_append, aec_hol_rev, he] at key
      show (hol X G A (w (X.src e)))⁻¹ * f.1 * hol X G A (w (X.src e)) * A e *
        ((hol X G A (w (X.tgt e)))⁻¹ * f.1 * hol X G A (w (X.tgt e)))⁻¹ = A e
      generalize hol X G A (w (X.src e)) = au at key ⊢
      generalize hol X G A (w (X.tgt e)) = av at key ⊢
      generalize f.1 = k at key ⊢
      generalize A e = a at key ⊢
      calc au⁻¹ * k * au * a * (av⁻¹ * k * av)⁻¹
          = au⁻¹ * (k * (au * a * av⁻¹) * k⁻¹) * av := by group
        _ = au⁻¹ * (au * a * av⁻¹) * av := by rw [← key]
        _ = a := by group
    exact ⟨⟨g, hg⟩, Subtype.ext hgx⟩
  exact ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, fun g => rfl⟩

end GaugeFunctor

open GaugeFunctor

theorem solution (X : Graph) (G : Type) [Group G] (x : Fin X.nV)
    (hX : X.Connected x) (A : Fin X.nE → G) :
    ∃ e : {g : Fin X.nV → G // gaugeAct X G g A = A} ≃
        {h : G // ∀ γ, X.IsPath x γ x → Commute h (hol X G A γ)},
      ∀ g, (e g).1 = g.1 x := aec_main X G x hX A
