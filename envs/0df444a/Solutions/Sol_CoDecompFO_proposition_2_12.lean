-- Prove2me | solution 1 for CoDecompFO.proposition_2_12
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:40:28.305102+00:00
-- url     : https://prove2.me/submissions/e7fe2670-2dc5-4ec2-820f-4201ca8fd5dd

import Definitions.Def_CoDecompFO_Lim

open CoDecompFO FirstOrder in
theorem solution {σ : Sig} (T : CoDecomp σ) (H : Type) [σ.lang.Structure H]
    (φt : (t : Fin T.b) → H → Fin (T.bag t).n) (φe : (e : Fin T.m) → H → Fin (T.adh e).n)
    (ht : ∀ t, IsHom σ (φt t)) (he : ∀ e, IsHom σ (φe e))
    (hl : ∀ e, φe e = T.gl e ∘ φt (T.ends e).1) (hr : ∀ e, φe e = T.gr e ∘ φt (T.ends e).2) :
    ∃! u : H →[σ.lang] T.Lim,
      (∀ t x, (u x).val t = φt t x) ∧ (∀ e x, CoDecomp.Lim.edgeProj e (u x) = φe e x) := by
  let f : H → T.Lim := fun x =>
    ⟨fun t => φt t x, fun e => by
      have h1 := congrFun (hl e) x
      have h2 := congrFun (hr e) x
      simp only [Function.comp] at h1 h2
      rw [← h1, ← h2]⟩
  let u : H →[σ.lang] T.Lim :=
    { toFun := f
      map_fun' := fun g => Empty.elim g
      map_rel' := by
        rintro n ⟨i, rfl⟩ x hx t
        exact ht t i x hx }
  refine ⟨u, ⟨fun t x => rfl, fun e x => ?_⟩, ?_⟩
  · show T.gl e (φt (T.ends e).1 x) = φe e x
    rw [hl e]; rfl
  · rintro u' ⟨h1, -⟩
    apply FirstOrder.Language.Hom.ext
    intro x
    apply CoDecomp.Lim.ext
    funext t
    exact h1 t x
