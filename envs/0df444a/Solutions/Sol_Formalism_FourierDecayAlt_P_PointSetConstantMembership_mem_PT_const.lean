-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PointSetConstantMembership.mem_PT_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:43.965204+00:00
-- url     : https://prove2.me/submissions/b76656a4-8c39-42e5-897a-f18ba8409ee8

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointSetConstantMembership

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PointSetConstantMembership
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate
namespace Formalism.FourierDecayAlt.P.PointSetConstantMembership
theorem _root_.solution {E : Type} [Field E] [DecidableEq E] (T : Finset E) (p : Pt E) :
    ∀ n, IsPt n p → (∀ b ∈ p, b.2 ∈ T) → p ∈ PT (fun _ _ => T) n := by
  induction p using List.reverseRecOn with
  | nil =>
    intro n hp _
    have : n = 0 := by simpa [lvl] using hp.1.symm
    subst this
    simp [PT]
  | append_singleton h b ih =>
    intro n hp hT
    obtain ⟨s, t⟩ := b
    have hs : 1 ≤ s := (hp.2 (s, t) (by simp)).1
    have hl : lvl h + s = n := by
      have := hp.1
      simpa [lvl] using this
    have hh : h ∈ PT (fun _ _ => T) (lvl h) :=
      ih (lvl h) ⟨rfl, fun b hb => hp.2 b (by simp [hb])⟩ (fun b hb => hT b (by simp [hb]))
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [PT]
    simp only [mem_biUnion, mem_attach, true_and, mem_image, Subtype.exists, mem_range]
    refine ⟨lvl h, by omega, h, hh, t, hT (s, t) (by simp), ?_⟩
    have : n' + 1 - lvl h = s := by omega
    rw [this]; rfl
end Formalism.FourierDecayAlt.P.PointSetConstantMembership
