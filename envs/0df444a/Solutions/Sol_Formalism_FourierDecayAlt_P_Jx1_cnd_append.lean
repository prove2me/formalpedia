-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx1.cnd_append
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:55.997008+00:00
-- url     : https://prove2.me/submissions/51423a1c-0760-4cdb-847e-4b7e8aef5ce7

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsdFormConjRewrite
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_bs_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_bs_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx1
variable {E : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.Jx1
theorem _root_.solution (Sg : ℕ → ℕ → Finset E) (h : TB.Pt E) (s : ℕ) (t : E) :
    Cnd Sg (h ++ [(s, t)]) ↔ Cnd Sg h ∧ 1 ≤ s ∧ t ∈ Sg (TB.level h + 1) s := by
  unfold Cnd
  constructor
  · intro H
    refine ⟨fun k hk => ?_, ?_, ?_⟩
    · have H1 := H k (by simp; omega)
      simp only [List.getElem_append_left hk, bs_left h s t k hk] at H1
      exact H1
    · have H1 := H h.length (by simp)
      simp only [List.getElem_append_right (le_refl _), Nat.sub_self] at H1
      simpa using H1.1
    · have H1 := H h.length (by simp)
      simp only [List.getElem_append_right (le_refl _), Nat.sub_self, bs_last] at H1
      simpa using H1.2
  · rintro ⟨H, h1, h2⟩ k hk
    have hk' : k < h.length + 1 := by simpa using hk
    rcases Nat.lt_or_ge k h.length with hlt | hge
    · simp only [List.getElem_append_left hlt, bs_left h s t k hlt]
      exact H k hlt
    · have hkl : k = h.length := by omega
      subst hkl
      simp only [List.getElem_append_right (le_refl _), Nat.sub_self, bs_last]
      simpa using ⟨h1, h2⟩
end Formalism.FourierDecayAlt.P.Jx1
