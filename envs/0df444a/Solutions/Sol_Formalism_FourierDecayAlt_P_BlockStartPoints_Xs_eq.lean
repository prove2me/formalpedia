-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BlockStartPoints.Xs_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:26.603857+00:00
-- url     : https://prove2.me/submissions/b30a9c2f-fcdf-4f45-b726-50ac854d80b7

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockStartPoints
import Theorems.Thm_Formalism_FourierDecayAlt_P_BlockStartPoints_mem_X_join

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BlockStartPoints
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
open Classical
noncomputable section
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.BlockStartPoints
theorem _root_.solution (T : Tower E) (i s : ℕ) (hs : 1 ≤ s) (hsi : s ≤ i) :
    Xs T i s = pts (T.X (i - s)) s (T.Sg (i - s + 1) s) := by
  ext p
  simp only [Xs, pts, mem_filter, mem_image, mem_product, Prod.exists]
  constructor
  · rintro ⟨hp, hl⟩
    rcases List.eq_nil_or_concat p with rfl | ⟨h, x, rfl⟩
    · simp at hl
    · obtain ⟨s', t⟩ := x
      have hss : s' = s := by simpa using hl
      subst hss
      rw [List.concat_eq_append] at hp
      obtain ⟨h1, h2, h3, h4⟩ := (mem_X_join T h s' t i).1 hp
      have hlev : level h = i - s' := by omega
      refine ⟨h, t, ⟨?_, ?_⟩, by rw [List.concat_eq_append]; rfl⟩
      · rw [← hlev]; exact h2
      · rw [← hlev]; exact h4
  · rintro ⟨h, t, ⟨hh, ht⟩, rfl⟩
    have hlev : level h = i - s := ((T.isTower _ _).1 hh).1
    exact ⟨(mem_X_join T h s t i).2 ⟨by omega, by rw [hlev]; exact hh, hs, by rw [hlev]; exact ht⟩,
      by simp [join]⟩
end Formalism.FourierDecayAlt.P.BlockStartPoints
