-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.mem_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:34.832785+00:00
-- url     : https://prove2.me/submissions/621e6816-51dc-43e6-b2e3-48fff636f114

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
variable {E : Type} [Field E] [DecidableEq E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
theorem _root_.solution (Sg : ℕ → ℕ → Finset E) (i s : ℕ) (hs : 1 ≤ s) (hsi : s ≤ i) (h : Pt E) (t : E) :
    TA.ext h s t ∈ PT Sg i ↔ h ∈ PT Sg (i - s) ∧ t ∈ Sg i s := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  simp only [PT, Finset.mem_biUnion, Finset.mem_attach, true_and, Finset.mem_image]
  constructor
  · rintro ⟨a, h', hh', t', ht', he⟩
    have hlt := Finset.mem_range.mp a.2
    unfold TA.ext at he
    obtain ⟨h1, h2⟩ := List.append_inj' he rfl
    have h3 : n + 1 - a.1 = s ∧ t' = t := by simpa using h2
    have ha : a.1 = n + 1 - s := by omega
    rw [← h1, ← h3.2, ← ha, ← h3.1]
    exact ⟨hh', ht'⟩
  · rintro ⟨hh, ht⟩
    have ha : n + 1 - s ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have e : n + 1 - (n + 1 - s) = s := by omega
    refine ⟨⟨n + 1 - s, ha⟩, h, hh, t, ?_, ?_⟩
    · simp only [e]
      exact ht
    · simp only [e]
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
