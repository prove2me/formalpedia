-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.B1.join_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:40.17821+00:00
-- url     : https://prove2.me/submissions/3247b163-e84a-4a1b-9437-93f39a2431a8

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
theorem _root_.solution (T : Tower E) {i s : ℕ} (hs : 1 ≤ s) (hsi : s ≤ i) {t : E}
    (ht : t ∈ T.Sg (i - s + 1) s) (h : Pt E) : join h s t ∈ T.X i ↔ h ∈ T.X (i - s) := by
  have E1 : ∀ k (hk' : k < h.length) (hk2 : k < (join h s t).length),
      (join h s t)[k]'hk2 = h[k]'hk' := by
    intro k hk' hk2
    first
    | simp [join, List.getElem_append_left hk']
    | simp [join, List.getElem_append, hk']
  have E2 : ∀ k, k ≤ h.length → blockStart (join h s t) k = blockStart h k := by
    intro k hk'
    simp [blockStart, join, List.take_append_of_le_length hk']
  rw [T.isTower i, T.isTower (i - s)]
  constructor
  · rintro ⟨hl, hk⟩
    have hl' : level h + s = i := by simpa [level, join] using hl
    refine ⟨by omega, fun k hk' => ?_⟩
    have hk2 : k < (join h s t).length := by simp [join]; omega
    have := hk k hk2
    rw [E1 k hk' hk2, E2 k hk'.le] at this
    exact this
  · rintro ⟨hl, hk⟩
    refine ⟨?_, fun k hk2 => ?_⟩
    · simp [level, join] at hl ⊢
      omega
    · by_cases hk' : k < h.length
      · rw [E1 k hk' hk2, E2 k hk'.le]
        exact hk k hk'
      · have hkl : k = h.length := by simp [join] at hk2; omega
        subst hkl
        have e1 : (join h s t)[h.length]'hk2 = (s, t) := by simp [join]
        have e2 : blockStart (join h s t) h.length = level h + 1 := by
          simp [blockStart, join, level, List.take_append_of_le_length (le_refl h.length)]
        rw [e1, e2, hl]
        exact ⟨hs, ht⟩
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
