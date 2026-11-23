-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TA2.isPt_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:59.71905+00:00
-- url     : https://prove2.me/submissions/fb181e28-2c53-42ec-9f7e-afe7e5a58649

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OffDiagonalSchurComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TA2
namespace Formalism.FourierDecayAlt.P.TA2
theorem _root_.solution {E : Type} [Zero E] {i s : ℕ} (hs : 1 ≤ s) (hsi : s ≤ i) {h : Pt E} {t : E}
    (hh : IsPt (i - s) h) (ht : t ≠ 0) : IsPt i (ext h s t) := by
  refine ⟨?_, ?_⟩
  · have := hh.1
    simp only [lvl] at this
    simp [lvl, Formalism.FourierDecayAlt.TA.ext, this]; omega
  · intro b hb
    simp only [Formalism.FourierDecayAlt.TA.ext, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact hh.2 b hb
    · exact ⟨hs, ht⟩
end Formalism.FourierDecayAlt.P.TA2
