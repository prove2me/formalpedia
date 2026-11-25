-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh.sum_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:00:02.046286+00:00
-- url     : https://prove2.me/submissions/931ed53f-337a-437a-9c44-e877e07b9495

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSPhaseA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.M Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh
theorem _root_.solution (P : M.Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    ∑ i : Fin (P.k - 1), (if (i : ℕ) + 1 = l then 1 else 0) = 1 := by
  rw [Finset.mem_Icc] at hl
  rw [Finset.sum_eq_single ⟨l - 1, by omega⟩]
  · rw [if_pos (by simp; omega)]
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    ext
    simp
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh
