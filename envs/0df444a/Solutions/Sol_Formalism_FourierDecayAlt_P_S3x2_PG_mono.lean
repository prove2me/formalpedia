-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.PG_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:46:53.132683+00:00
-- url     : https://prove2.me/submissions/d389bedd-a6ed-468a-a3fc-26a213541527

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_mem_PG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x2
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x2
theorem _root_.solution {V W : Subgroup (GL (Fin k) A)} (h : V ≤ W) : PG r V ≤ PG r W := by
  intro g hg
  obtain ⟨n, u, hu, hn, rfl⟩ := (mem_PG _ _).1 hg
  exact (mem_PG _ _).2 ⟨n, u, h hu, hn, rfl⟩
end Formalism.FourierDecayAlt.P.S3x2
