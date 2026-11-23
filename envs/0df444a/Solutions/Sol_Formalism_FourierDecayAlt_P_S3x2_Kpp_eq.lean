-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.Kpp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:01.153686+00:00
-- url     : https://prove2.me/submissions/d51ea991-cbd1-42a8-b84f-c6e9515609d4

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_coe_phi
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isNU_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.S3x2.coe_phi

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x2
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3
variable (o : Type) [CommRing o] [IsLocalRing o]
local notation "𝔽" => IsLocalRing.ResidueField o
variable {o} {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x2
theorem _root_.solution (L : Levels o r k) : L.Kpp = (PG r (upUniG 𝔽 k)).comap (red o (Idx r k)) := by
  ext x
  rw [L.mem_Kpp, Subgroup.mem_comap, isNU_iff]
end Formalism.FourierDecayAlt.P.S3x2
