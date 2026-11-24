-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLevelIdx.kset_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:45:18.423891+00:00
-- url     : https://prove2.me/submissions/710aa16e-ef2e-476b-b33c-fe4be9188c50

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelIdx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelIdx
open MeasureTheory Formalism.MainNotions.S Matrix
open scoped ENNReal TensorProduct
variable (I : AutInst)
variable {I}
namespace Formalism.MainNotions.BridgeLevelIdx
theorem _root_.solution {x x' : I.Gf} (hx : x ∈ I.Kset) (hx' : x' ∈ I.Kset) : x⁻¹ * x' ∈ I.Kset := by
  show ((x⁻¹ * x' : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [Subgroup.coe_mul, Subgroup.coe_inv]
  exact (Formalism.UG.stabGL I.Lf).mul_mem ((Formalism.UG.stabGL I.Lf).inv_mem hx) hx'
end Formalism.MainNotions.BridgeLevelIdx
