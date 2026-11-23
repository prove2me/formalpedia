-- Prove2me | solution 1 for Formalism.L2.G.toFr_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:12:55.946714+00:00
-- url     : https://prove2.me/submissions/e4690615-46f0-4835-807c-daa4d4c62cda

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_SignBlockDeterminant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.G
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
  (σE : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (v : HeightOneSpectrum (𝓞 F))
  (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) (fr : GL (Fin N) (v.adicCompletion F))
namespace Formalism.L2.G
theorem _root_.solution (x : GL (Fin N) (E ⊗[F] v.adicCompletion F)) :
    toFr v spl fr x = fr⁻¹ * bc ((RingHom.fst _ _).comp spl.toRingHom) x * fr := by
  show (MulAut.conj fr⁻¹) (bc ((RingHom.fst _ _).comp spl.toRingHom) x) = _
  rw [MulAut.conj_apply, inv_inv]
end Formalism.L2.G
