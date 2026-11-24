-- Prove2me | solution 1 for Formalism.L2.G.mem_JU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:01:31.525882+00:00
-- url     : https://prove2.me/submissions/4ef37126-e692-4186-80c8-2f4b2ef7eb59

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_SignBlockDeterminant
import Theorems.Thm_Formalism_L2_G_toFr_apply

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
theorem _root_.solution (a t : ℕ) (fixLast : Bool) (fc : ℕ) (x : GL (Fin N) (E ⊗[F] v.adicCompletion F)) :
    x ∈ JU σE J v spl fr a t fixLast fc ↔ x ∈ UPts σE J (v.adicCompletion F) ∧
      fr⁻¹ * bc ((RingHom.fst _ _).comp spl.toRingHom) x * fr ∈ JLoc F v N a t fixLast fc := by
  rw [JU, Subgroup.mem_inf, Subgroup.mem_comap, toFr_apply]
end Formalism.L2.G
