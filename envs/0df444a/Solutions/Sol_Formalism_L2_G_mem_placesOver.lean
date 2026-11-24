-- Prove2me | solution 1 for Formalism.L2.G.mem_placesOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:10:29.966812+00:00
-- url     : https://prove2.me/submissions/1d1e8ac6-bcc2-4e7a-9e49-746d6fc116b5

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_SignBlockDeterminant
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_AtGGlob
import Theorems.Thm_Formalism_L2_G_finite_placesOver

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
variable (F : Type) [Field F] [NumberField F]
namespace Formalism.L2.G
theorem _root_.solution (g : ℕ) (hg : g ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ placesOver F g ↔ ((g : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  rw [placesOver, dif_pos (finite_placesOver F g hg)]
  simp
end Formalism.L2.G
