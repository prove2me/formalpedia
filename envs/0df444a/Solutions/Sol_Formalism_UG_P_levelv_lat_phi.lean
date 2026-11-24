-- Prove2me | solution 1 for Formalism.UG.P.levelv_lat_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:38:54.806577+00:00
-- url     : https://prove2.me/submissions/46b20d2e-a2f5-4f09-b00a-5c1655cf8578

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
import Theorems.Thm_Formalism_UG_P_levelv_S_le_range
import Theorems.Thm_Formalism_UG_P_levelv_mem_lat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
open IsDedekindDomain NumberField
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (x : n → E ⊗[F] v.adicCompletion F)
    (hx : x ∈ stdLat (n := n) ↥(lvS F E v)) : ∃ α, levelvPhi F E v n α = x := by
  rw [levelv_mem_lat] at hx
  choose α hα using fun j => AddMonoidHom.mem_range.mp (levelv_S_le_range v (x j) (hx j))
  exact ⟨α, funext fun j => hα j⟩
end Formalism.UG.P
