-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.HasWt.C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:33:34.639534+00:00
-- url     : https://prove2.me/submissions/250181a7-e14f-414b-b818-7e6d290100fd

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_IdentityTwentyB
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
variable {k : Type*} [Field k] {Z : Type*} {v : AddValuation k (WithTop ℝ)}
  {r w w' w1 w2 wa wb a₀ : ℝ} {f g a b : MvPowerSeries Z k}
namespace Formalism.BaseCaseIdentities
namespace HasWt
theorem _root_.solution {x : k} (hx : ((a₀ : ℝ) : WithTop ℝ) ≤ v x) (hf : HasWt v r w f) :
    HasWt v r (a₀ + w) (C x * f) := by
  rw [hasWt_iff] at *
  intro A
  rw [coeff_C_mul, v.map_mul]
  have : ((a₀ + w - ((A.degree : ℕ) : ℝ) * r : ℝ) : WithTop ℝ)
      = ((a₀ : ℝ) : WithTop ℝ) + ((w - ((A.degree : ℕ) : ℝ) * r : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_add]; congr 1; ring
  rw [this]
  exact add_le_add hx (hf A)
end HasWt
end Formalism.BaseCaseIdentities
