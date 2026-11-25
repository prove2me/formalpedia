-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.HasWt.natCast_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:49:17.634248+00:00
-- url     : https://prove2.me/submissions/b3471962-9987-44ec-be58-d21eade79ad8

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_IdentityTwentyB
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_C_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_v_natCast_nonneg

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
theorem _root_.solution {l n : ℕ} (hv : v (l : k) = 1) (hd : l ∣ n) (hf : HasWt v r w f) :
    HasWt v r (1 + w) ((n : MvPowerSeries Z k) * f) := by
  have h1 : (n : MvPowerSeries Z k) = C (n : k) := (map_natCast C n).symm
  rw [h1]
  refine hf.C_mul ?_
  obtain ⟨m, rfl⟩ := hd
  push_cast
  rw [v.map_mul, hv]
  have := v_natCast_nonneg v m
  calc (1 : WithTop ℝ) = 1 + 0 := by simp
    _ ≤ 1 + v (m : k) := by gcongr
end HasWt
end Formalism.BaseCaseIdentities
