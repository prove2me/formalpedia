-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.HasWt.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:33:36.6938+00:00
-- url     : https://prove2.me/submissions/3fb3c21c-d5c2-44e4-b2f1-b40620da7499

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
theorem _root_.solution (hf : HasWt v r w1 f) (hg : HasWt v r w2 g) : HasWt v r (w1 + w2) (f * g) := by
  classical
  rw [hasWt_iff] at *
  intro A
  rw [coeff_mul]
  refine v.map_le_sum fun p hp => ?_
  rw [v.map_mul]
  have hA : A = p.1 + p.2 := (Finset.HasAntidiagonal.mem_antidiagonal.1 hp).symm
  have hd : ((A.degree : ℕ) : ℝ) = ((p.1.degree : ℕ) : ℝ) + ((p.2.degree : ℕ) : ℝ) := by
    rw [hA, map_add]; push_cast; ring
  have : ((w1 + w2 - ((A.degree : ℕ) : ℝ) * r : ℝ) : WithTop ℝ)
      = ((w1 - ((p.1.degree : ℕ) : ℝ) * r : ℝ) : WithTop ℝ)
        + ((w2 - ((p.2.degree : ℕ) : ℝ) * r : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_add, hd]; congr 1; ring
  rw [this]
  exact add_le_add (hf p.1) (hg p.2)
end HasWt
end Formalism.BaseCaseIdentities
