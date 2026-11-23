-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.coeff_PsiPartial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:00.707239+00:00
-- url     : https://prove2.me/submissions/ad3d9262-adb6-4f36-84df-f86924742528

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint

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
noncomputable section
open Classical
variable {k : Type*} [Field k] {Z : Type*} {C : Type*}
open Formalism.BaseCaseIdentities.Data
variable [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution (N : ℕ) (t : C → MvPowerSeries Z k) (b : C) (A : Z →₀ ℕ) :
    coeff A (D.PsiPartial N t b) = coeff A (D.zvec b) -
      ∑ c, ∑ j ∈ Finset.Icc 1 N, D.al c j b * coeff A (t c ^ (D.l ^ j)) := by
  simp only [PsiPartial, map_sub, map_sum, coeff_C_mul]
end Formalism.BaseCaseIdentities.Data
