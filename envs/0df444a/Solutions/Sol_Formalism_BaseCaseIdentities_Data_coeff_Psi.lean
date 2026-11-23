-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.coeff_Psi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:32.382869+00:00
-- url     : https://prove2.me/submissions/20c4dbb5-2de4-41d5-bf1b-58bf052fa187

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
theorem _root_.solution (t : C → MvPowerSeries Z k) (b : C) (A : Z →₀ ℕ) :
    coeff A (D.Psi t b) = coeff A (D.zvec b) -
      ∑ c, ∑ j ∈ Finset.Icc 1 A.degree, D.al c j b * coeff A (t c ^ (D.l ^ j)) := rfl
end Formalism.BaseCaseIdentities.Data
