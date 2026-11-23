-- Prove2me | solution 1 for Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.natCast_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:40.852468+00:00
-- url     : https://prove2.me/submissions/9e85b173-8580-4365-a86c-f6a1dee402fb

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
open Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
theorem _root_.solution (N : Submodule (𝓞 K) V) (g : ℕ) {x : V} (hx : x ∈ N) :
    (g : K) • x ∈ N := by
  rw [Nat.cast_smul_eq_nsmul]
  exact N.nsmul_mem hx g
end Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
