-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z3.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:40:50.22108+00:00
-- url     : https://prove2.me/submissions/abd760a1-d0c0-4d5b-a9c0-b929dc0bc049

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z3
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {P : Submodule K V} {S : Subring K} {M M₁ M₂ : AddSubgroup V}
namespace Formalism.L2.SG.Pf.LatDictZ.Z3
theorem _root_.solution {Q : Submodule K V} (hc : IsCompl P Q) (v : V) : ∃ a ∈ P, ∃ b ∈ Q, a + b = v :=
  Submodule.mem_sup.mp (by rw [hc.sup_eq_top]; trivial)
end Formalism.L2.SG.Pf.LatDictZ.Z3
