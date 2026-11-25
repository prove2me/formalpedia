-- Prove2me | solution 1 for Formalism.L2.SG.Pf.GluingBases.isLattice_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:12:59.591406+00:00
-- url     : https://prove2.me/submissions/38d4bd63-aa71-4e08-a8d7-912fcf3bd970

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegOnOfCompl
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LeDualFOfGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.GluingBases
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.SG.Pf.GluingBases
theorem _root_.solution {ι' : Type} [Finite ι'] (β : ι' → V)
    (hβ : Submodule.span K (Set.range β) = ⊤) :
    Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range β)) where
  fg := Submodule.fg_span (Set.finite_range β)
  span_eq_top := by rw [Submodule.span_span_of_tower]; exact hβ
end Formalism.L2.SG.Pf.GluingBases
