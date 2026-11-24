-- Prove2me | solution 1 for Formalism.L2.SG.LsDatumA.sub_mem_X_of_mkW_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:17:45.267452+00:00
-- url     : https://prove2.me/submissions/38689088-5652-47e4-8a9e-63d6c714441d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_LinQRawRange
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_LsDatumA
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.LsDatumA
open Formalism.MainNotions.S.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
namespace Formalism.L2.SG.LsDatumA
theorem _root_.solution {r : ℕ} {f : Fin (r + 1) → V} {x y : ↥(H.perp (H.X f))}
    (h : H.mkW f x = H.mkW f y) : (x : V) - y ∈ H.X f := by
  have h' := (Submodule.Quotient.eq _).mp h
  simpa using h'
end Formalism.L2.SG.LsDatumA
