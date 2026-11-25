-- Prove2me | solution 1 for Formalism.L2.SG.Pf.HasProdFiniteSupport.hasProd_of_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:15:57.262546+00:00
-- url     : https://prove2.me/submissions/84b32e24-2ad2-47d2-82da-fc0d3ace580b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_HasProdFiniteSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.HasProdFiniteSupport
open Filter Topology
variable {ι : Type*}
namespace Formalism.L2.SG.Pf.HasProdFiniteSupport
theorem _root_.solution (P : ι → Prop) [DecidablePred P] [Fintype {i // P i}] {f : ι → ℝ} {a : ℝ}
    (h : HasProd (fun i : {i // ¬ P i} => f i) a) : HasProd f (a * ∏ i : {i // P i}, f i) := by
  have h1 : HasProd ({i | ¬ P i}.mulIndicator f) a :=
    (hasProd_subtype_iff_mulIndicator (s := {i | ¬ P i})).mp h
  have h2 : HasProd ({i | P i}.mulIndicator f) (∏ i : {i // P i}, f i) :=
    letI : Fintype ({i | P i} : Set ι) := inferInstanceAs (Fintype {i // P i})
    (hasProd_subtype_iff_mulIndicator (s := {i | P i})).mp (hasProd_fintype _)
  have h3 := h1.mul h2
  convert h3 using 1
  funext i
  by_cases hp : P i <;> simp [Set.mulIndicator, hp]
end Formalism.L2.SG.Pf.HasProdFiniteSupport
