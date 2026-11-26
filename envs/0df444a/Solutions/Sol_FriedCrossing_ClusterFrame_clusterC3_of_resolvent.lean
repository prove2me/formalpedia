-- Prove2me | solution 1 for FriedCrossing.ClusterFrame.clusterC3_of_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:16:06.392683+00:00
-- url     : https://prove2.me/submissions/1a1a5ded-086a-4f34-bf09-f58011b8bd44

import Definitions.Def_B1s_resolvent_scale_9_11
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Definitions.Def_B1s_cluster_from_resolvent_9_11
import Theorems.Thm_FriedCrossing_ClusterFrame_contDiff_Mreal

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap MeasureTheory intervalIntegral Scale
open FriedCrossing.ClusterFrame
open ParamInt
variable {S : BanachScale.{0}} (F : ResolventFamily S Param) (Jc : ComplexStructure S)
variable {k : ℕ}
namespace FriedCrossing.ClusterFrame
theorem _root_.solution {S₁ S₂ : BanachScale.{0}}
    (F₁ : ResolventFamily S₁ Param) (J₁ : ComplexStructure S₁) (D₁ : FrameData S₁ 2)
    (F₂ : ResolventFamily S₂ Param) (J₂ : ComplexStructure S₂) (D₂ : FrameData S₂ 4)
    (hdet₁ : ∀ p, (Amat F₁ J₁ D₁ p).det ≠ 0) (hdet₂ : ∀ p, (Amat F₂ J₂ D₂ p).det ≠ 0) :
    Ledger.ClusterC3 (Mreal F₁ J₁ D₁) (Mreal F₂ J₂ D₂) where
  deg1 i j := contDiff_Mreal F₁ J₁ D₁ hdet₁ i j
  deg2 i j := contDiff_Mreal F₂ J₂ D₂ hdet₂ i j
end FriedCrossing.ClusterFrame
