-- Prove2me | solution 1 for Formalism.L2.Pj.frChart_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:16:57.307029+00:00
-- url     : https://prove2.me/submissions/b9024785-b5da-4c58-a554-05246dc2727e

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnitIndepOfCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Theorems.Thm_Formalism_L2_Pj_chartAt_of_cover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
variable {pts mapR borR}
namespace Formalism.L2.Pj
theorem _root_.solution (hT : MapTrans pts mapR) (hC : MapCancel pts mapR)
    (h : ∀ (S : Type) [CommRing S] [Algebra K S] (w : pts S) (m : Ideal S) [m.IsMaximal],
      ∃ (A : TRing K) (u : pts A.R) (c : A.R →ₐ[K] Localization.AtPrime m),
        IsMonoPt pts mapR u ∧ ChartCls pts mapR w m u c ∧ ChartLoc pts mapR w m A u) :
    FrChart pts mapR := by
  intro S _ _ w m _
  obtain ⟨A, u, c, hu, hcl, hloc⟩ := h S w m
  exact ⟨A, u, c, chartAt_of_cover hT hC hu hcl hloc⟩
end Formalism.L2.Pj
