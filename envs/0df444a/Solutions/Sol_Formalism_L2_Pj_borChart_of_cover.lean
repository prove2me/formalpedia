-- Prove2me | solution 1 for Formalism.L2.Pj.borChart_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:16:59.26319+00:00
-- url     : https://prove2.me/submissions/d6dbf828-5b26-488c-965f-5c611c244bd4

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
theorem _root_.solution (hT : MapTrans pts mapR) (hC : MapCancel pts mapR) (hB : BorBC pts mapR borR)
    (h : ∀ (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ) (w w' : pts S), borR t w w' →
      ∀ (m : Ideal S) [m.IsMaximal],
      ∃ (A : TRing K) (u : pts A.R) (c c' : A.R →ₐ[K] Localization.AtPrime m),
        IsMonoPt pts mapR u ∧ BorOver pts mapR borR A u ∧ ChartCls pts mapR w m u c ∧ ChartLoc pts mapR w m A u ∧
          ChartCls pts mapR w' m u c' ∧ ChartLoc pts mapR w' m A u) :
    BorChart pts mapR borR := by
  intro S _ _ t w w' hb m _
  obtain ⟨A, u, c, c', hu, hBo, hcl, hloc, hcl', hloc'⟩ := h S t w w' hb m
  obtain ⟨B, uB, uB', tB, π, π', hπ, hπ', hbB, huniv⟩ := hBo
  have ch := chartAt_of_cover hT hC hu hcl hloc
  have ch' := chartAt_of_cover hT hC hu hcl' hloc'
  obtain ⟨wm, hwm, hc⟩ := hcl
  obtain ⟨wm', hwm', hc'⟩ := hcl'
  have hbm := hB S _ (locM K m) t w w' wm wm' hb hwm hwm'
  obtain ⟨cB, e1, e2, e3⟩ := huniv _ c c' wm wm' _ hc hc' hbm
  refine ⟨A, u, c, c', B, uB, uB', tB, π, π', cB, ch, ch', hπ, hπ', hbB, e1, e2, fun i => ?_⟩
  rw [e3 i]
  rfl
end Formalism.L2.Pj
