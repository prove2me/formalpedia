-- Prove2me | solution 1 for Formalism.L2.Pj.chartAt_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:45.257465+00:00
-- url     : https://prove2.me/submissions/93878d21-82ba-4546-82dc-e9138644a1f6

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnitIndepOfCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts

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
theorem _root_.solution (hT : MapTrans pts mapR) (hC : MapCancel pts mapR) {S : Type} [CommRing S] [Algebra K S]
    {w : pts S} {m : Ideal S} [m.IsPrime] {A : TRing K} {u : pts A.R} {c : A.R →ₐ[K] Localization.AtPrime m}
    (hu : IsMonoPt pts mapR u) (hcl : ChartCls pts mapR w m u c) (hloc : ChartLoc pts mapR w m A u) :
    FrChartAt pts mapR w m A u c := by
  obtain ⟨wm, hwm, hc⟩ := hcl
  intro p φ y hy
  obtain ⟨g, hg, p', lam, y', a, hlam, h1, h2⟩ := hloc p φ y hy
  have hunit : IsUnit (((locM K m).comp φ) g) :=
    IsLocalization.map_units (Localization.AtPrime m) (⟨φ g, hg⟩ : m.primeCompl)
  obtain ⟨μ, hμ⟩ := hlam (Localization.AtPrime m) ((locM K m).comp φ) hunit
  refine ⟨p', lam, a, μ, y', h1, h2, hμ, ?_⟩
  have h3 : mapR (μ.comp lam) y wm := by
    rw [hμ]
    exact hT _ _ _ φ (locM K m) y w wm hy hwm
  have h4 : mapR μ y' wm := hC _ _ _ lam μ y y' wm h1 h3
  exact hu _ (μ.comp a) c wm (hT _ _ _ a μ u y' wm h2 h4) hc
end Formalism.L2.Pj
