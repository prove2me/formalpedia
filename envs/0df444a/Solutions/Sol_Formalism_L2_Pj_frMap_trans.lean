-- Prove2me | solution 1 for Formalism.L2.Pj.frMap_trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:59.115176+00:00
-- url     : https://prove2.me/submissions/271b6dd8-706e-46c6-ad26-d4ca04247e32

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnitIndepOfCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Theorems.Thm_Formalism_L2_Pj_spMap_algHom_comp
import Theorems.Thm_Formalism_L2_Pj_spMap_dual_comp
import Theorems.Thm_Formalism_L2_Pj_ppx_le_cov

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {c : Coeff l}
namespace Formalism.L2.Pj
theorem _root_.solution : MapTrans (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) := by
  intro S T U _ _ _ _ _ _ φ ψ y z w h₁ h₂
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  refine ⟨?_, ?_, pm2 ≫ pm1, ?_, ?_, ?_⟩
  · rw [hx2, hx1, spMap_algHom_comp, Category.assoc]
  · intro τ i
    rw [hu2 τ i, hu1 τ i, spMap_dual_comp, Category.assoc]
  · rw [Category.assoc, hs1, hs2]
  · rw [Category.assoc, hf1, ← Category.assoc, hf2, Category.assoc, spMap_algHom_comp]
  · intro i h
    have h1' := ppx_le_cov pm1 hs1 i
    have h2' := ppx_le_cov pm2 hs2 i
    have e : (pm2 ≫ pm1).appLE _ _ h = pm1.appLE _ _ h1' ≫ pm2.appLE _ _ h2' :=
      (Scheme.Hom.appLE_comp_appLE pm2 pm1 _ _ _ h1' h2').symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, ha1 i h1', ha2 i h2']
end Formalism.L2.Pj
