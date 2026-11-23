-- Prove2me | solution 1 for Formalism.L2.Pj.spMap_dual_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:49.467535+00:00
-- url     : https://prove2.me/submissions/bc64b831-d91b-4d29-8a8d-dff24d2d7283

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnitIndepOfCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Theorems.Thm_Formalism_L2_Pj_dualMap_comp

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
namespace Formalism.L2.Pj
theorem _root_.solution {K : Type} [Field K] {S T U : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T]
    [CommRing U] [Algebra K U] (φ : S →ₐ[K] T) (ψ : T →ₐ[K] U) :
    spMap (dualMap (ψ.comp φ).toRingHom) = spMap (dualMap ψ.toRingHom) ≫ spMap (dualMap φ.toRingHom) := by
  have e : (ψ.comp φ).toRingHom = ψ.toRingHom.comp φ.toRingHom := rfl
  rw [e, dualMap_comp]
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
end Formalism.L2.Pj
