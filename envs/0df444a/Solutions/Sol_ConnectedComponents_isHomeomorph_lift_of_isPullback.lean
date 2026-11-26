-- Prove2me | solution 1 for ConnectedComponents.isHomeomorph_lift_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T19:42:49.834835+00:00
-- url     : https://prove2.me/submissions/25078a4d-5b77-4f90-a0de-75b9fc96f6ac

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Inseparable
import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Sober
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.Prespectral
import Definitions.Def_ProEtale_Mathlib_Topology_Category_TopCat_Limits_Pullbacks
import Definitions.Def_ProEtale_Mathlib_Topology_Connected_TotallyDisconnected
import Definitions.Def_ProEtale_Mathlib_Topology_Inseparable
import Definitions.Def_ProEtale_Mathlib_Topology_QuasiSeparated
import Definitions.Def_ProEtale_Mathlib_Topology_Separation_Hausdorff
import Definitions.Def_ProEtale_Mathlib_Topology_Sober
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Basic
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Prespectral
import Definitions.Def_ProEtale_Topology_Preliminaries_Profinite
import Definitions.Def_ProEtale_Topology_Preliminaries_Pullback
import Definitions.Def_ProEtale_Topology_SpectralSpace_ConnectedComponent
import Theorems.Thm_CategoryTheory_IsPullback_compactSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

/-!
# Connected Component in Spectral Space

Profiniteness is expressed as [TopologicalSpace X] [CompactSpace X] [T2Space X]
[TotallyDisconnectedSpace X]

-/

universe u

variable {X : Type u} [TopologicalSpace X]


section Spectral

variable [SpectralSpace X]

open CategoryTheory TopCat Continuous Limits


@[stacks 096C "first part"]
theorem ConnectedComponents.isHomeomorph_lift_of_isPullback {Y T : Type u} [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    IsHomeomorph (connectedComponentsLift g.2) :=
  let _ := IsPullback.compactSpace pb
  (isHomeomorph_iff_continuous_bijective (X := ConnectedComponents Y) (Y := T)).mpr
    ⟨connectedComponentsLift_continuous g.2, lift_bijective_of_isPullback pb⟩

end Spectral


theorem solution.{sol_u1} : type_of% @ConnectedComponents.isHomeomorph_lift_of_isPullback.{sol_u1} := @ConnectedComponents.isHomeomorph_lift_of_isPullback.{sol_u1}
