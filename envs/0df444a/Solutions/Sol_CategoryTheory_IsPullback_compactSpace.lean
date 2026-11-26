-- Prove2me | solution 1 for CategoryTheory.IsPullback.compactSpace
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T19:42:12.43411+00:00
-- url     : https://prove2.me/submissions/ad4793d4-454e-4b01-a631-52df9c171bc6

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Inseparable
import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sober
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.Prespectral
import Definitions.Def_ProEtale_Mathlib_Topology_Category_TopCat_Limits_Pullbacks
import Definitions.Def_ProEtale_Mathlib_Topology_Inseparable
import Definitions.Def_ProEtale_Mathlib_Topology_QuasiSeparated
import Definitions.Def_ProEtale_Mathlib_Topology_Separation_Hausdorff
import Definitions.Def_ProEtale_Mathlib_Topology_Sober
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Basic
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Prespectral
import Definitions.Def_ProEtale_Topology_Preliminaries_Pullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe u

open CategoryTheory TopCat Limits

variable {X Y S : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace S]
variable (f : C(X, S)) (g : C(Y, S))

variable {P : Type u} [TopologicalSpace P] {f' : C(P, Y)} {g' : C(P, X)}
    (pb : IsPullback (ofHom g') (ofHom f') (ofHom f) (ofHom g))


section IsPullback

variable {f g}

include f' g' pb


variable [T2Space S]


theorem CategoryTheory.IsPullback.compactSpace [CompactSpace X] [CompactSpace Y] : CompactSpace P :=
  (homeoOfIso pb.isoPullback).symm.compactSpace


end IsPullback


theorem solution.{sol_u1} : type_of% @CategoryTheory.IsPullback.compactSpace.{sol_u1} := @CategoryTheory.IsPullback.compactSpace.{sol_u1}
