-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.fdeg_eq_inertiaDeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:59.22569+00:00
-- url     : https://prove2.me/submissions/0aef6230-a77b-4ddc-bab1-84e888e7392e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable (A : Type*) [CommRing A] [Algebra O A]
variable {O A}
attribute [instance] IsDVRAt.isDomain IsDVRAt.isDVR
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution (ζ : Pts O A) : fdeg ζ = ζ.asIdeal.inertiaDeg O := by
  have : ζ.asIdeal.LiesOver (maximalIdeal O) := ⟨(comap_eq_maximalIdeal ζ).symm⟩
  let _ : Algebra (O ⧸ maximalIdeal O) (ResidueField O) :=
    show Algebra (O ⧸ maximalIdeal O) (O ⧸ maximalIdeal O) from Algebra.id _
  have : IsFractionRing (O ⧸ maximalIdeal O) (ResidueField O) := by
    let _ : Field (O ⧸ maximalIdeal O) := Ideal.Quotient.field _
    show IsFractionRing (O ⧸ maximalIdeal O) (O ⧸ maximalIdeal O)
    infer_instance
  have : IsScalarTower O (O ⧸ maximalIdeal O) (ResidueField O) :=
    show IsScalarTower O (O ⧸ maximalIdeal O) (O ⧸ maximalIdeal O) from inferInstance
  exact (Ideal.inertiaDeg_eq_of_isFractionRing (maximalIdeal O) ζ.asIdeal (ResidueField O)
    (ResidueField (Loc ζ))).symm
end Formalism.MainNotions.Gaps.EtaleWeightGaps
