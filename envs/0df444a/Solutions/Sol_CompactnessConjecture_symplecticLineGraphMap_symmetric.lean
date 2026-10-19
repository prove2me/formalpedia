-- Prove2me | solution 1 for CompactnessConjecture.symplecticLineGraphMap_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/ee9c1a7e-1735-4dc5-925f-830d583d16fa

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticLineGraphMap_horizontal

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    symplecticLineGraphMap K L hvertical ![1, 0] 1 =
      symplecticLineGraphMap K L hvertical ![0, 1] 0 := by
  let u : L.1 :=
    (symplecticLineHorizontalProjectionEquiv K L hvertical).symm
      ![1, 0]
  let v : L.1 :=
    (symplecticLineHorizontalProjectionEquiv K L hvertical).symm
      ![0, 1]
  have hu :
      symplecticHorizontalProjection K
        (u : SymplecticVector K) = ![1, 0] := by
    change
      symplecticLineHorizontalProjectionEquiv K L hvertical u =
        ![1, 0]
    exact
      (symplecticLineHorizontalProjectionEquiv K L hvertical).apply_symm_apply
        ![1, 0]
  have hv :
      symplecticHorizontalProjection K
        (v : SymplecticVector K) = ![0, 1] := by
    change
      symplecticLineHorizontalProjectionEquiv K L hvertical v =
        ![0, 1]
    exact
      (symplecticLineHorizontalProjectionEquiv K L hvertical).apply_symm_apply
        ![0, 1]
  have hu0 : (u : SymplecticVector K) 0 = 1 := by
    simpa [symplecticHorizontalProjection] using congrFun hu 0
  have hu2 : (u : SymplecticVector K) 2 = 0 := by
    simpa [symplecticHorizontalProjection] using congrFun hu 1
  have hv0 : (v : SymplecticVector K) 0 = 0 := by
    simpa [symplecticHorizontalProjection] using congrFun hv 0
  have hv2 : (v : SymplecticVector K) 2 = 1 := by
    simpa [symplecticHorizontalProjection] using congrFun hv 1
  have hu3 :
      (u : SymplecticVector K) 3 =
        symplecticLineGraphMap K L hvertical ![1, 0] 1 := by
    have h := congrFun
      (symplecticLineGraphMap_horizontal K L hvertical u) 1
    rw [hu] at h
    simpa [symplecticVerticalProjection] using h.symm
  have hv1 :
      (v : SymplecticVector K) 1 =
        symplecticLineGraphMap K L hvertical ![0, 1] 0 := by
    have h := congrFun
      (symplecticLineGraphMap_horizontal K L hvertical v) 0
    rw [hv] at h
    simpa [symplecticVerticalProjection] using h.symm
  have hpair := L.2.2
    (u : SymplecticVector K) u.2
    (v : SymplecticVector K) v.2
  have hzero :
      symplecticLineGraphMap K L hvertical ![0, 1] 0 -
        symplecticLineGraphMap K L hvertical ![1, 0] 1 = 0 := by
    rw [sub_eq_add_neg]
    simpa [standardSymplecticForm, hu0, hu2, hv0, hv2,
      hu3, hv1] using hpair
  exact (sub_eq_zero.mp hzero).symm
end CompactnessConjecture
