-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_fg_subalgebra_isPullback_iso_of_iso_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/db47cee1-fd5b-5331-b14b-4985539da6d9

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_stdIsoPackage_of_iso_of_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_of_stdIsoPackage
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_iso_of_stdIsoPackage
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_isPullback_iso_of_iso_of_isPullback
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op"
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) {N m : ℕ}
    {R : Type} [CommRing R] [IsNoetherianRing R] {L : Type} [CommRing L] [Algebra R L]
    (u w : FakeEllipticCurve.WithFullLevel Λ N m R) (u' w' : FakeEllipticCurve.WithFullLevel Λ N m L)
    (hu : FakeEllipticCurve.WithFullLevel.IsPullback (algebraMap R L) u u')
    (hw : FakeEllipticCurve.WithFullLevel.IsPullback (algebraMap R L) w w')
    (he : FakeEllipticCurve.WithFullLevel.Iso u' w') (s : Finset L) :
    ∃ (T : Subalgebra R L), T.FG ∧ (↑s : Set L) ⊆ T ∧
      ∃ (uT wT : FakeEllipticCurve.WithFullLevel Λ N m ↥T),
        FakeEllipticCurve.WithFullLevel.IsPullback (algebraMap R ↥T) u uT ∧
        FakeEllipticCurve.WithFullLevel.IsPullback (algebraMap R ↥T) w wT ∧
        FakeEllipticCurve.WithFullLevel.Iso uT wT := by
  classical
  obtain ⟨e, e_snd, e_mul, e_act, e_P, e_lev, e_lev'⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_stdIsoPackage_of_iso_of_isPullback hΛ u w u' w' hu hw he
  obtain ⟨T, hTfg, hsT, eT, eT_snd, eT_mul, eT_act, eT_P, eT_lev, eT_lev'⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_fg_subalgebra_stdIsoPackage_of_stdIsoPackage
      hΛ u w e e_snd e_mul e_act e_P e_lev e_lev' s
  obtain ⟨uT, wT, huT, hwT, hT⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_iso_of_stdIsoPackage u w eT eT_snd eT_mul eT_act eT_P eT_lev eT_lev'
  exact ⟨T, hTfg, hsT, uT, wT, huT, hwT, hT⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_isPullback_iso_of_iso_of_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_isPullback_iso_of_iso_of_isPullback (solution)
