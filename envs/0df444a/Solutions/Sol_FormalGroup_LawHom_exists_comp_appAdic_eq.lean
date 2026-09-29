-- Prove2me | solution 1 for FormalGroup.LawHom.exists_comp_appAdic_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/6e99c30e-28ab-5395-87dd-b62ef4bb18d6

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_VariableChangeSeries
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_FormalGroup_LawHom_exists_comp_series_eq_subst
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_LawHom_exists_comp_appAdic_eq

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing FormalGroup

attribute [local instance] MvPolynomial.gradedAlgebra

namespace LCAAux

open scoped PowerSeries.WithPiTopology

attribute [local instance] DiscreteTopology.instContinuousSMul in

theorem eval₂_subst {R : Type*} [CommRing R] [UniformSpace R] [DiscreteUniformity R]
    {A : Type*} [CommRing A] [Algebra R A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [IsLinearTopology A A] [T2Space A] [CompleteSpace A]
    (g f : PowerSeries R) (hg : PowerSeries.constantCoeff g = 0) (a : A) (ha : PowerSeries.HasEval a) :
    PowerSeries.eval₂ (algebraMap R A) a (PowerSeries.subst g f) =
      PowerSeries.eval₂ (algebraMap R A) (PowerSeries.eval₂ (algebraMap R A) a g) f := by
  have hgs : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' hg
  have e1 : PowerSeries.eval₂ (algebraMap R A) a (PowerSeries.subst g f) =
      ((PowerSeries.aeval ha).comp (PowerSeries.substAlgHom hgs)) f := by
    rw [AlgHom.comp_apply, PowerSeries.coe_substAlgHom hgs, PowerSeries.coe_aeval ha]
  rw [e1, PowerSeries.substAlgHom_eq_aeval hgs, PowerSeries.comp_aeval _ (PowerSeries.continuous_aeval ha),
    PowerSeries.coe_aeval]
  exact congrArg (fun b => PowerSeries.eval₂ (algebraMap R A) b f) (congrFun (PowerSeries.coe_aeval ha) g)

end LCAAux

theorem solution
    {R : Type u} [CommRing R] {F G H : FormalGroup R} (φ : FormalGroup.LawHom F G) (χ : FormalGroup.LawHom G H) :
    ∃ ω : FormalGroup.LawHom F H,
      ω.series = PowerSeries.subst φ.series χ.series ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A] (I : Ideal A) [IsAdicComplete I A] (a : A), a ∈ I →
        ω.appAdic I a = χ.appAdic I (φ.appAdic I a) := by
  classical
  obtain ⟨ω, hω, -⟩ := FormalGroup.LawHom.exists_comp_series_eq_subst φ χ
  refine ⟨ω, hω, ?_⟩
  intro A _ _ I _ a ha
  letI wI : WithIdeal A := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨hcs, ht2⟩ := hI.isAdicComplete_iff.mp (inferInstance : IsAdicComplete I A)
  have ha' : PowerSeries.HasEval a := (PowerSeries.hasEval_def a).mpr (WithIdeal.isTopologicallyNilpotent_of_mem ha)
  show FormalGroup.evalSeries ω.series a = FormalGroup.evalSeries χ.series (FormalGroup.evalSeries φ.series a)
  unfold FormalGroup.evalSeries
  rw [hω]
  exact @LCAAux.eval₂_subst R _ ⊥ inferInstance A _ _ _ _ _ _ ht2 hcs φ.series χ.series φ.constantCoeff_series a ha'

end S_FormalGroup_LawHom_exists_comp_appAdic_eq
end P2MW
export P2MW.S_FormalGroup_LawHom_exists_comp_appAdic_eq (solution)
