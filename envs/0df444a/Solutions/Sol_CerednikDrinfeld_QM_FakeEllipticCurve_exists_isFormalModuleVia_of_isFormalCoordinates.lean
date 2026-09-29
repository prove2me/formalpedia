-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFormalModuleVia_of_isFormalCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c1d347d1-d537-5381-ad43-8a31b7e21010

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong
import Theorems.Thm_CerednikDrinfeld_QM_existsUnique_hom_isFormalCompletionAlong_of_isFormalCoordinates
import Theorems.Thm_CerednikDrinfeld_QM_IsFormalCompletionAlong_of_forall_mapPt_eq_mul_of_isFormalCoordinates
import Theorems.Thm_CerednikDrinfeld_QM_IsFormalCompletionAlong_id_and_comp
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_F_eq_and_addVia_act_eq_of_isOrderCoord_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_coprime_natCast_mem_isFormalCompletionAlong_act_nthSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalModuleVia_of_isFormalCoordinates
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal

open scoped Quaternion

namespace D2aAction

theorem isFormalCompletionAlong_congr {B : Type} [CommRing B] {A A' : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of B)} {f' : A' ⟶ Spec (CommRingCat.of B)} {g g' : ℕ}
    {θ : RelativeGroupLaw.FormalCoordinates f g} {θ' : RelativeGroupLaw.FormalCoordinates f' g'}
    {h h' : A ⟶ A'} {hh : h ≫ f' = f} {hh' : h' ≫ f' = f} {φ : Fin g' → MvPowerSeries (Fin g) B}
    (e : h = h') (H : IsFormalCompletionAlong θ θ' h' hh' φ) : IsFormalCompletionAlong θ θ' h hh φ := by
  subst e
  exact H

end D2aAction

open D2aAction in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (B : Type) [CommRing B] (hq : IsNilpotent ((q : ℕ) : B)) (E : FakeEllipticCurve Λ N B)
    (F : MvFormalGroup 2 B) (hF : F.IsComm) (θ : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hθ : E.L.IsFormalCoordinates F θ) :
    ∃ X : FormalODModule q B, X.F = F ∧ E.IsFormalModuleVia coord X θ := by
  classical
  haveI := hF

  have hC : ∀ m : ↥Λ, ∃! φ : MvFormalGroup.End F,
      IsFormalCompletionAlong θ θ (E.act m) (E.act_over m) φ.toPowerSeries := fun m =>
    CerednikDrinfeld.QM.existsUnique_hom_isFormalCompletionAlong_of_isFormalCoordinates E.L E.L F F θ θ hθ hθ
      (E.act m) (E.act_over m) (fun B' _ _ P Q => E.act_hom m _ P Q)
  let ρ : ↥Λ → MvFormalGroup.End F := fun m => Classical.choose (hC m).exists
  have hρ : ∀ m, IsFormalCompletionAlong θ θ (E.act m) (E.act_over m) (ρ m).toPowerSeries := fun m =>
    Classical.choose_spec (hC m).exists
  have hρu : ∀ (m : ↥Λ) (φ : MvFormalGroup.End F),
      IsFormalCompletionAlong θ θ (E.act m) (E.act_over m) φ.toPowerSeries → φ = ρ m :=
    fun m φ h => (hC m).unique h (hρ m)

  have hadd : ∀ m m' : ↥Λ, ρ (m + m') = ρ m + ρ m' := by
    intro m m'
    symm
    apply hρu
    exact CerednikDrinfeld.QM.IsFormalCompletionAlong.of_forall_mapPt_eq_mul_of_isFormalCoordinates θ θ E.L F hθ
      (E.act m) (E.act m') (E.act (m + m')) (E.act_over m) (E.act_over m') (E.act_over _)
      (fun B' _ _ P => E.act_add m m' _ P) (ρ m).toPowerSeries (ρ m').toPowerSeries
      (ρ m).constantCoeff_eq_zero (ρ m').constantCoeff_eq_zero (hρ m) (hρ m')
  have hmul : ∀ (m m' : ↥Λ) (h : (m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]), h⟩ = ρ m * ρ m' := by
    intro m m' h
    symm
    apply hρu
    have hc := (CerednikDrinfeld.QM.IsFormalCompletionAlong.id_and_comp θ θ θ).2 (E.act m') (E.act_over m')
      (E.act m) (E.act_over m) (by rw [Category.assoc, E.act_over, E.act_over]) (ρ m').toPowerSeries
      (ρ m).toPowerSeries (ρ m').constantCoeff_eq_zero (hρ m') (hρ m)
    exact isFormalCompletionAlong_congr (E.act_mul m m' h) hc

  obtain ⟨n, hn, h1, hc1, hcomp1⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_coprime_natCast_mem_isFormalCompletionAlong_act_nthSeries coord
      hcoord B hq E F hF θ hθ
  have hunit : ∃ n : ℕ, n.Coprime q ∧ ∃ h : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      coord ⟨((n : ℚ) : ℍ[ℚ, a, b]), h⟩ = ((n : Zp2 q), 0) ∧
        (ρ ⟨((n : ℚ) : ℍ[ℚ, a, b]), h⟩).toPowerSeries = F.nthSeries n := by
    refine ⟨n, hn, h1, hc1, ?_⟩
    have hnat : (n : MvFormalGroup.End F) = ρ ⟨((n : ℚ) : ℍ[ℚ, a, b]), h1⟩ := by
      apply hρu
      rw [MvFormalGroup.End.toPowerSeries_natCast]
      exact hcomp1
    rw [← hnat, MvFormalGroup.End.toPowerSeries_natCast]

  obtain ⟨X, hXF, hact⟩ :=
    CerednikDrinfeld.FormalODModule.exists_F_eq_and_addVia_act_eq_of_isOrderCoord_of_isNilpotent coord hcoord B hq F
      ρ hadd hmul hunit
  refine ⟨X, hXF, ?_, ?_⟩
  · rw [hXF]
    exact hθ
  · intro B' _ _ J k hJ m s hs
    rw [hXF, hact m]
    exact hρ m B' J k hJ s hs

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalModuleVia_of_isFormalCoordinates
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalModuleVia_of_isFormalCoordinates (solution)
