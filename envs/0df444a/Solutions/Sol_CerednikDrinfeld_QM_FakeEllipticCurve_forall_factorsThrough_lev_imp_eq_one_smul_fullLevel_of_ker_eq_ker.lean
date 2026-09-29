-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.forall_factorsThrough_lev_imp_eq_one_smul_fullLevel_of_ker_eq_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/2f924c1d-87bc-516f-8b5e-6a28714838e1

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_lev_imp_eq_one_iff_of_ringHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel_of_ker_eq_ker

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace PointIndep31

noncomputable def sigma {S : Type} [CommRing S] (p : PrimeSpectrum S) :
    S →+* AlgebraicClosure (FractionRing (S ⧸ p.asIdeal)) :=
  (algebraMap (FractionRing (S ⧸ p.asIdeal)) (AlgebraicClosure (FractionRing (S ⧸ p.asIdeal)))).comp
    ((algebraMap (S ⧸ p.asIdeal) (FractionRing (S ⧸ p.asIdeal))).comp (Ideal.Quotient.mk p.asIdeal))

theorem exists_comp_sigma_eq {S : Type} [CommRing S] (p : PrimeSpectrum S)
    (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (hsk : RingHom.ker sk = p.asIdeal) :
    ∃ ι : AlgebraicClosure (FractionRing (S ⧸ p.asIdeal)) →+* k, ι.comp (sigma p) = sk := by

  let ψ : S ⧸ p.asIdeal →+* k := Ideal.Quotient.lift p.asIdeal sk (fun a ha => by
    rw [← RingHom.mem_ker, hsk]; exact ha)
  have hψ : Function.Injective ψ := by
    rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_quotient_lift, hsk, Ideal.map_quotient_self]

  let φ : FractionRing (S ⧸ p.asIdeal) →+* k := IsFractionRing.lift hψ
  letI : Algebra (FractionRing (S ⧸ p.asIdeal)) k := φ.toAlgebra

  let ι : AlgebraicClosure (FractionRing (S ⧸ p.asIdeal)) →ₐ[FractionRing (S ⧸ p.asIdeal)] k := IsAlgClosed.lift
  refine ⟨ι.toRingHom, ?_⟩
  ext s
  simp only [sigma, RingHom.coe_comp, Function.comp_apply]
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
  show φ (algebraMap (S ⧸ p.asIdeal) (FractionRing (S ⧸ p.asIdeal)) (Ideal.Quotient.mk p.asIdeal s)) = sk s
  rw [show φ (algebraMap (S ⧸ p.asIdeal) (FractionRing (S ⧸ p.asIdeal)) (Ideal.Quotient.mk p.asIdeal s)) =
      ψ (Ideal.Quotient.mk p.asIdeal s) from IsFractionRing.lift_algebraMap hψ _]
  exact Ideal.Quotient.lift_mk _ _ _

end PointIndep31

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} (m ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    {S : Type} [CommRing S] (hm : IsUnit ((m : ℕ) : S)) (E : FakeEllipticCurve Λ N S) (P : E.FullLevel m)
    (p : PrimeSpectrum S)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (sk₀ : S →+* k₀) (hsk₀ : RingHom.ker sk₀ = p.asIdeal)
    (h₀ : ∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
      FactorsThrough E.lev
        (pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k₀ sk₀) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k₀ sk₀))) →
      pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k₀ sk₀) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k₀ sk₀)) = E.L.one (geomPoint k₀ sk₀))
    (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (hsk : RingHom.ker sk = p.asIdeal) :
    ∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
      FactorsThrough E.lev
        (pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk))) →
      pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = E.L.one (geomPoint k sk) := by
  obtain ⟨ι₀, hι₀⟩ := PointIndep31.exists_comp_sigma_eq p k₀ sk₀ hsk₀
  obtain ⟨ι, hι⟩ := PointIndep31.exists_comp_sigma_eq p k sk hsk
  subst hι₀ hι
  have hK := (CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.forall_factorsThrough_lev_imp_eq_one_iff_of_ringHom
    (⟨E, P⟩ : FakeEllipticCurve.WithFullLevel Λ N m S) _ (PointIndep31.sigma p) k₀ ι₀ L₀ (m / ℓ)).mpr h₀
  exact (CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.forall_factorsThrough_lev_imp_eq_one_iff_of_ringHom
    (⟨E, P⟩ : FakeEllipticCurve.WithFullLevel Λ N m S) _ (PointIndep31.sigma p) k ι L₀ (m / ℓ)).mp hK

end S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel_of_ker_eq_ker
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel_of_ker_eq_ker (solution)
