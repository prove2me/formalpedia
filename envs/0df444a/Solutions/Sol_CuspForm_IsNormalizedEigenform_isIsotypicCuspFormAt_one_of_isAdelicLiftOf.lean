-- Prove2me | solution 1 for CuspForm.IsNormalizedEigenform.isIsotypicCuspFormAt_one_of_isAdelicLiftOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/4d9c8a39-2e64-58f2-a05c-65411f39edeb

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent

import Theorems.Thm_CuspForm_IsEigenformWith_isIsotypicCuspFormAt_of_isAdelicLiftOfGamma1
import Theorems.Thm_CuspForm_IsAdelicLiftOf_apply_centralScalar_mul
import Theorems.Thm_CuspForm_exists_gamma1_coe_eq_and_hasNebentypus_one
import Theorems.Thm_CuspForm_IsNormalizedEigenform_isEigenformWith_one_of_coe_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNormalizedEigenform_isIsotypicCuspFormAt_one_of_isAdelicLiftOf
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

namespace Ws41
namespace R1aAsm

open IsDedekindDomain NumberField

theorem absNorm_prime (v : HeightOneSpectrum (𝓞 ℚ)) : (Ideal.absNorm v.asIdeal).Prime := by
  haveI : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ)
      Rat.ringOfIntegersEquiv.symm.surjective
  set π := Submodule.IsPrincipal.generator v.asIdeal with hπdef
  have hspan := (Submodule.IsPrincipal.span_singleton_generator v.asIdeal).symm
  have hπprime : Prime π :=
    Submodule.IsPrincipal.prime_generator_of_isPrime v.asIdeal v.ne_bot
  have hπℤ : Prime (Rat.ringOfIntegersEquiv π) :=
    (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.toMulEquiv).mpr hπprime
  have hrank : Module.finrank ℤ (𝓞 ℚ) = 1 :=
    (RingOfIntegers.rank ℚ).trans (Module.finrank_self (R := ℚ))
  have hπeq : algebraMap ℤ (𝓞 ℚ) (Rat.ringOfIntegersEquiv π) = π := by
    rw [algebraMap_int_eq, eq_intCast,
      show ((Rat.ringOfIntegersEquiv π : ℤ) : 𝓞 ℚ)
        = Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv π) from
        (map_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm,
      RingEquiv.symm_apply_apply]
  rw [hspan, Ideal.absNorm_span_singleton, ← hπdef, ← hπeq, Algebra.norm_algebraMap, hrank,
    pow_one]
  exact Int.prime_iff_natAbs_prime.mp hπℤ

theorem not_absNorm_dvd_of_not_dvd_ratLevel {M : ℕ} (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ¬ v.asIdeal ∣ AdelicDock.ratLevel M) : ¬ Ideal.absNorm v.asIdeal ∣ M := by
  intro hdvd
  apply hv

  rw [AdelicDock.ratLevel, Ideal.dvd_span_singleton]
  obtain ⟨c, hc⟩ := hdvd
  have hmem : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  have : ((M : ℕ) : 𝓞 ℚ) = ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) * (c : 𝓞 ℚ) := by
    rw [hc]; push_cast; ring
  show ((M : ℕ) : 𝓞 ℚ) ∈ v.asIdeal
  rw [this]
  exact v.asIdeal.mul_mem_right _ hmem

end Ws41.R1aAsm

theorem solution
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (hg : g.IsNormalizedEigenform)
    (Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hΦ : g.IsAdelicLiftOf Φ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ¬ v.asIdeal ∣ AdelicDock.ratLevel M)
    (Ψ : HeckeEigensystem ℚ ℂ)
    (ha : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Ψ.a v = ModularFormClass.qCoeff g (Ideal.absNorm v.asIdeal))
    (hb : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → Ψ.b v = (Ideal.absNorm v.asIdeal : ℂ)) :
    IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) (1 : (productionPinsGeneral ℚ).Z →* ℂˣ) (AdelicDock.ratLevel M) S Ψ Φ := by
  classical
  obtain ⟨g₁, hg₁, hneb⟩ := CuspForm.exists_gamma1_coe_eq_and_hasNebentypus_one 2 g
  have hh : CuspForm.IsEigenformWith (1 : DirichletCharacter ℂ M) g₁ :=
    hg.isEigenformWith_one_of_coe_eq g₁ hg₁
  have hΦ₁ : CuspForm.IsAdelicLiftOfGamma1 g₁ Φ := by
    refine ⟨hΦ.1, hΦ.2.1, fun x hfin hpos => ?_⟩
    rw [hg₁]
    exact hΦ.2.2 x hfin hpos
  have hξ : ∀ (z : ↥((productionPinsGeneral ℚ).Z)) (x : AdelicGL2 (𝓞 ℚ) ℚ),
      Φ (centralScalar (𝓞 ℚ) ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * x)
        = (((1 : (productionPinsGeneral ℚ).Z →* ℂˣ) z : ℂˣ) : ℂ) * Φ x := by
    intro z x
    rw [hΦ.apply_centralScalar_mul, MonoidHom.one_apply, Units.val_one, one_mul]
  have ha₁ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Ψ.a v = ModularFormClass.qCoeff g₁ (Ideal.absNorm v.asIdeal) := by
    intro v hv; rw [ha v hv, hg₁]
  have hb₁ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Ψ.b v = (Ideal.absNorm v.asIdeal : ℂ) *
        (1 : DirichletCharacter ℂ M) ((Ideal.absNorm v.asIdeal : ℕ) : ZMod M) := by
    intro v hv
    have hunit : IsUnit (((Ideal.absNorm v.asIdeal : ℕ) : ZMod M)) :=
      (ZMod.isUnit_iff_coprime _ _).mpr
        ((Nat.Prime.coprime_iff_not_dvd (Ws41.R1aAsm.absNorm_prime v)).mpr
          (Ws41.R1aAsm.not_absNorm_dvd_of_not_dvd_ratLevel v (hS v hv)))
    rw [hb v hv, MulChar.one_apply hunit, mul_one]
  exact CuspForm.IsEigenformWith.isIsotypicCuspFormAt_of_isAdelicLiftOfGamma1 hh Φ hΦ₁ 1 hξ S hS Ψ ha₁ hb₁

end S_CuspForm_IsNormalizedEigenform_isIsotypicCuspFormAt_one_of_isAdelicLiftOf
end P2MW
export P2MW.S_CuspForm_IsNormalizedEigenform_isIsotypicCuspFormAt_one_of_isAdelicLiftOf (solution)
