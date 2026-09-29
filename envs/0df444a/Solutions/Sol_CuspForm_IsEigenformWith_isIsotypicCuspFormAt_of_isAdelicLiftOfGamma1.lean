-- Prove2me | solution 1 for CuspForm.IsEigenformWith.isIsotypicCuspFormAt_of_isAdelicLiftOfGamma1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/2d1bbd59-aafb-51ce-bd45-59c9429e04b2

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent

import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_continuous
import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_isKfSmooth
import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_memLp_two_restrict_productionPinsGeneral
import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_isCuspidalFn_productionPinsGeneral
import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_apply_mul_eq_of_mem_productionPinsGeneral_U
import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_isHeckeCosetEigenfunctionAt_productionPinsGeneral_of_heckeU_add_smul_slash_heckeDiagMatrix_eq
import Theorems.Thm_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_eq_qCoeff_smul
import Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_apply_centralScalar_det_gen_mul_eq_nebentypus_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsEigenformWith_isIsotypicCuspFormAt_of_isAdelicLiftOfGamma1
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

set_option autoImplicit false

namespace Ws41
namespace R2Asm

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

end Ws41.R2Asm

theorem solution
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith ε h)
    (Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (hξ : ∀ (z : ↥((productionPinsGeneral ℚ).Z)) (x : AdelicGL2 (𝓞 ℚ) ℚ),
      Φ (centralScalar (𝓞 ℚ) ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * x) = ((ξ z : ℂˣ) : ℂ) * Φ x)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ¬ v.asIdeal ∣ AdelicDock.ratLevel M)
    (Ψ : HeckeEigensystem ℚ ℂ)
    (ha : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Ψ.a v = ModularFormClass.qCoeff h (Ideal.absNorm v.asIdeal))
    (hb : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Ψ.b v = (Ideal.absNorm v.asIdeal : ℂ) * ε ((Ideal.absNorm v.asIdeal : ℕ) : ZMod M)) :
    IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ (AdelicDock.ratLevel M) S Ψ Φ := by
  have hne : ∀ v : HeightOneSpectrum (𝓞 ℚ), (HeckeEigensystem.cNorm v) ≠ 0 :=
    fun v => HeckeEigensystem.cNorm_ne_zero v
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
  ·
    letI := (productionPinsGeneral ℚ).mS
    exact (lsXiMemberAt_iff (𝓞 ℚ) ℚ (productionPinsGeneral ℚ).μ (productionPinsGeneral ℚ).Z ξ
      (productionPinsGeneral ℚ).D Φ).mpr
        ⟨⟨fun γ g => hΦ.left_inv γ g, hξ⟩, hΦ.memLp_two_restrict_productionPinsGeneral⟩
  ·
    exact hΦ.isCuspidalFn_productionPinsGeneral
  ·
    exact hΦ.isKfSmooth
  ·
    exact hΦ.continuous
  ·
    intro g u hu
    exact hΦ.apply_mul_eq_of_mem_productionPinsGeneral_U g u hu
  ·
    intro v hv
    have hvM := hS v hv
    have hp : (Ideal.absNorm v.asIdeal).Prime := Ws41.R2Asm.absNorm_prime v
    have hpM : ¬ Ideal.absNorm v.asIdeal ∣ M := Ws41.R2Asm.not_absNorm_dvd_of_not_dvd_ratLevel v hvM
    have hT := hh.heckeU_add_smul_slash_heckeDiagMatrix_eq_qCoeff_smul hp hpM
    rw [← ha v hv] at hT
    exact hΦ.isHeckeCosetEigenfunctionAt_productionPinsGeneral_of_heckeU_add_smul_slash_heckeDiagMatrix_eq
      hh.hasNebentypus v hvM (Ψ.a v) hT
  ·
    intro v hv g
    rw [hΦ.apply_centralScalar_det_gen_mul_eq_nebentypus_mul hh.hasNebentypus v (hS v hv) g,
      HeckeEigensystem.toRawCentral_b, hb v hv, ← mul_assoc,
      show (HeckeEigensystem.cNorm v)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) = 1 from inv_mul_cancel₀ (hne v),
      one_mul]

end S_CuspForm_IsEigenformWith_isIsotypicCuspFormAt_of_isAdelicLiftOfGamma1
end P2MW
export P2MW.S_CuspForm_IsEigenformWith_isIsotypicCuspFormAt_of_isAdelicLiftOfGamma1 (solution)
