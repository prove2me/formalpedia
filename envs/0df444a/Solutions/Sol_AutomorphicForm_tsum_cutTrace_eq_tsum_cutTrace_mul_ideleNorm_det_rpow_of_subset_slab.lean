-- Prove2me | solution 1 for AutomorphicForm.tsum_cutTrace_eq_tsum_cutTrace_mul_ideleNorm_det_rpow_of_subset_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/45d7b703-d35f-51ce-90a2-e794095403ac

import Theorems.Thm_AutomorphicForm_mem_cuspClasses_iff_twist_mem_cuspClasses_and_cutTrace_eq_cutTrace_twist_mul_ideleNorm_det_rpow_of_subset_slab
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_tsum_cutTrace_eq_tsum_cutTrace_mul_ideleNorm_det_rpow_of_subset_slab
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace TraceTwistReduce

open NumberField IsDedekindDomain AutomorphicForm

theorem twist_twist_inv {K : Type} [Field K] [NumberField K] (π : HeckeEigensystem K ℂ)
    (χ : HeightOneSpectrum (𝓞 K) → ℂ) (hχ : ∀ v, χ v ≠ 0) :
    (π.twist (fun v => (χ v)⁻¹)).twist χ = π := by
  rcases π with ⟨lvl, hlvl, a, b⟩
  simp only [HeckeEigensystem.twist, HeckeEigensystem.mk.injEq, true_and]
  refine ⟨funext fun v => ?_, funext fun v => ?_⟩
  · field_simp [hχ v]
  · field_simp [hχ v]

theorem twist_inv_twist {K : Type} [Field K] [NumberField K] (π : HeckeEigensystem K ℂ)
    (χ : HeightOneSpectrum (𝓞 K) → ℂ) (hχ : ∀ v, χ v ≠ 0) :
    (π.twist χ).twist (fun v => (χ v)⁻¹) = π := by
  rcases π with ⟨lvl, hlvl, a, b⟩
  simp only [HeckeEigensystem.twist, HeckeEigensystem.mk.injEq, true_and]
  refine ⟨funext fun v => ?_, funext fun v => ?_⟩
  · field_simp [hχ v]
  · field_simp [hχ v]

end TraceTwistReduce

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦdet : ∃ α β : ℝ, 0 < α ∧
      Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K)
    (ξK ξ₀K : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (w : ℝ)
    (hξ₀ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ((ξ₀K ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) =
        ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (-w) : ℝ) : ℂ))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (f' : AdelicGL2 (𝓞 K) K → ℂ) (hf' : Continuous f') (hfc' : HasCompactSupport f')
    (hff' : ∀ g : AdelicGL2 (𝓞 K) K,
      f' g = f g * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) :
    ∑' π : {π : HeckeEigensystem K ℂ //
        π ∈ cuspClasses K
          (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N SK},
      cutTrace K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N SK π.1 tysK f hf hfc =
    ∑' π : {π : HeckeEigensystem K ℂ //
        π ∈ cuspClasses K
          (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ₀K N SK},
      cutTrace K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ₀K N SK π.1 tysK f' hf' hfc' := by
  classical
  set χ : HeightOneSpectrum (𝓞 K) → ℂ := (fun v : HeightOneSpectrum (𝓞 K) =>
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v))) ^ (-(w / 2)) : ℝ) : ℂ)) with hχdef
  have hχ : ∀ v, χ v ≠ 0 := by
    intro v
    simp only [hχdef, ne_eq, Complex.ofReal_eq_zero]
    exact (Real.rpow_pos_of_pos (NumberField.TateGlobal.ideleNorm_pos _) _).ne'
  have ISO := fun π : HeckeEigensystem K ℂ =>
    AutomorphicForm.mem_cuspClasses_iff_twist_mem_cuspClasses_and_cutTrace_eq_cutTrace_twist_mul_ideleNorm_det_rpow_of_subset_slab
      K Φ hΦdet SK N tysK ξK ξ₀K w hξ₀ f hf hfc f' hf' hfc' hff' π

  let e : {π : HeckeEigensystem K ℂ // π ∈ cuspClasses K (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N SK} ≃
      {π : HeckeEigensystem K ℂ // π ∈ cuspClasses K (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ₀K N SK} :=
    { toFun := fun π => ⟨π.1.twist χ, (ISO π.1).1.mp π.2⟩
      invFun := fun π' => ⟨π'.1.twist (fun v => (χ v)⁻¹), (ISO _).1.mpr (by
        rw [TraceTwistReduce.twist_twist_inv _ χ hχ]; exact π'.2)⟩
      left_inv := fun π => Subtype.ext (TraceTwistReduce.twist_inv_twist _ χ hχ)
      right_inv := fun π' => Subtype.ext (TraceTwistReduce.twist_twist_inv _ χ hχ) }
  rw [← Equiv.tsum_eq e]
  exact tsum_congr fun π => (ISO π.1).2

end S_AutomorphicForm_tsum_cutTrace_eq_tsum_cutTrace_mul_ideleNorm_det_rpow_of_subset_slab
end P2MW
export P2MW.S_AutomorphicForm_tsum_cutTrace_eq_tsum_cutTrace_mul_ideleNorm_det_rpow_of_subset_slab (solution)
