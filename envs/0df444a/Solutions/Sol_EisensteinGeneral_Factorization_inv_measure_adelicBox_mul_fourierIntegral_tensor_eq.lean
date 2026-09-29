-- Prove2me | solution 1 for EisensteinGeneral.Factorization.inv_measure_adelicBox_mul_fourierIntegral_tensor_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/9551a7be-59e4-559b-ac66-afbbc79f5234

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicFourier
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Theorems.Thm_NumberField_AdelicBox_inv_measure_adelicBox_mul_integral_pureTensor_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_EisensteinGeneral_Factorization_inv_measure_adelicBox_mul_fourierIntegral_tensor_eq
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain

noncomputable section

namespace FiniteAdelicFactorization

open IsDedekindDomain Filter Topology
open scoped RestrictedProduct ENNReal NNReal

section Recognition

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {Y : Type*} [MeasurableSpace Y]

end Recognition

section Places

variable (F : Type) [Field F] [NumberField F]

private theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI : Countable F := by
    have e := (Module.finBasis ℚ F).equivFun.toEquiv
    exact (Equiv.countable_iff e).mpr inferInstance
  haveI : Countable (𝓞 F) :=
    Function.Injective.countable (f := ((↑) : 𝓞 F → F)) NumberField.RingOfIntegers.coe_injective
  haveI : Countable (List (𝓞 F)) := inferInstance
  have hsurj : Function.Surjective (fun l : List (𝓞 F) => Ideal.span {x | x ∈ l}) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
    refine ⟨s.toList, ?_⟩
    have hset : {x : 𝓞 F | x ∈ s.toList} = (s : Set (𝓞 F)) := Set.ext fun x => Finset.mem_toList
    show Ideal.span {x | x ∈ s.toList} = I
    rw [hset]
    exact hs
  haveI : Countable (Ideal (𝓞 F)) := hsurj.countable
  exact Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    fun v w h => HeightOneSpectrum.ext h

attribute [local instance] countable_heightOneSpectrum

end Places

attribute [local instance] countable_heightOneSpectrum

section Measures

variable (F : Type) [Field F] [NumberField F]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]

end Measures

section StratumIdentity

variable (F : Type) [Field F] [NumberField F]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]

end StratumIdentity

section LocalIntegrals

variable (F : Type) [Field F] [NumberField F]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]

end LocalIntegrals

variable (F : Type) [Field F] [NumberField F]

section ArchimedeanSplit

open scoped Classical in

private theorem inv_measure_adelicBox_mul_fourierIntegral_tensor_eq
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (f : mixedEmbedding.mixedSpace F → ℂ) (g : FiniteAdeleRing (𝓞 F) F → ℂ)
    (w : AdeleRing (𝓞 F) F) :
    ((μ (adelicBox F)).toReal : ℂ)⁻¹ *
        fourierIntegral ψ μ (fun x ↦ f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * g x.2) w
      = (((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
        * (fourierIntegral
              (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
                (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
              MeasureTheory.volume f (InfiniteAdeleRing.ringEquiv_mixedSpace F w.1)
          * (((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)⁻¹
              * fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr _ _)) ν g w.2)) := by
  have key := NumberField.AdelicBox.inv_measure_adelicBox_mul_integral_pureTensor_eq F μ ν
    (fun y => (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
          (-(y * InfiniteAdeleRing.ringEquiv_mixedSpace F w.1)) * f y)
    (fun z => (ψ.compAddMonoidHom (AddMonoidHom.inr _ _)) (-(z * w.2)) * g z)
  have hpt : (fun x : AdeleRing (𝓞 F) F =>
        ψ (-(x * w)) * (f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * g x.2))
      = fun x : AdeleRing (𝓞 F) F =>
        (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
            (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
            (-(InfiniteAdeleRing.ringEquiv_mixedSpace F x.1
                * InfiniteAdeleRing.ringEquiv_mixedSpace F w.1))
          * f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)
          * ((ψ.compAddMonoidHom (AddMonoidHom.inr _ _)) (-(x.2 * w.2)) * g x.2) := by
    funext x
    have hsplit : -(x * w)
        = (((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (-(x.1 * w.1)) :
              AdeleRing (𝓞 F) F)
            + ((AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (-(x.2 * w.2)) :
              AdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F) :=
      Prod.ext (show -(x.1 * w.1) = -(x.1 * w.1) + 0 from (add_zero _).symm)
        (show -(x.2 * w.2) = 0 + -(x.2 * w.2) from (zero_add _).symm)
    have hmul : ψ (((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (-(x.1 * w.1)) :
              AdeleRing (𝓞 F) F)
            + ((AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (-(x.2 * w.2)) :
              AdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F)
        = ψ ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (-(x.1 * w.1)))
            * ψ ((AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (-(x.2 * w.2))) :=
      AddChar.map_add_eq_mul ψ _ _
    show ψ (-(x * w)) * (f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * g x.2)
        = ψ ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
              ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
                (-(InfiniteAdeleRing.ringEquiv_mixedSpace F x.1
                    * InfiniteAdeleRing.ringEquiv_mixedSpace F w.1))))
            * f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)
            * (ψ ((AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (-(x.2 * w.2)))
                * g x.2)
    rw [map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm,
      map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm, RingEquiv.symm_apply_apply,
      RingEquiv.symm_apply_apply, hsplit, hmul]
    ring
  simp only [fourierIntegral_def]
  rw [hpt]
  exact key

end ArchimedeanSplit

end FiniteAdelicFactorization

end

open FiniteAdelicFactorization

open scoped Classical in

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (f : mixedEmbedding.mixedSpace F → ℂ) (g : FiniteAdeleRing (𝓞 F) F → ℂ)
    (w : AdeleRing (𝓞 F) F) :
    ((μ (adelicBox F)).toReal : ℂ)⁻¹ *
        fourierIntegral ψ μ (fun x ↦ f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * g x.2) w
      = (((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
        * (fourierIntegral
              (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
                (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
              MeasureTheory.volume f (InfiniteAdeleRing.ringEquiv_mixedSpace F w.1)
          * (((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)⁻¹
              * fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr _ _)) ν g w.2)) := by
  exact FiniteAdelicFactorization.inv_measure_adelicBox_mul_fourierIntegral_tensor_eq F μ ν ψ f g w

#print axioms solution

end S_EisensteinGeneral_Factorization_inv_measure_adelicBox_mul_fourierIntegral_tensor_eq
end P2MW
export P2MW.S_EisensteinGeneral_Factorization_inv_measure_adelicBox_mul_fourierIntegral_tensor_eq (solution)
