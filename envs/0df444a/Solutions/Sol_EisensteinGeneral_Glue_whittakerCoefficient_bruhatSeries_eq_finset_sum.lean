-- Prove2me | solution 1 for EisensteinGeneral.Glue.whittakerCoefficient_bruhatSeries_eq_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/b6eed3ed-caf5-5b52-be6e-fc79b0ee153c

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Algebra.Module.ZLattice.Basic
import Theorems.Thm_EisensteinGeneral_Glue_whittakerCoefficientIntegrable_bruhatSeries_and_ae_summable_of_integrable
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_EisensteinGeneral_Glue_whittakerCoefficient_bruhatSeries_eq_finset_sum

set_option autoImplicit false

open EisensteinGeneral.Glue

section Part1

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox NumberField.AdelicFourier NumberField.AdelicHaar IsDedekindDomain AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace EgenGlue

private scoped instance l1_nontrivial (F : Type) [Field F] [NumberField F] : Nontrivial (AdeleRing (𝓞 F) F) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  exact ⟨⟨0, 1, fun h => zero_ne_one (α := w.Completion) (congrArg (fun z : AdeleRing (𝓞 F) F => z.1 w) h)⟩⟩

private scoped instance l1_countable (F : Type) [Field F] [NumberField F] :
    Countable (AdeleRing.principalSubgroup (𝓞 F) F) := by
  have hsurj : Function.Surjective
      (fun β : F => (⟨algebraMap F _ β, β, rfl⟩ : AdeleRing.principalSubgroup (𝓞 F) F)) := by
    rintro ⟨_, β, rfl⟩; exact ⟨β, rfl⟩
  exact hsurj.countable

private theorem tsum_finset_sum_mul_eq {β : Type} (n : ℕ) (c : Fin n → ℂ) (f : Fin n → β → ℂ)
    (hf : ∀ i, Summable (f i)) :
    ∑' b : β, ∑ i : Fin n, c i * f i b = ∑ i : Fin n, c i * ∑' b : β, f i b := by
  rw [Summable.tsum_finsetSum fun i _ => (hf i).mul_left (c i)]
  exact Finset.sum_congr rfl fun i _ => (hf i).tsum_mul_left (c i)

private theorem whittakerCoefficient_eq_finset_sum (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (n : ℕ) (c : Fin n → ℂ) (Θ : Fin n → AdelicGL2 (𝓞 F) F → ℂ)
    (Φ' : AdelicGL2 (𝓞 F) F → ℂ) (hΦ' : ∀ g', Φ' g' = ∑ i : Fin n, c i * Θ i g') (ξ : F) (g : AdelicGL2 (𝓞 F) F)
    (hint : ∀ i, WhittakerCoefficientIntegrable F (productionPins F) ψ (Θ i) ξ g) :
    whittakerCoefficient F (productionPins F) ψ Φ' ξ g
      = ∑ i : Fin n, c i * whittakerCoefficient F (productionPins F) ψ (Θ i) ξ g := by
  letI := (productionPins F).nS
  simp only [whittakerCoefficient, WhittakerCoefficientIntegrable] at hint ⊢
  simp_rw [hΦ', Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ fun i _ => (hint i).const_mul (c i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul (c i) _

private theorem tsum_whittakerCoefficient_zero (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (g : AdelicGL2 (𝓞 F) F) :
    ∑' ξ : {ξ : F // ξ ≠ 0}, whittakerCoefficient F (productionPins F) ψ
      (fun g' => (0 : ℂ) + ∑' ξ' : F,
        (fun _ : AdelicGL2 (𝓞 F) F => (0 : ℂ))
          (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g'))
      (ξ : F) g = 0 := by
  simp only [tsum_zero, add_zero, whittakerCoefficient_zero]

end EgenGlue
p2m_reactivate "P2MW.S_EisensteinGeneral_Glue_whittakerCoefficient_bruhatSeries_eq_finset_sum.EgenGlue"

end Part1
p2m_reactivate "P2MW.S_EisensteinGeneral_Glue_whittakerCoefficient_bruhatSeries_eq_finset_sum.EgenGlue"

section Solution

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox NumberField.AdelicFourier NumberField.AdelicHaar IsDedekindDomain AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

open EgenGlue EisensteinGeneral.Glue in

theorem solution (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψc : Continuous ψ) (hψ : ∀ x, ‖ψ x‖ = 1) (n : ℕ) (c : Fin n → ℂ)
    (Ψ : Fin n → AdelicGL2 (𝓞 F) F → ℂ) (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hΨ : ∀ i, ∃ χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, IsInducedSection (𝓞 F) F χ₁ χ₂ (Ψ i))
    (hΦ : ∀ g', Φ g' = ∑ i : Fin n, c i * Ψ i g') (ξ : F) (g : AdelicGL2 (𝓞 F) F)
    (hint : ∀ i, Integrable (fun y => Ψ i (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)) (adelicAddHaar (𝓞 F) F)) :
    whittakerCoefficient F (productionPins F) ψ
        (fun g' => Φ g' + ∑' ξ' : F, Φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g'))
        ξ g
      = ∑ i : Fin n, c i * whittakerCoefficient F (productionPins F) ψ
          (fun g' => Ψ i g' + ∑' ξ' : F,
            Ψ i (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) ξ g := by
  have h0 := fun i =>
    whittakerCoefficientIntegrable_bruhatSeries_and_ae_summable_of_integrable F ψ hψc hψ (Ψ i) (hΨ i) ξ g
      (hint i)
  refine Eq.trans ?_ (whittakerCoefficient_eq_finset_sum F ψ n c
    (fun i g' => Ψ i g' + ∑' ξ' : F,
      Ψ i (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g'))
    (fun g' => ∑ i : Fin n, c i * (Ψ i g' + ∑' ξ' : F,
      Ψ i (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')))
    (fun _ => rfl) ξ g (fun i => (h0 i).1))
  letI := (productionPins F).nS
  simp only [whittakerCoefficient]
  refine integral_congr_ae ?_
  filter_upwards [Filter.eventually_all.2 fun i => (h0 i).2] with x hx
  congr 1
  simp_rw [hΦ]
  rw [tsum_finset_sum_mul_eq n c _ hx, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Solution
p2m_reactivate "P2MW.S_EisensteinGeneral_Glue_whittakerCoefficient_bruhatSeries_eq_finset_sum.EgenGlue"

#print axioms solution

end S_EisensteinGeneral_Glue_whittakerCoefficient_bruhatSeries_eq_finset_sum
end P2MW
export P2MW.S_EisensteinGeneral_Glue_whittakerCoefficient_bruhatSeries_eq_finset_sum (solution)
