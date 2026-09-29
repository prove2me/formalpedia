-- Prove2me | solution 1 for AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/bf6d8153-080e-5565-84e5-5532cad42a7d

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_whittakerCoefficient_sum_smul_of_continuous

set_option autoImplicit false

open MeasureTheory Filter Topology NumberField NumberField.AdelicBox NumberField.AdelicHaar AutomorphicForm
open scoped ProbabilityTheory

namespace Ws37WLin

theorem continuous_unipotentGL2 (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (fun x : A => (unipotentGL2 x : GL (Fin 2) A)) := by
  have hmat : ∀ s : A → A, Continuous s → Continuous (fun x : A => (!![1, s x; 0, 1] : Matrix (Fin 2) (Fin 2) A)) := by
    intro s hs
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [hs, continuous_const]
  rw [Units.continuous_iff]
  constructor
  · have h__af := hmat id continuous_id
    simp [unipotentGL2_coe] at h__af
    exact h__af
  · have hinv : ∀ x : A, ((unipotentGL2 x : GL (Fin 2) A)⁻¹ : GL (Fin 2) A) = unipotentGL2 (-x) := by
      intro x
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero]
    simp only [hinv]
    simpa [unipotentGL2_coe] using hmat Neg.neg continuous_neg

end Ws37WLin

open Ws37WLin
open NumberField.AdelicLevel AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ)
    (m : ℕ) (φ : Fin m → (AdelicGL2 (𝓞 F) F → ℂ)) (hφ : ∀ j, Continuous (φ j)) (cs : Fin m → ℂ)
    (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ (fun x => ∑ j, cs j * φ j x) α g =
      ∑ j, cs j * whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ (φ j) α g := by
  classical
  letI := adeleBorel (𝓞 F) F
  haveI := borelSpace_adeleBorel (𝓞 F) F
  set μ : Measure (AdeleRing (𝓞 F) F) := adelicAddHaar (𝓞 F) F with hμ
  set B : Set (AdeleRing (𝓞 F) F) := adelicBox F with hB

  have hW : ∀ f : AdelicGL2 (𝓞 F) F → ℂ,
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ f α g =
        ((μ B)⁻¹).toReal • ∫ x in B, f (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) ∂μ := by
    intro f
    unfold whittakerCoefficient
    dsimp only [productionPinsOf]
    exact integral_smul_measure _ _

  obtain ⟨C, hCc, hBC⟩ := exists_isCompact_adelicBox_subset F
  have hBfin : μ B < ⊤ := adelicAddHaar_adelicBox_lt_top F
  have hBmeas : MeasurableSet B := measurableSet_adelicBox F
  set G : Fin m → AdeleRing (𝓞 F) F → ℂ := fun j x =>
    φ j (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) with hG
  have hint : ∀ j, IntegrableOn (G j) B μ := by
    intro j
    have hc : Continuous (G j) :=
      ((hφ j).comp ((continuous_unipotentGL2 (AdeleRing (𝓞 F) F)).mul continuous_const)).mul
        (hψ.comp ((continuous_const.mul continuous_id).neg))
    obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn (f := G j) hc.continuousOn
    exact Measure.integrableOn_of_bounded hBfin.ne hc.aestronglyMeasurable
      (ae_restrict_of_forall_mem hBmeas fun x hx => hM x (hBC hx))
  rw [hW, show (∑ j, cs j * whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ (φ j) α g) =
      ∑ j, cs j * (((μ B)⁻¹).toReal • ∫ x in B, G j x ∂μ) from
    Finset.sum_congr rfl (fun j _ => by rw [hW])]
  have hsum : (fun x => (∑ j, cs j * φ j (unipotentGL2 x * g)) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))) =
      fun x => ∑ j, cs j * G j x := by
    funext x
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hG, mul_assoc]
  rw [hsum, integral_finset_sum _ (fun j _ => (hint j).const_mul (cs j))]
  simp_rw [integral_const_mul]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.real_smul, Complex.real_smul]
  ring

end S_AutomorphicForm_whittakerCoefficient_sum_smul_of_continuous
end P2MW
export P2MW.S_AutomorphicForm_whittakerCoefficient_sum_smul_of_continuous (solution)
