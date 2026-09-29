-- Prove2me | solution 1 for EisensteinGeneral.Piece.integral_smul_add_mul_addChar_neg_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/56b51363-f5b6-56c3-95e7-0363b44cde13

import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Algebra.Module.ZLattice.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_EisensteinGeneral_Piece_integral_smul_add_mul_addChar_neg_mul_eq

set_option autoImplicit false

section Part1

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox NumberField.AdelicFourier NumberField.AdelicHaar IsDedekindDomain AutomorphicForm

open scoped NNReal
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace EgenPiece

private theorem pc_map_smul_adelicAddHaar (F : Type) [Field F] [NumberField F] (a : (AdeleRing (𝓞 F) F)ˣ) :
    Measure.map (fun x : AdeleRing (𝓞 F) F => a • x) (adelicAddHaar (𝓞 F) F)
      = (distribHaarChar (AdeleRing (𝓞 F) F) a)⁻¹ • adelicAddHaar (𝓞 F) F := by
  haveI : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  haveI : (adelicAddHaar (𝓞 F) F).Regular := by
    unfold adelicAddHaar
    infer_instance
  have hdef : DomMulAct.mk a⁻¹ • adelicAddHaar (𝓞 F) F
      = Measure.map (fun x : AdeleRing (𝓞 F) F => a • x) (adelicAddHaar (𝓞 F) F) := by
    show Measure.map (fun x : AdeleRing (𝓞 F) F => a⁻¹⁻¹ • x) _ = _
    rw [inv_inv]
  rw [← hdef, Measure.isAddLeftInvariant_eq_smul_of_regular (DomMulAct.mk a⁻¹ • adelicAddHaar (𝓞 F) F)
    (adelicAddHaar (𝓞 F) F), addHaarScalarFactor_smul_eq_distribHaarChar, map_inv]

end EgenPiece

end Part1

section Solution

open MeasureTheory NumberField NumberField.AdelicHaar
open scoped NNReal
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox NumberField.AdelicFourier NumberField.AdelicHaar IsDedekindDomain AutomorphicForm

open EgenPiece in

theorem solution (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (f : AdeleRing (𝓞 F) F → ℂ) (a : (AdeleRing (𝓞 F) F)ˣ)
    (u ξ : AdeleRing (𝓞 F) F) :
    ∫ y, f (a • (y + u)) * ψ (-(ξ * y)) ∂(adelicAddHaar (𝓞 F) F)
      = (((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) : ℂ)⁻¹ * ψ (ξ * u)
        * ∫ z, f z * ψ (-(ξ * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z)) ∂(adelicAddHaar (𝓞 F) F) := by
  haveI : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 F) F

  let e : AdeleRing (𝓞 F) F ≃ᵐ AdeleRing (𝓞 F) F :=
    ((Homeomorph.addLeft u).trans (Homeomorph.smul a)).toMeasurableEquiv
  have he : ∀ y, e y = a • (u + y) := fun _ => rfl
  have hmap : Measure.map e (adelicAddHaar (𝓞 F) F)
      = (distribHaarChar (AdeleRing (𝓞 F) F) a)⁻¹ • adelicAddHaar (𝓞 F) F := by
    have hcoe : (e : AdeleRing (𝓞 F) F → AdeleRing (𝓞 F) F)
        = (fun x : AdeleRing (𝓞 F) F => a • x) ∘ (fun x : AdeleRing (𝓞 F) F => u + x) := funext fun _ => rfl
    have hg : Measurable (fun x : AdeleRing (𝓞 F) F => a • x) := (continuous_const_smul a).measurable
    have hf : Measurable (fun x : AdeleRing (𝓞 F) F => u + x) :=
      (show Continuous (fun x : AdeleRing (𝓞 F) F => u + x) from continuous_const.add continuous_id).measurable
    rw [hcoe, ← Measure.map_map hg hf, map_add_left_eq_self, pc_map_smul_adelicAddHaar]

  have h1 : ∀ y : AdeleRing (𝓞 F) F,
      f (e y) * ψ (-(ξ * (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * e y - u)))
        = f (a • (y + u)) * ψ (-(ξ * y)) := by
    intro y
    rw [he, Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, Units.inv_mul_cancel_left,
      add_sub_cancel_left, add_comm u y]
  have h2 : ∀ z : AdeleRing (𝓞 F) F,
      f z * ψ (-(ξ * (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z - u)))
        = ψ (ξ * u) * (f z * ψ (-(ξ * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z))) := by
    intro z
    have harg : -(ξ * (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z - u))
        = ξ * u + -(ξ * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z) := by ring
    rw [harg, AddChar.map_add_eq_mul]
    ring
  calc ∫ y, f (a • (y + u)) * ψ (-(ξ * y)) ∂(adelicAddHaar (𝓞 F) F)
      = ∫ y, f (e y) * ψ (-(ξ * (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * e y - u)))
          ∂(adelicAddHaar (𝓞 F) F) := by
        simp only [h1]
    _ = ∫ z, f z * ψ (-(ξ * (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z - u)))
          ∂(Measure.map e (adelicAddHaar (𝓞 F) F)) :=
        (integral_map_equiv e (fun z => f z
          * ψ (-(ξ * (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z - u))))).symm
    _ = ∫ z, f z * ψ (-(ξ * (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z - u)))
          ∂((distribHaarChar (AdeleRing (𝓞 F) F) a)⁻¹ • adelicAddHaar (𝓞 F) F) := by
        rw [hmap]
    _ = (distribHaarChar (AdeleRing (𝓞 F) F) a)⁻¹
          • ∫ z, f z * ψ (-(ξ * (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z - u)))
              ∂(adelicAddHaar (𝓞 F) F) :=
        integral_smul_nnreal_measure _ _
    _ = (distribHaarChar (AdeleRing (𝓞 F) F) a)⁻¹
          • (ψ (ξ * u) * ∫ z, f z * ψ (-(ξ * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z))
              ∂(adelicAddHaar (𝓞 F) F)) := by
        simp only [h2]
        rw [integral_const_mul]
    _ = (((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) : ℂ)⁻¹ * ψ (ξ * u)
          * ∫ z, f z * ψ (-(ξ * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * z))
              ∂(adelicAddHaar (𝓞 F) F) := by
        rw [NNReal.smul_def, Complex.real_smul]
        push_cast
        ring

end Solution

#print axioms solution

end S_EisensteinGeneral_Piece_integral_smul_add_mul_addChar_neg_mul_eq
end P2MW
export P2MW.S_EisensteinGeneral_Piece_integral_smul_add_mul_addChar_neg_mul_eq (solution)
