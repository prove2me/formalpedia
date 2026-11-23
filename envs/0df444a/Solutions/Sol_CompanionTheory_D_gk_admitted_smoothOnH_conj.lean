-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.smoothOnH_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:15.300343+00:00
-- url     : https://prove2.me/submissions/24a03912-dc26-4323-a191-10784dfde8c8

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_InPCommutatorOfInK
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfFiniteRank
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open MeasureTheory Matrix
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PI.UpqRep
variable {n : ℕ} {ε : Fin n → Bool}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A B P : Matrix (Fin n) (Fin n) ℂ}
    (hP : IsUnit P) (hAB : Pᴴ * A * P = B) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (h : SmoothOnH A fun g => f (P⁻¹ * g * P)) : SmoothOnH B f := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  have hmem : ∀ g, inUH B g → inUH A (P * g * P⁻¹) := by
    intro g hg
    unfold inUH at hg ⊢
    have h3 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    calc (P * g * P⁻¹)ᴴ * A * (P * g * P⁻¹) = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * A * P) * g) * P⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((P⁻¹)ᴴ * Pᴴ) * A * (P * P⁻¹) := by rw [hAB, hg, ← hAB]; simp only [Matrix.mul_assoc]
      _ = A := by rw [h3, h1, Matrix.one_mul, Matrix.mul_one]
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun g => P * g * P⁻¹
      map_add' := fun a b => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c a => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  have hL : ContDiff ℝ ∞ fun g : Matrix (Fin n) (Fin n) ℂ => P * g * P⁻¹ := (LinearMap.toContinuousLinearMap L).contDiff
  intro g₀ hg₀
  obtain ⟨V, F, hV, hgV, hF, hfF⟩ := h _ (hmem g₀ hg₀)
  refine ⟨(fun g => P * g * P⁻¹) ⁻¹' V, fun g => F (P * g * P⁻¹), hV.preimage hL.continuous, hgV,
    hF.comp hL.contDiffOn fun g hg => hg, fun g hg hgB => ?_⟩
  refine Eq.trans ?_ (hfF _ hg (hmem g hgB))
  show f g = f (P⁻¹ * (P * g * P⁻¹) * P)
  congr 1
  calc g = (P⁻¹ * P) * g * (P⁻¹ * P) := by rw [h2, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]
end CompanionTheory.D.gk.admitted
