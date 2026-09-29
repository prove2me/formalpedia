-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.exists_isShiftInvertC
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:52:20.497849+00:00
-- url     : https://prove2.me/submissions/7163c094-05a0-4696-80c3-eff044abd699

-- Generated from ChapterHashimotoComplexShifts.lean — solution of BookProof.HashimotoShiftInvert.exists_isShiftInvertC
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert



















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {A : Dom →ₗ[ℂ] F} (hsym : SymmetricOn Dom A)
    {γ : ℂ} (hγ : γ.im ≠ 0) (hsurj : Function.Surjective (cshiftMap A γ)) :
    ∃ X : F →L[ℂ] F, IsShiftInvertC A γ X := by

  classical
  have hpos : 0 < |γ.im| := abs_pos.mpr hγ
  have hinj : Function.Injective (cshiftMap A γ) := cshiftMap_injective hsym hγ
  choose g hg using hsurj
  have hgshift : ∀ x : Dom, g (cshiftMap A γ x) = x := fun x => hinj (hg _)
  have hadd : ∀ u v : F, ((g (u + v) : Dom) : F) = (g u : F) + (g v : F) := by
    intro u v
    have : cshiftMap A γ (g (u + v)) = cshiftMap A γ (g u + g v) := by
      rw [hg, map_add, hg, hg]
    exact congrArg Subtype.val (hinj this)
  have hsmul : ∀ (c : ℂ) (u : F), ((g (c • u) : Dom) : F) = c • (g u : F) := by
    intro c u
    have : cshiftMap A γ (g (c • u)) = cshiftMap A γ (c • g u) := by
      rw [hg, map_smul, hg]
    exact congrArg Subtype.val (hinj this)
  let L : F →ₗ[ℂ] F :=
    { toFun := fun u => (g u : F)
      map_add' := hadd
      map_smul' := by intro c u; simpa using hsmul c u }
  have hbound : ∀ u : F, ‖L u‖ ≤ |γ.im|⁻¹ * ‖u‖ := by
    intro u
    have hb : |γ.im| * ‖((g u : Dom) : F)‖ ≤ ‖cshiftMap A γ (g u)‖ := norm_cshiftMap_ge hsym _ _
    rw [hg u] at hb
    rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
    exact hb
  refine ⟨L.mkContinuous |γ.im|⁻¹ hbound, fun x => ?_, fun u => ?_⟩
  · change ((g (cshiftMap A γ x) : Dom) : F) = (x : F)
    rw [hgshift x]
  · refine ⟨(g u).2, ?_⟩
    have hsub : (⟨((g u : Dom) : F), (g u).2⟩ : Dom) = g u := Subtype.ext rfl
    change cshiftMap A γ ⟨((g u : Dom) : F), _⟩ = u
    rw [hsub, hg u]
