-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.exists_isShiftInvert
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-02T14:42:53.064338+00:00
-- url     : https://prove2.me/submissions/fb29ccf6-f8da-4ba5-88d5-e763c05169fc

-- Generated from ChapterHashimotoShiftInvert.lean — solution of BookProof.HashimotoShiftInvert.exists_isShiftInvert
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Theorems.Thm_BookProof_HashimotoShiftInvert_norm_shiftMap_ge
import Theorems.Thm_BookProof_HashimotoShiftInvert_shiftMap_injective
open BookProof.HashimotoShiftInvert




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {A : Dom →ₗ[ℂ] F} (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    {γ : ℝ} (hγ : 0 < γ) (hsurj : Function.Surjective (shiftMap A γ)) :
    ∃ R : F →L[ℂ] F, IsShiftInvert A γ R := by

  classical
  have hinj : Function.Injective (shiftMap A γ) := shiftMap_injective hpos hγ
  choose g hg using hsurj
  have hgshift : ∀ x : Dom, g (shiftMap A γ x) = x := fun x => hinj (hg _)
  have hadd : ∀ u v : F, ((g (u + v) : Dom) : F) = (g u : F) + (g v : F) := by
    intro u v
    have : shiftMap A γ (g (u + v)) = shiftMap A γ (g u + g v) := by
      rw [hg, map_add, hg, hg]
    exact congrArg Subtype.val (hinj this)
  have hsmul : ∀ (c : ℂ) (u : F), ((g (c • u) : Dom) : F) = c • (g u : F) := by
    intro c u
    have : shiftMap A γ (g (c • u)) = shiftMap A γ (c • g u) := by
      rw [hg, map_smul, hg]
    exact congrArg Subtype.val (hinj this)
  let L : F →ₗ[ℂ] F :=
    { toFun := fun u => (g u : F)
      map_add' := hadd
      map_smul' := by intro c u; simpa using hsmul c u }
  have hbound : ∀ u : F, ‖L u‖ ≤ γ⁻¹ * ‖u‖ := by
    intro u
    have hb : γ * ‖((g u : Dom) : F)‖ ≤ ‖shiftMap A γ (g u)‖ := norm_shiftMap_ge hpos _
    rw [hg u] at hb
    rw [inv_mul_eq_div, le_div_iff₀ hγ, mul_comm]
    exact hb
  refine ⟨L.mkContinuous γ⁻¹ hbound, fun x => ?_, fun u => ?_⟩
  · change ((g (shiftMap A γ x) : Dom) : F) = (x : F)
    rw [hgshift x]
  · refine ⟨(g u).2, ?_⟩
    have hsub : (⟨((g u : Dom) : F), (g u).2⟩ : Dom) = g u := Subtype.ext rfl
    change shiftMap A γ ⟨((g u : Dom) : F), _⟩ = u
    rw [hsub, hg u]
