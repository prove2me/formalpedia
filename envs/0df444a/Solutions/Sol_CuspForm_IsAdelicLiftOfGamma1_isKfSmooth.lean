-- Prove2me | solution 1 for CuspForm.IsAdelicLiftOfGamma1.isKfSmooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e42b6081-86e3-5298-b8f0-43a3ed2dcf96

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsAdelicLiftOfGamma1_isKfSmooth

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm

namespace Ws41
namespace B4

open NumberField NumberField.AdelicLevel AdelicDock

theorem finEmbed_glFin_of_glArch_eq_one (u : AdelicGL2 (𝓞 ℚ) ℚ) (hu : glArch (𝓞 ℚ) ℚ u = 1) :
    finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ u) = u := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have hmat : finMat (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = (u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) := by
    refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_
    · rw [mapMatrix_arch_finMat]
      ext i j
      have h : (glArch (𝓞 ℚ) ℚ u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j
          = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j := by rw [hu, Units.val_one]
      rw [glArch_apply] at h
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply]
      exact h.symm
    · rw [mapMatrix_fin_finMat]
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleFin_apply, glFin_apply]
  rw [coe_finEmbed, hmat]

theorem mem_productionPinsGeneral_U_iff (N : Ideal (𝓞 ℚ)) (u : AdelicGL2 (𝓞 ℚ) ℚ) :
    u ∈ (productionPinsGeneral ℚ).U N ↔
      glFin (𝓞 ℚ) ℚ u ∈ finiteLevelOne (𝓞 ℚ) ℚ N ∧ glArch (𝓞 ℚ) ℚ u = 1 := by
  show u ∈ levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ ↔ _
  rw [Subgroup.mem_inf, mem_levelOne_iff, mem_finiteAdelicGL2Subgroup_iff]

end Ws41.B4

theorem Ws41.B4.apply_mul_eq_of_mem_U
    {M : ℕ} [NeZero M] {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    (g u : AdelicGL2 (𝓞 ℚ) ℚ) (hu : u ∈ (productionPinsGeneral ℚ).U (AdelicDock.ratLevel M)) :
    Φ (g * u) = Φ g := by
  obtain ⟨hfin, harch⟩ := (Ws41.B4.mem_productionPinsGeneral_U_iff _ u).mp hu
  rw [← Ws41.B4.finEmbed_glFin_of_glArch_eq_one u harch]
  exact hΦ.level_inv _ hfin g

theorem solution
    {M : ℕ} [NeZero M] {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) :
    IsKfSmooth ℚ Φ := by
  have hN : AdelicDock.ratLevel M ≠ ⊥ := AdelicDock.ratLevel_ne_bot (NeZero.ne M)
  rw [AutomorphicForm.isKfSmooth_iff, FLT.SmoothVectors.isSmoothVector_iff_exists_isOpen_subgroup]
  refine ⟨(NumberField.AdelicLevel.levelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M)).subgroupOf
      (AutomorphicForm.finiteAdelicGL2Subgroup ℚ), ?_, ?_⟩
  · exact (NumberField.AdelicLevel.isOpen_levelOne (𝓞 ℚ) ℚ hN).preimage continuous_subtype_val
  · intro u hu
    rw [Subgroup.mem_subgroupOf] at hu
    rw [Subgroup.smul_def]
    refine FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_
    rw [FLT.SmoothVectors.RightTranslationFn.toFun_smul, FLT.SmoothVectors.RightTranslationFn.toFun_mk]
    exact Ws41.B4.apply_mul_eq_of_mem_U hΦ x u (show (u : AdelicGL2 (𝓞 ℚ) ℚ) ∈ _ from ⟨hu, u.2⟩)

end S_CuspForm_IsAdelicLiftOfGamma1_isKfSmooth
end P2MW
export P2MW.S_CuspForm_IsAdelicLiftOfGamma1_isKfSmooth (solution)
