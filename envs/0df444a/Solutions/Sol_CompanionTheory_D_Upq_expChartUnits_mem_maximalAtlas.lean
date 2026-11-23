-- Prove2me | solution 1 for CompanionTheory.D.Upq.expChartUnits_mem_maximalAtlas
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:12.919243+00:00
-- url     : https://prove2.me/submissions/f2583d57-da2d-43de-b702-d0b6524df17f

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq
open scoped Manifold ContDiff Topology
open NormedSpace Set
set_option linter.unusedSectionVars false
variable (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]
local notation "𝔢" => expPartialHomeomorph 𝕂 𝔸
namespace CompanionTheory.D.Upq
theorem _root_.solution (g : 𝔸ˣ) (n : WithTop ℕ∞) :
    expChartUnits 𝕂 g ∈ IsManifold.maximalAtlas 𝓘(𝕂, 𝔸) n 𝔸ˣ := by
  rw [IsManifold.mem_maximalAtlas_iff]
  intro e' he'
  obtain rfl : e' = _ := he'
  have h1 : (expChartUnits 𝕂 g).symm ≫ₕ
      Units.isOpenEmbedding_val.toOpenPartialHomeomorph (Units.val : 𝔸ˣ → 𝔸) ∈
      contDiffGroupoid n 𝓘(𝕂, 𝔸) := by
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
    constructor
    · simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
        Function.id_comp, Function.comp_id, preimage_id_eq, range_id, inter_univ]
      exact (contDiff_const.mul (contDiff_exp 𝕂 𝔸)).contDiffOn.congr (fun X _ => rfl)
    · simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
        Function.id_comp, Function.comp_id, preimage_id_eq, range_id, inter_univ]
      set e0 := Units.isOpenEmbedding_val.toOpenPartialHomeomorph (Units.val : 𝔸ˣ → 𝔸)
      have hmaps : MapsTo (fun a : 𝔸 => ((g⁻¹ : 𝔸ˣ) : 𝔸) * a)
          ((expChartUnits 𝕂 g).symm ≫ₕ e0).symm.source (𝔢).target := by
        intro a ha
        rw [OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.trans_target] at ha
        have hr : ((e0.symm a : 𝔸ˣ) : 𝔸) = a := e0.right_inv ha.1
        have := ha.2
        simp only [mem_preimage] at this
        change (((g⁻¹ * e0.symm a : 𝔸ˣ) : 𝔸)) ∈ (𝔢).target at this
        rwa [Units.val_mul, hr] at this
      refine ((contDiffOn_expPartialHomeomorph_symm 𝕂 𝔸).comp
        (contDiff_const.mul contDiff_id).contDiffOn hmaps).congr ?_
      intro a ha
      rw [OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.trans_target] at ha
      have hr : ((e0.symm a : 𝔸ˣ) : 𝔸) = a := e0.right_inv ha.1
      show (𝔢).symm (((g⁻¹ * e0.symm a : 𝔸ˣ) : 𝔸)) = _
      rw [Units.val_mul, hr]; rfl
  refine ⟨h1, ?_⟩
  have := (contDiffGroupoid n 𝓘(𝕂, 𝔸)).symm h1
  rwa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm] at this
end CompanionTheory.D.Upq
