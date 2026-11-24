-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.Lv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:38:45.479232+00:00
-- url     : https://prove2.me/submissions/201fac9f-237b-4ac7-8fb9-23af7ce79951

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_shear
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_coord_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Kf_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_k2map_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_tb_coord
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Kg_meas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
attribute [local instance] isAddHaarMeasure_matrix_volume
attribute [local instance] haar_prod2
open scoped Pointwise
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (F : Frame H Ep Em) : ∃ c : ℝ≥0, 0 < c ∧ ∀ ρ : ℝ, Lv H Ep Q ρ = c * Mv P Q ρ := by
  obtain ⟨c, hc, hmap⟩ := coord_meas F
  refine ⟨c, hc, fun ρ => ?_⟩
  have hK : Measurable (fun p : (Q → P → ℂ) × (Q → Q → ℂ) => Kf P Q ρ (swapBlockPair p)) :=
    (Kf_meas ρ).comp k2map_cont.measurable
  have he : Measurable (coordE F) :=
    (LinearMap.continuous_of_finiteDimensional (coordE F).toLinearMap).measurable
  calc Lv H Ep Q ρ = ∫⁻ Y : Q → m → ℂ, Kf P Q ρ (swapBlockPair (coordE F Y)) := by
        unfold Lv Ff; simp_rw [tb_coord F]
    _ = ∫⁻ p, Kf P Q ρ (swapBlockPair p) ∂((volume : Measure (Q → m → ℂ)).map (coordE F)) := (lintegral_map hK he).symm
    _ = c * ∫⁻ p, Kf P Q ρ (swapBlockPair p) ∂((volume : Measure (Q → P → ℂ)).prod (volume : Measure (Q → Q → ℂ))) := by
        rw [hmap, lintegral_smul_measure]; rfl
    _ = c * ∫⁻ B : Q → P → ℂ, ∫⁻ X : Q → Q → ℂ, Kf P Q ρ (swapBlockPair (B, X)) := by
        rw [lintegral_prod _ hK.aemeasurable]
    _ = c * ∫⁻ B : Q → P → ℂ, ∫⁻ X : Q → Q → ℂ, Kf P Q ρ (gramF X, B) := by
        congr 1
        refine lintegral_congr fun B => ?_
        exact shear (cm B) (fun T => Kf P Q ρ (T, B)) ((Kf_meas ρ).comp (measurable_id.prodMk measurable_const))
          (fun T hT => Set.indicator_of_notMem (show ((T : Q → Q → ℂ), B) ∉ Kset P Q ρ from fun h => hT h.1) _)
    _ = c * Mv P Q ρ := by
        rw [lintegral_lintegral_swap]
        · rfl
        · exact ((Kg_meas ρ).comp measurable_swap).aemeasurable
end Formalism.FourierDecayAlt.P.HermitianFormFactor
