-- Prove2me | solution 1 for Formalism.L2.SG.PiMeasureScaling.pi_reindex_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:58:21.616342+00:00
-- url     : https://prove2.me/submissions/0d198f5a-ec46-4422-a6a0-e45298d9aa8e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_PiMeasureScaling
import Theorems.Thm_Formalism_L2_SG_PiMeasureScaling_sf_smul
import Theorems.Thm_Formalism_L2_SG_PiMeasureScaling_pi_smul_vol
import Theorems.Thm_Formalism_L2_SG_PiMeasureScaling_map_scale
import Theorems.Thm_Formalism_L2_SG_PiMeasureScaling_reindex_mp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.PiMeasureScaling
namespace Formalism.L2.SG.PiMeasureScaling
theorem _root_.solution {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (a : ℝ≥0∞) (ha : a ≠ ⊤) (s : ι → ℂ) (hs : ∀ i, s i ≠ 0) :
    (Measure.pi (fun _ : κ => a • (volume : Measure ℂ))).map (fun y i => s i * y (e i)) =
      (∏ i, a * ENNReal.ofReal (Complex.normSq (s i))⁻¹) • (volume : Measure (ι → ℂ)) := by
  classical
  have hk : Measure.pi (fun _ : κ => a • (volume : Measure ℂ)) =
      (∏ _k : κ, a) • (volume : Measure (κ → ℂ)) := pi_smul_vol (fun _ => a) (fun _ => ha)
  have hsc : (volume : Measure (ι → ℂ)).map (fun x i => s i * x i) =
      (∏ i, ENNReal.ofReal (Complex.normSq (s i))⁻¹) • (volume : Measure (ι → ℂ)) := by
    haveI : ∀ i, SigmaFinite (Measure.map (fun x => s i * x) (volume : Measure ℂ)) := fun i => by
      rw [map_scale _ (hs i)]
      exact sf_smul _ ENNReal.ofReal_ne_top
    rw [volume_pi, Measure.pi_map_pi (fun i => (measurable_const_mul (s i)).aemeasurable)]
    simp_rw [map_scale _ (hs _)]
    rw [pi_smul_vol _ (fun i => ENNReal.ofReal_ne_top), volume_pi]
  have hcomp : (fun (y : κ → ℂ) (i : ι) => s i * y (e i)) =
      (fun (x : ι → ℂ) i => s i * x i) ∘ (fun (y : κ → ℂ) (i : ι) => y (e i)) := rfl
  rw [hk, Measure.map_smul, hcomp,
    ← Measure.map_map (measurable_pi_lambda _ fun i => (measurable_pi_apply i).const_mul (s i))
      (reindex_mp e).measurable, (reindex_mp e).map_eq, hsc, smul_smul]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const, Finset.card_univ,
    Finset.card_univ, Fintype.card_congr e]
end Formalism.L2.SG.PiMeasureScaling
