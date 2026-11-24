-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ProjectiveLineModels.projective_lines_power_hypothesis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:34:31.731854+00:00
-- url     : https://prove2.me/submissions/3424561b-e655-4ec5-978e-38d7b54e100c

import Definitions.Def_Formalism_SizeWindowBrackets_JointDPublishedSizes
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ProjectiveLines
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_line_model_input_sizes
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_line_rank_sum_eq
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_projective_lines_geometry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.ProjectiveLineModels
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)
open Formalism.LFunctionChainParameters.MatrixLatticeEstimates
variable (p : ℕ) [Fact p.Prime]
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
namespace Formalism.LFunctionChainParameters.ProjectiveLineModels
theorem _root_.solution (hp19 : 19 ≤ p) (v : InfinitePlace K) :
    ∃ (h : Option (ZMod p) × ZMod p → ℝ) (s u : ℝ), 0 ≤ u ∧ ∀ HH U : ℝ,
      s - muMinDef (Pi.basisFun K (ZMod p × ZMod p)) (fun _ => 1) (stdLat K (ZMod p × ZMod p)) ≤ HH →
      0 < HH → u ≤ U →
      HypBPow (κ₁ := Empty) (V := fun _ : Option (ZMod p) × ZMod p => ZMod p → K) (ι := fun _ => ZMod p)
        (Pi.basisFun K (ZMod p × ZMod p)) (fun _ => 1) (stdLat K (ZMod p × ZMod p))
        (fun _ => Pi.basisFun K (ZMod p)) (fun _ _ => 1) (fun _ => stdLat K (ZMod p)) (lineMap K p) h v
        (fun _ => 1) 1 (lineMat p) (fun _ => 1) (ιf := fun _ => ZMod p) (lineMat p) (fun _ => 1)
        s u U HH 0 ((p : ℝ) ^ 2) 0 0 0 0 (HH / ((p : ℝ) + 1)) ((p : ℝ) + 1) 1 := by
  have hpR : (19 : ℝ) ≤ p := by exact_mod_cast hp19
  set hh : Option (ZMod p) × ZMod p → ℝ := fun i => htMap (Pi.basisFun K (ZMod p)) (fun _ => 1)
    (Pi.basisFun K (ZMod p × ZMod p)) (fun _ => 1) (lineMap K p i) with hhh
  set mu : Option (ZMod p) × ZMod p → ℝ :=
    fun i => muDef (Pi.basisFun K (ZMod p)) (fun _ => 1) (stdLat K (ZMod p)) - hh i with hmu
  set s : ℝ := (∑ i : Option (ZMod p) × ZMod p, (Fintype.card (ZMod p) : ℝ) * mu i)
    / ∑ _i : Option (ZMod p) × ZMod p, (Fintype.card (ZMod p) : ℝ) with hs
  set u : ℝ := ∑ i : Option (ZMod p) × ZMod p,
    |muMaxDef (Pi.basisFun K (ZMod p)) (fun _ => 1) (stdLat K (ZMod p)) - hh i - s| with hu
  have hR : (0 : ℝ) < ∑ _i : Option (ZMod p) × ZMod p, (Fintype.card (ZMod p) : ℝ) := by
    have := line_rank_sum_eq p
    unfold RsG at this
    rw [this]
    positivity
  have hu0 : 0 ≤ u := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨hh, s, u, hu0, fun HH U h1 h2 h3 => ?_⟩
  have num : LatNum (V := fun _ : Option (ZMod p) × ZMod p => ZMod p → K) (ι := fun _ => ZMod p)
      (Pi.basisFun K (ZMod p × ZMod p)) (fun _ => 1) (stdLat K (ZMod p × ZMod p))
      (fun _ => Pi.basisFun K (ZMod p)) (fun _ _ => 1) (fun _ => stdLat K (ZMod p)) hh s u HH := by
    refine ⟨?_, hu0, fun i => ?_, h1, h2.le⟩
    · rw [hs, div_mul_cancel₀ _ hR.ne']
    · have k1 := le_abs_self (muMaxDef (Pi.basisFun K (ZMod p)) (fun _ => 1) (stdLat K (ZMod p)) - hh i - s)
      have k2 : |muMaxDef (Pi.basisFun K (ZMod p)) (fun _ => 1) (stdLat K (ZMod p)) - hh i - s| ≤ u :=
        Finset.single_le_sum
          (f := fun i => |muMaxDef (Pi.basisFun K (ZMod p)) (fun _ => 1) (stdLat K (ZMod p)) - hh i - s|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
      linarith
  have hx0 : (0 : ℝ) < (p : ℝ) + 1 := by linarith
  have hx : ((p : ℝ) + 1) ^ (-(1 : ℝ)) = 1 / ((p : ℝ) + 1) := by
    rw [Real.rpow_neg hx0.le, Real.rpow_one, one_div]
  have hx20 : 1 / ((p : ℝ) + 1) ≤ 1 / 20 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hxp : 0 < 1 / ((p : ℝ) + 1) := by positivity
  refine ⟨projective_lines_geometry p K v, num, fun _ => one_pos, fun _ => by simp, fun _ => by simp, by positivity,
    by rw [hx]; exact hx20, ?_, by norm_num, by rw [hx]; positivity, by rw [hx]; positivity, le_rfl, le_rfl,
    ?_, ?_, line_model_input_sizes p, by linarith, by norm_num, by positivity, ?_, h3, by norm_num⟩
  · rw [Real.rpow_one, line_rank_sum_eq]
  · rw [hx]; simpa using hxp.le
  · simp
  · rw [Real.rpow_one, mul_div_cancel₀ _ hx0.ne']
end Formalism.LFunctionChainParameters.ProjectiveLineModels
