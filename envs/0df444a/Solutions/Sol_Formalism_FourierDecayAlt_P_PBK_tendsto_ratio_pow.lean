-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.tendsto_ratio_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:33:18.975927+00:00
-- url     : https://prove2.me/submissions/70462610-898a-473c-bf99-4b8661c7e591

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemLpBzOfSup
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoIntegralInnerGermMoving
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoRatioPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution (s : ℕ) (a b : ℂ) :
    Tendsto (fun x : ℂ => (x + a) ^ (s - 1) / (x + b) ^ (s - 1)) (cocompact ℂ) (𝓝 1) := by
  have hn : Tendsto (fun x : ℂ => ‖x + b‖) (cocompact ℂ) atTop := by
    have h0 : Tendsto (fun x : ℂ => ‖x‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
    refine tendsto_atTop_mono (fun x => ?_) (tendsto_atTop_add_const_right _ (-‖b‖) h0)
    have := norm_sub_norm_le x (-b)
    rw [norm_neg, sub_neg_eq_add] at this
    linarith
  have hi : Tendsto (fun x : ℂ => (x + b)⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact (tendsto_inv_atTop_zero.comp hn).congr fun x => by simp [norm_inv]
  have hne : ∀ᶠ x in cocompact ℂ, x + b ≠ 0 :=
    (hn.eventually_gt_atTop 0).mono fun x hx => norm_pos_iff.mp hx
  have hq : Tendsto (fun x : ℂ => 1 + (a - b) * (x + b)⁻¹) (cocompact ℂ) (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℂ))).add ((tendsto_const_nhds (x := a - b)).mul hi)
  have hp := hq.pow (s - 1)
  rw [one_pow] at hp
  refine hp.congr' ?_
  filter_upwards [hne] with x hx
  rw [← div_pow]
  congr 1
  first
  | (field_simp; ring)
  | field_simp
end Formalism.FourierDecayAlt.P.PBK
