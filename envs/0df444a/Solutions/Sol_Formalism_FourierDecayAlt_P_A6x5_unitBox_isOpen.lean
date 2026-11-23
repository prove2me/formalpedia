-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x5.unitBox_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:00.369207+00:00
-- url     : https://prove2.me/submissions/47ab53d4-7d9d-426b-b368-0ed6ed303f1a

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_one_add_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_image_pow_eq_preimage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.DoubleCosetMeasures Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x5
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x5
theorem _root_.solution (hD : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (ϖ : Kˣ) (hϖR : (ϖ : K) ∈ R) (hϖ : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) (j : ℕ) :
    IsOpen (unitBox R ϖ j) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨y, hzy, hz, hy⟩
  have hO : IsOpen ((fun w => ((ϖ⁻¹ : Kˣ) : K) ^ (j + 1) * (w - z)) ⁻¹' (R : Set K)) :=
    hD.isOpen.preimage (continuous_const.mul (continuous_id.sub continuous_const))
  refine Filter.mem_of_superset (hO.mem_nhds ?_) ?_
  · change ((ϖ⁻¹ : Kˣ) : K) ^ (j + 1) * (z - z) ∈ R
    rw [sub_self, mul_zero]
    exact R.zero_mem
  · intro w hw
    have hw' : w - z ∈ (fun x => ((ϖ⁻¹ : Kˣ) : K) ^ (j + 1) * x) ⁻¹' (R : Set K) := hw
    rw [← image_pow_eq_preimage] at hw'
    obtain ⟨r, hr, hrw⟩ := hw'
    have hrw' : (ϖ : K) ^ (j + 1) * r = w - z := hrw
    have hwz : w = z + (ϖ : K) ^ (j + 1) * r := by rw [hrw']; ring
    obtain ⟨u, hu, hu1⟩ := one_add_unit hD hn ϖ hϖR hϖ (r * ((ϖ : K) ^ j * y)) (R.mul_mem hr hy)
    refine ⟨y * u, ?_, ?_, ?_⟩
    · calc w * (y * u) = (z * y + (ϖ : K) * (r * ((ϖ : K) ^ j * y))) * u := by rw [hwz]; ring
        _ = 1 := by rw [hzy, hu1]
    · have : (ϖ : K) ^ j * w = (ϖ : K) ^ j * z + (ϖ : K) ^ j * (ϖ : K) ^ (j + 1) * r := by
        rw [hwz]; ring
      rw [this]
      exact R.add_mem hz (R.mul_mem (R.mul_mem (R.pow_mem hϖR _) (R.pow_mem hϖR _)) hr)
    · rw [← mul_assoc]
      exact R.mul_mem hy hu
end Formalism.FourierDecayAlt.P.A6x5
