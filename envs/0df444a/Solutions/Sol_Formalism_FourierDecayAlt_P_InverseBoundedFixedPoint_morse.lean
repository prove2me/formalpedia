-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.morse
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:42.612818+00:00
-- url     : https://prove2.me/submissions/48755a80-cb92-4c1d-883d-26761af705bb

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_I_nhds
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_adic_of_datum
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_inv_bounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_root_bounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_morse_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
theorem _root_.solution : MorseLemma := by
  intro K _ _ _ R ψ hD hn m _ Q hQ hQu
  obtain ⟨ϖ, h⟩ := adic_of_datum hD hn
  have := hD.red
  have := hD.t2
  obtain ⟨M0, hM0⟩ := h.inv_bounded hQ hQu
  obtain ⟨n0, hn0⟩ := h.root_bounded (m + 1) (by omega)
  obtain ⟨u4, hu4⟩ := hn (4 * (m + 1)) (by omega)
  have h2 : IsUnit (2 : K) := by
    have := hn 2 (by omega)
    simpa using this
  have hcv : ((u4 * ϖ : Kˣ) : K) = 4 * ((m + 1 : ℕ) : K) * (ϖ : K) := by
    rw [Units.val_mul, hu4]; push_cast; ring
  refine ⟨I R ((ϖ ^ (n0 + M0) * (u4 * ϖ) : Kˣ) : K), I_nhds h.isOpen _, fun B hB hBV z hz => ?_⟩
  have hz' : (ϖ : K) ^ n0 * ((ϖ : K) ^ M0 * ((z⁻¹ : Kˣ) : K)) ∈ R := by
    apply hn0
    have h1 := hM0 _ hz ((((z⁻¹ : Kˣ) : K)) ^ (m + 1)) (by rw [← mul_pow]; simp)
    have e : ((ϖ : K) ^ M0 * ((z⁻¹ : Kˣ) : K)) ^ (m + 1) =
        ((ϖ : K) ^ M0) ^ m * ((ϖ : K) ^ M0 * (((z⁻¹ : Kˣ) : K)) ^ (m + 1)) := by ring
    rw [e]
    exact R.mul_mem (R.pow_mem (R.pow_mem h.mem _) _) h1
  obtain ⟨φ, h1, h2', h3⟩ := h.morse_local h2 m (u4 * ϖ) z hcv B hB.2.isClosed (fun b hb => by
    obtain ⟨r, hr, e⟩ := hBV hb
    refine ⟨_, R.mul_mem hz' hr, ?_⟩
    have i0 : (z : K) * ((z⁻¹ : Kˣ) : K) = 1 := by simp
    rw [e]
    push_cast
    linear_combination (-((ϖ : K) ^ (n0 + M0) * ((u4 : K) * (ϖ : K)) * r)) * i0)
  exact ⟨φ, h1, fun Λ _ => h2' Λ, h3⟩
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
