-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.root_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:07.400704+00:00
-- url     : https://prove2.me/submissions/860aaa9a-8755-4e43-9461-1c448d7a1012

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_pow_step

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
namespace Adic
theorem _root_.solution (h : Adic R ϖ) [IsReduced K] (s : ℕ) (hs : 1 ≤ s) :
    ∃ n0 : ℕ, ∀ v : K, v ^ s ∈ R → (ϖ : K) ^ n0 * v ∈ R := by
  obtain ⟨n0, hn0⟩ := h.pow_step s
  refine ⟨n0, fun v hv => ?_⟩
  have key : ∀ k : ℕ, (ϖ : K) ^ k * v ∈ R → (ϖ : K) ^ n0 * v ∈ R := by
    intro k
    induction k with
    | zero =>
      intro h0
      have := R.mul_mem (R.pow_mem h.mem n0) h0
      simpa using this
    | succ k ih =>
      intro hk
      by_cases hkn : k + 1 ≤ n0
      · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hkn
        have := R.mul_mem (R.pow_mem h.mem d) hk
        have e : (ϖ : K) ^ n0 * v = (ϖ : K) ^ d * ((ϖ : K) ^ (k + 1) * v) := by rw [hd]; ring
        rwa [e]
      · apply ih
        have h1 : ((ϖ : K) ^ (k + 1) * v) ^ s ∈ I R ((ϖ : K) ^ n0) := by
          have hle : n0 ≤ (k + 1) * s := by nlinarith
          obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
          exact ⟨(ϖ : K) ^ d * v ^ s, R.mul_mem (R.pow_mem h.mem d) hv, by
            rw [mul_pow, ← pow_mul, hd]; ring⟩
        obtain ⟨r, hr, e⟩ := hn0 _ hk h1
        have i1 : ((ϖ⁻¹ : Kˣ) : K) * (ϖ : K) = 1 := by simp
        have : (ϖ : K) ^ k * v = r := by
          linear_combination ((ϖ⁻¹ : Kˣ) : K) * e + (r - (ϖ : K) ^ k * v) * i1
        rwa [this]
  obtain ⟨k, hk⟩ := h.absorb v
  exact key k hk
end Adic
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
