-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x8.Adic.root_near
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:12:23.087889+00:00
-- url     : https://prove2.me/submissions/c67ff8c1-4e69-4822-8ed9-2f2fe6096c28

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Adic_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x8
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.A6x8
namespace Adic
theorem _root_.solution (h : Adic R ϖ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (s : ℕ) (hs : 1 ≤ s)
    {E : Set K} (hE : E ∈ 𝓝 (0 : K)) :
    ∃ a : Kˣ, (a : K) ∈ I R (ϖ : K) ∧ ∀ b : K, Near R (a : K) b → ∃ κ : K, κ ^ s = b ∧ κ - 1 ∈ E := by
  obtain ⟨N, hN⟩ := h.basis E hE
  obtain ⟨u, hu⟩ := hn s (by omega)
  have hsR : (s : K) ∈ R := natCast_mem R s
  refine ⟨u ^ 2 * ϖ ^ (N + 1), ⟨(s : K) ^ 2 * (ϖ : K) ^ N,
    R.mul_mem (R.pow_mem hsR 2) (R.pow_mem h.mem N), by push_cast; rw [hu]; ring⟩, fun b hb => ?_⟩
  have hb' : Near R ((s : K) ^ 2 * (ϖ : K) ^ (N + 1)) b := by
    have e : ((u ^ 2 * ϖ ^ (N + 1) : Kˣ) : K) = (s : K) ^ 2 * (ϖ : K) ^ (N + 1) := by
      push_cast; rw [hu]
    rwa [e] at hb
  obtain ⟨κ, ⟨r, hr, e⟩, hκ⟩ := h.root s (c := (ϖ : K) ^ (N + 1))
    ⟨(ϖ : K) ^ N, R.pow_mem h.mem N, by ring⟩ hb'
  refine ⟨κ, hκ, ?_⟩
  have : κ - 1 = (ϖ : K) ^ N * ((ϖ : K) * (s : K) * r) := by rw [e]; ring
  rw [this]
  exact hN _ (R.mul_mem (R.mul_mem h.mem hsR) hr)
end Adic
end Formalism.FourierDecayAlt.P.A6x8
