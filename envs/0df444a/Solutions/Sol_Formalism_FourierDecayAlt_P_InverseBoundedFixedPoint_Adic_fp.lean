-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.fp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:40.001038+00:00
-- url     : https://prove2.me/submissions/e68fd620-19b2-4fb6-9f61-eb2c0e30ee55

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_I_compact
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_sep
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_I_anti
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_fixed_point

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
theorem _root_.solution (h : Adic R ϖ) {E ι : Type} [TopologicalSpace E] (co : ι → E → K)
    (hco : ∀ i, Continuous (co i)) (hinj : ∀ x y, (∀ i, co i x = co i y) → x = y)
    (X : Set E) (hX : IsCompact X) (hXc : IsClosed X) (hne : X.Nonempty)
    (hXR : ∀ x ∈ X, ∀ i, co i x ∈ R) (T : E → E) (hT : ∀ x ∈ X, T x ∈ X)
    (hc : ∀ n, ∀ x ∈ X, ∀ y ∈ X, (∀ i, co i x - co i y ∈ I R ((ϖ : K) ^ n)) →
      ∀ i, co i (T x) - co i (T y) ∈ I R ((ϖ : K) ^ (n + 1))) : ∃ x ∈ X, T x = x := by
  have := h.t2
  refine fixed_point X hX hXc hne (fun n x y => ∀ i, co i x - co i y ∈ I R ((ϖ : K) ^ n))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ T hT hc
  · intro n y
    have : {x | ∀ i, co i x - co i y ∈ I R ((ϖ : K) ^ n)} =
        ⋂ i, (fun x => co i x - co i y) ⁻¹' I R ((ϖ : K) ^ n) := by
      ext x; simp
    rw [this]
    exact isClosed_iInter fun i =>
      (I_compact h.isCompact _).isClosed.preimage ((hco i).sub continuous_const)
  · intro x hx y hy i
    exact ⟨_, R.sub_mem (hXR x hx i) (hXR y hy i), by simp⟩
  · intro n x i
    exact ⟨0, R.zero_mem, by simp⟩
  · intro n x y hxy i
    exact I_anti h.mem (Nat.le_succ n) (hxy i)
  · intro n x y z h1 h2 i
    obtain ⟨r, hr, e⟩ := h1 i
    obtain ⟨r', hr', e'⟩ := h2 i
    exact ⟨r + r', R.add_mem hr hr', by linear_combination e + e'⟩
  · intro n x y h1 i
    obtain ⟨r, hr, e⟩ := h1 i
    exact ⟨-r, R.neg_mem hr, by linear_combination -e⟩
  · intro x y hxy
    exact hinj x y fun i => sub_eq_zero.1 (h.sep _ fun n => hxy n i)
end Adic
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
