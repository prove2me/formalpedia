-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FiniteSumSwap.finsum_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:13.056785+00:00
-- url     : https://prove2.me/submissions/90231364-b779-46c0-94d0-36b01a039a35

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumSwap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FiniteSumSwap
namespace Formalism.FourierDecayAlt.P.FiniteSumSwap
theorem _root_.solution {I J : Type} (P : I → Prop) [DecidablePred P] (T : J → Prop) [DecidablePred T]
    (hP : {q | P q}.Finite) (hT : {z | T z}.Finite) (a : ℂ) (g : J → ℂ) (F : J → I → ℂ)
    (e : I → ℂ) :
    ∑ᶠ q : I, (if P q then a * ∑ᶠ z : J, (if T z then g z * F z q else 0) else 0) * e q =
      a * ∑ᶠ z : J, (if T z then g z * ∑ᶠ q : I, (if P q then F z q else 0) * e q else 0) := by
  have h1 : ∀ f : I → ℂ, ∑ᶠ q : I, (if P q then f q else 0) * e q =
      ∑ q ∈ hP.toFinset, f q * e q := by
    intro f
    rw [finsum_eq_sum_of_support_subset (s := hP.toFinset)]
    · refine Finset.sum_congr rfl fun q hq => ?_
      rw [if_pos (by simpa using hq)]
    · intro q hq
      by_contra hq'
      have : ¬ P q := by simpa using hq'
      simp [this] at hq
  have h2 : ∀ f : J → ℂ, ∑ᶠ z : J, (if T z then f z else 0) = ∑ z ∈ hT.toFinset, f z := by
    intro f
    rw [finsum_eq_sum_of_support_subset (s := hT.toFinset)]
    · refine Finset.sum_congr rfl fun z hz => ?_
      rw [if_pos (by simpa using hz)]
    · intro z hz
      by_contra hz'
      have : ¬ T z := by simpa using hz'
      simp [this] at hz
  rw [h1, h2]
  simp_rw [h1, h2]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun q _ => ?_
  ring
end Formalism.FourierDecayAlt.P.FiniteSumSwap
