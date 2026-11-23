-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz3.pair_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:37.826361+00:00
-- url     : https://prove2.me/submissions/5c5e4087-fe58-4a3e-a2b4-8c9c986ee0ac

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz3
theorem _root_.solution (J : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ i ∈ Icc 1 J, ∑ i' ∈ Ioc i J, f i i' = ∑ d ∈ Icc 1 J, ∑ i ∈ Icc 1 (J - d), f i (i + d) := by
  have h : ∀ i, ∑ i' ∈ Ioc i J, f i i' = ∑ d ∈ Icc 1 (J - i), f i (i + d) := by
    intro i
    apply Finset.sum_nbij' (fun i' => i' - i) (fun d => i + d)
    · intro a ha; simp only [mem_Ioc, mem_Icc] at *; omega
    · intro a ha; simp only [mem_Ioc, mem_Icc] at *; omega
    · intro a ha; simp only [mem_Ioc] at *; omega
    · intro a ha; simp only [mem_Icc] at *; omega
    · intro a ha
      simp only [mem_Ioc] at ha
      have : i + (a - i) = a := by omega
      rw [this]
  simp_rw [h]
  apply Finset.sum_comm'
  intro i d
  simp only [mem_Icc]
  omega
end Formalism.FourierDecayAlt.P.Sz3
