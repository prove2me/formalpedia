-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.sum_frameM_row
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:41.596425+00:00
-- url     : https://prove2.me/submissions/13445ebe-1c64-4ead-9e59-cc7057ee0472

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {K : Type} [NormedField K] [CharZero K] {d N0 N1 : ℕ} [NeZero d]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (x : ZMod d × Fin N0 × Fin N0 → K) (s : ZMod d) (i : Fin N0) (b : Fin N1) :
    (∑ j : ZV d N0 N1, MvPolynomial.C (frameM (N1 := N1) x j (s, i, b)) * MvPolynomial.X j :
      MvPolynomial (ZV d N0 N1) K) =
      ∑ a : Fin N0, MvPolynomial.C (x (s, i, a)) * MvPolynomial.X (s, a, b) := by
  rw [show (∑ j : ZV d N0 N1, MvPolynomial.C (frameM (N1 := N1) x j (s, i, b)) * MvPolynomial.X j :
      MvPolynomial (ZV d N0 N1) K) =
      ∑ j : ZV d N0 N1, if j.1 = s ∧ j.2.2 = b then
        MvPolynomial.C (x (s, i, j.2.1)) * MvPolynomial.X (s, j.2.1, b) else 0 from
    Finset.sum_congr rfl fun j _ => ?_]
  · rw [Fintype.sum_prod_type]
    simp [Fintype.sum_prod_type, ite_and]
  · obtain ⟨t, a, c⟩ := j
    simp only [frameM]
    by_cases h : t = s ∧ c = b
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [if_neg (fun hh => h ⟨hh.1.symm, hh.2.symm⟩), if_neg h]
      simp
end Formalism.DworkPowerSeriesWeights
