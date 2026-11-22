-- Prove2me | solution 1 for Formalism.GM.M.SSD.coeff_kap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:56.925945+00:00
-- url     : https://prove2.me/submissions/d7b06f4f-6c71-4725-b35e-8d2b7b365643

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.SSD
open MvPolynomial Finset
variable {σ τ K : Type} [Field K] [DecidableEq σ]
namespace Formalism.GM.M.SSD
theorem _root_.solution (F : (τ →₀ ℕ) → (σ →₀ ℕ)) (hF : Function.Injective F) (Q : MvPolynomial σ K) (n : τ →₀ ℕ) :
    coeff n (kap F hF Q) = coeff (F n) Q := by
  classical
  rw [kap, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Finset.mem_preimage, mem_support_iff, not_not] at h; exact h.symm
end Formalism.GM.M.SSD
