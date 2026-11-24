-- Prove2me | solution 1 for Formalism.QuantumDeterminants.prod_lt_sub_eq_factorial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:34:14.920418+00:00
-- url     : https://prove2.me/submissions/9998ddc8-1465-42d7-b13b-567ccc5b46f6

import Definitions.Def_Formalism_FormalDegreeBessel_HolDimLowK
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_HolomorphicLowKDimensionHolds
import Theorems.Thm_Formalism_QuantumDeterminants_prod_range_sub_cast_eq_factorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
namespace Formalism.QuantumDeterminants
theorem _root_.solution {n : ℕ} (b : Fin n) :
    ∏ a ∈ univ.filter (fun a : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      (((b : ℕ).factorial : ℕ) : ℝ) := by
  rw [Finset.prod_filter]
  have h1 : (∏ a : Fin n, (if a < b then (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) else 1)) =
      ∏ i ∈ range n, (if i < (b : ℕ) then (((b : ℕ) : ℝ) - (i : ℝ)) else 1) := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => if i < (b : ℕ) then (((b : ℕ) : ℝ) - (i : ℝ)) else 1) n]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp only [Fin.lt_def]
  rw [h1, ← Finset.prod_filter]
  have h2 : (range n).filter (fun i => i < (b : ℕ)) = range (b : ℕ) := by
    ext i; simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨lt_trans h b.isLt, h⟩
  rw [h2, prod_range_sub_cast_eq_factorial]
end Formalism.QuantumDeterminants
