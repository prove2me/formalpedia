-- Prove2me | solution 1 for FD1D.FiniteLaw.expect_timeAverage_eq_sum_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:46:02.426022+00:00
-- url     : https://prove2.me/submissions/921b0187-ec41-416d-a172-9781b4ea8eac

import Definitions.Def_FD1D_Expectations
import Definitions.Def_FD1D_Averaging
import Theorems.Thm_FD1D_FiniteLaw_expect_timeAverage

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteLaw
variable {α : Type*} [Fintype α]
namespace FD1D.FiniteLaw
theorem _root_.solution {T : ℕ} (hT : 0 < T)
    (μ : ℕ → FiniteLaw α) (f : ℕ → α → ℝ) :
    (timeAverage hT (fun t : Fin T => μ t)).expect
        (fun z => f z.1 z.2) =
      (∑ t ∈ Finset.range T, (μ t).expect (f t)) / (T : ℝ) := by
  rw [expect_timeAverage]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun t => (μ t).expect (f t)) T
end FD1D.FiniteLaw
