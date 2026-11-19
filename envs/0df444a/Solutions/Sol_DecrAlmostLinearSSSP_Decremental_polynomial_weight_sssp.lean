-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.polynomial_weight_sssp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T17:37:39.718193+00:00
-- url     : https://prove2.me/submissions/08f8efbb-913b-46d9-ac2b-4079eb3c76b4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_13
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_dynamic_cut_interface
set_option autoImplicit false
open DecrAlmostLinearSSSP.Decremental
theorem solution :
    ∀ exponent : ℕ, ∃ (p : Program) (C : ℝ) (a : ℕ → ℝ) (queryBound : ℕ),
      0 < C ∧ 0 < queryBound ∧ Subpolynomial a ∧
      (∀ i : Input, i.Valid → 2 ≤ i.n → i.W ≤ i.size ^ exponent →
        1 / (i.size : ℝ) < i.accuracy → i.accuracy < 1 →
        Maintains p C a queryBound false i) ∧
      (∀ (b : Core) (K : ℝ), 32 ≤ K → ∀ choose : State b → CutReply b,
        CutQuality b K choose → ∀ s, Attained b K choose s →
        (s.toggles : ℝ) ≤ 16 * K ^ 3 * A b * b.input.size * Real.log (2 * Q b)) := by
  intro d
  apply (DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.2.2.2.2.2.2.2) d
  exact (DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13.2.2.2.2.2.2.1) (d+3) (dynamic_cut_interface (4*(d+3)+68))
