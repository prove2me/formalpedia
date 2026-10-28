-- Prove2me | solution 1 for FinancialDerivatives.FD03.european_smul
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:05:12.552231+00:00
-- url     : https://prove2.me/submissions/245f81ab-53c4-436c-bff2-47697893a453

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_payoffTreeMap
import Mathlib.Tactic
import Definitions.Def_fd03_oneStepValue
open FinancialDerivatives.FD03


open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket) (n : ℕ)
    (a : ℝ) (claim : PayoffTree n) :
    europeanValue m n (payoffTreeMap (fun x => a * x) n claim) =
      a * europeanValue m n claim := by


  induction claim with
  | leaf c => rfl
  | branch u d ihu ihd =>
    show oneStepValue m (europeanValue m _ (payoffTreeMap _ _ u)) (europeanValue m _ (payoffTreeMap _ _ d)) = _
    rw [ihu, ihd]
    show _ = a * oneStepValue m _ _
    unfold oneStepValue
    ring
