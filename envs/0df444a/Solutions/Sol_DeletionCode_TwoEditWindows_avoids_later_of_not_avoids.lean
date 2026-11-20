-- Prove2me | solution 1 for DeletionCode.TwoEditWindows.avoids_later_of_not_avoids
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:11.31545+00:00
-- url     : https://prove2.me/submissions/3b2c860e-6d56-434b-b598-324873c221d7

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_TwoEditWindows

set_option autoImplicit true
open DeletionCode DeletionCode.TwoEditWindows
namespace DeletionCode.TwoEditWindows
theorem _root_.solution {k start next edit : ℕ}
    (hgap : start + k ≤ next) (hbad : ¬ Avoids k start edit) :
    Avoids k next edit := by
  unfold Avoids at *
  right
  omega
end DeletionCode.TwoEditWindows
