-- Prove2me | solution 1 for DeletionCode.MaximalRuns.eraseIdx_same_in_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:09.663058+00:00
-- url     : https://prove2.me/submissions/b71ab81d-abc2-43df-85f5-13ea47921f96

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns
import Theorems.Thm_DeletionCode_MaximalRuns_eraseIdx_in_run

set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns
namespace DeletionCode.MaximalRuns
theorem _root_.solution (pre suffix : List Bool) (rho : ℕ) (bit : Bool) (p q : ℕ)
    (hp : pre.length ≤ p) (hp' : p < pre.length + rho)
    (hq : pre.length ≤ q) (hq' : q < pre.length + rho) :
    (pre ++ List.replicate rho bit ++ suffix).eraseIdx p =
      (pre ++ List.replicate rho bit ++ suffix).eraseIdx q := by
  rw [eraseIdx_in_run pre suffix rho bit p hp hp', eraseIdx_in_run pre suffix rho bit q hq hq']
end DeletionCode.MaximalRuns
