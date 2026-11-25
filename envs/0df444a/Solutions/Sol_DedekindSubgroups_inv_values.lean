-- Prove2me | solution 1 for DedekindSubgroups.inv_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:12:52.430889+00:00
-- url     : https://prove2.me/submissions/57574ed5-2518-4fe8-b0bf-675bd6b73a25

module
public import Definitions.Def_DedekindSubgroups_Prime
public import Definitions.Def_DedekindSubgroups_Optimality

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
set_option maxRecDepth 100000
namespace DedekindSubgroups
theorem _root_.solution : inv 4 63 = 720 ∧ inv 16 63 = 720 ∧ inv 22 63 = 882 ∧ inv 43 63 = 882 := by
  refine ⟨by decide, by decide, by decide, by decide⟩
end DedekindSubgroups
