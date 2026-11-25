-- Prove2me | solution 1 for DedekindSubgroups.E_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:08:51.798986+00:00
-- url     : https://prove2.me/submissions/46f237f1-9224-4336-9040-3d8c8a14bd57

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
namespace DedekindSubgroups
theorem _root_.solution (h k : ℕ) : ((E h k : ℤ) : ℚ) = ∑ r ∈ range k, (r : ℚ) * sig h k r := by
  unfold E; push_cast; rfl
end DedekindSubgroups
