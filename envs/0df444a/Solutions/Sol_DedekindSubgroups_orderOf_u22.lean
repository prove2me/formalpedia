-- Prove2me | solution 1 for DedekindSubgroups.orderOf_u22
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:11:52.942903+00:00
-- url     : https://prove2.me/submissions/57f97d35-0020-4d09-9fb6-d7f90c2a1fbc

module
public import Definitions.Def_DedekindSubgroups_Prime
public import Definitions.Def_DedekindSubgroups_Optimality

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
namespace DedekindSubgroups
theorem _root_.solution : orderOf u22 = 3 := orderOf_eq_prime (by decide) (by decide)
end DedekindSubgroups
