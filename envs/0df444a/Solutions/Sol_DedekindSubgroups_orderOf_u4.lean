-- Prove2me | solution 1 for DedekindSubgroups.orderOf_u4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:11:49.228561+00:00
-- url     : https://prove2.me/submissions/3b3e7858-dfd6-4d08-a95b-ae40ee98c0f5

module
public import Definitions.Def_DedekindSubgroups_Prime
public import Definitions.Def_DedekindSubgroups_Optimality

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
namespace DedekindSubgroups
theorem _root_.solution : orderOf u4 = 3 := orderOf_eq_prime (by decide) (by decide)
end DedekindSubgroups
