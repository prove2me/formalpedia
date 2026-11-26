-- Prove2me | solution 1 for CSeparatedNPComplete.Karamata_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:59:01.295893+00:00
-- url     : https://prove2.me/submissions/d586588f-61fb-438a-85ec-07561b9bc25e

module
public import Definitions.Def_CSeparatedNPComplete
public import Definitions.Def_CSeparatedNPComplete_Solution
public import Theorems.Thm_CSeparatedNPComplete_convexOnPredicate_iff_convexOn
public import Theorems.Thm_CSeparatedNPComplete_majorized_sum_convex_le


set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution
    (n : Nat) (P : Real → Prop) (f : Real → Real) (u v : Vec n)
    (hconv : convexOnPredicate P f)
    (Pu : ∀ i, P (u i)) (Pv : ∀ i, P (v i))
    (hmajorized : majorized u v) :
    vecSum (fun i => f (u i)) ≥ vecSum (fun i => f (v i)) := by
  exact hmajorized.sum_convex_le ((convexOnPredicate_iff_convexOn P f).mp hconv) Pu Pv
end CSeparatedNPComplete
