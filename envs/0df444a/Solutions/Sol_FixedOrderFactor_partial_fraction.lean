-- Prove2me | solution 1 for FixedOrderFactor.partial_fraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:15.615643+00:00
-- url     : https://prove2.me/submissions/8a105d82-fdf0-417d-b7ef-3f1a53c63c2f

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Local

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Complex Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {a b t : ℂ} (ha : 1 - a ≠ 0) (hb : 1 - b ≠ 0) (hab : a * b = t)
    (ht : 1 - t ≠ 0) :
    1 / ((1 - a) * (1 - b)) = (1 / (1 - t)) * (1 / (1 - a) + 1 / (1 - b) - 1) := by
  subst hab
  field_simp
  ring
end FixedOrderFactor
