-- Prove2me | solution 1 for FixedOrderFactor.sqrtCount_imaginary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:11:36.518737+00:00
-- url     : https://prove2.me/submissions/d254931d-541a-4f8f-9c69-25ca527bfab4

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_sqrtCount_imaginary__18e778af86a9


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {r : ℕ} (hr : 0 < r) (hev : Even r) :
    (¬ 8 ∣ r → ∀ s, sqrtCount (2 * r) (1 + r) s = 0) ∧
      (∀ d, d ∣ r → ¬ 2 ∣ d → sqrtCount (2 * r) (1 + r) (r / d) = 0) :=
  sqrtCount_imaginary' hr hev
end FixedOrderFactor
