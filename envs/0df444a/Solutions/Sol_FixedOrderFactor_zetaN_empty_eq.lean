-- Prove2me | solution 1 for FixedOrderFactor.zetaN_empty_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:52:19.599733+00:00
-- url     : https://prove2.me/submissions/e7c90dc5-046a-409c-9570-341a27352608

module
public import Definitions.Def_FixedOrderFactor_Order
public import Definitions.Def_FixedOrderFactor_Values

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {s : ℕ} (hs : s ≠ 0) : zetaN ∅ s = ∑' n : ℕ, 1 / (n : ℝ) ^ s := by
  unfold zetaN
  congr 1; funext n
  have hP : PrimeTo ∅ n := fun q hq => absurd hq (Finset.notMem_empty q)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hs]
  · simp [hn, hP]
end FixedOrderFactor
