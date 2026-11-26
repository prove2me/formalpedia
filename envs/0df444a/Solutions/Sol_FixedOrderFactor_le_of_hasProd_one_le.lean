-- Prove2me | solution 1 for FixedOrderFactor.le_of_hasProd_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:22.105706+00:00
-- url     : https://prove2.me/submissions/fd01697f-4069-4799-bf75-0ecacb1f9b3b

module
public import Definitions.Def_FixedOrderFactor_Model
public import Definitions.Def_FixedOrderFactor_Order

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {ι : Type*} [DecidableEq ι] {f : ι → ℝ} {a : ℝ} (h : HasProd f a)
    (hf : ∀ i, 1 ≤ f i) (i₀ : ι) : f i₀ ≤ a := by
  refine ge_of_tendsto h ?_
  filter_upwards [eventually_ge_atTop {i₀}] with s hs
  have hi : i₀ ∈ s := hs (mem_singleton_self i₀)
  rw [← Finset.mul_prod_erase s f hi]
  have h1 : 1 ≤ ∏ i ∈ s.erase i₀, f i := one_le_prod (fun i _ => hf i)
  nlinarith [hf i₀]
end FixedOrderFactor
