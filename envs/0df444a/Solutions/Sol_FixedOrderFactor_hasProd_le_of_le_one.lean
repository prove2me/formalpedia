-- Prove2me | solution 1 for FixedOrderFactor.hasProd_le_of_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:22.84092+00:00
-- url     : https://prove2.me/submissions/dfe3e0e7-dfe6-435a-89de-0342e0241158

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
    (hf0 : ∀ i, 0 ≤ f i) (hf : ∀ i, f i ≤ 1) (i₀ : ι) : a ≤ f i₀ := by
  refine le_of_tendsto h ?_
  filter_upwards [eventually_ge_atTop {i₀}] with s hs
  have hi : i₀ ∈ s := hs (mem_singleton_self i₀)
  rw [← Finset.mul_prod_erase s f hi]
  have h1 : ∏ i ∈ s.erase i₀, f i ≤ 1 := prod_le_one (fun i _ => hf0 i) (fun i _ => hf i)
  have h0 : 0 ≤ ∏ i ∈ s.erase i₀, f i := prod_nonneg (fun i _ => hf0 i)
  nlinarith [hf0 i₀]
end FixedOrderFactor
