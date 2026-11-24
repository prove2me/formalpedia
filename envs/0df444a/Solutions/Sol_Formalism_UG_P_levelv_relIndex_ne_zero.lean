-- Prove2me | solution 1 for Formalism.UG.P.levelv_relIndex_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:38:58.815573+00:00
-- url     : https://prove2.me/submissions/59f0320b-d458-4aa5-8731-b384c95218a1

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution {G : Type*} [Group G] (H K : Subgroup G) {β : Type*} [Finite β]
    (f : G → β) (hf : ∀ a ∈ K, ∀ b ∈ K, f a = f b → a⁻¹ * b ∈ H) : H.relIndex K ≠ 0 := by
  classical
  have hfin : Finite (K ⧸ H.subgroupOf K) := by
    refine Finite.of_surjective
      (fun y : Set.range (fun k : K => f k) =>
        (QuotientGroup.mk (Set.mem_range.mp y.2).choose : K ⧸ H.subgroupOf K)) ?_
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨⟨f k, k, rfl⟩, ?_⟩
    beta_reduce
    have hc := (Set.mem_range.mp (⟨k, rfl⟩ : f k ∈ Set.range (fun k : K => f k))).choose_spec
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hf _ (Set.mem_range.mp (⟨k, rfl⟩ : f k ∈ Set.range (fun k : K => f k))).choose.2 _ k.2 hc
  show (H.subgroupOf K).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite
end Formalism.UG.P
