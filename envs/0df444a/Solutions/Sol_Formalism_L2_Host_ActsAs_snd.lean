-- Prove2me | solution 1 for Formalism.L2.Host.ActsAs.snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:01:13.203847+00:00
-- url     : https://prove2.me/submissions/baefa6be-8d45-4c2f-b665-2c519c4c2932

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_Lemmas
import Theorems.Thm_Formalism_L2_Host_pow_neg_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IntermediateField NumberField
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.L2.Host
namespace ActsAs
theorem _root_.solution {e q d : ℕ} {s : EQ e q d →ₐ[ℚ] Qb} {g : GG e} (h : ActsAs e q d s g)
    (u' : (ZMod (2 ^ (e + 2)))ˣ) (hu' : hcl e u' = g.2) (x : EQ e q d) (z : Qb) (hz : z ∈ mus (2 ^ (e + 2)))
    (hx : (x : Qb) = z + z⁻¹) :
    s x = z ^ (u' : ZMod (2 ^ (e + 2))).val + z⁻¹ ^ (u' : ZMod (2 ^ (e + 2))).val := by
  obtain ⟨-, -, u, hu, hs⟩ := h
  rw [hs x z hz hx]
  have hq : (hcl e u : HGrp e) = hcl e u' := hu.trans hu'.symm
  rw [hcl, hcl, QuotientGroup.eq, Subgroup.mem_zpowers_iff] at hq
  obtain ⟨k, hk⟩ := hq
  have hz1 : z ^ (2 ^ (e + 2)) = 1 := hz
  have hz' : z⁻¹ ^ (2 ^ (e + 2)) = 1 := by rw [inv_pow, hz1, inv_one]
  rcases Int.even_or_odd k with he | ho
  · rw [he.neg_one_zpow, eq_comm, inv_mul_eq_one] at hk
    rw [hk]
  · rw [ho.neg_one_zpow, eq_comm, inv_mul_eq_iff_eq_mul, mul_neg_one] at hk
    rw [hk, Units.val_neg, pow_neg_val hz1, pow_neg_val hz', inv_inv, add_comm]
end ActsAs
end Formalism.L2.Host
