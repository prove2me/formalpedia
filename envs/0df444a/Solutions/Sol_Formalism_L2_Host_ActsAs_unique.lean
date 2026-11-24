-- Prove2me | solution 1 for Formalism.L2.Host.ActsAs.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:58:14.192417+00:00
-- url     : https://prove2.me/submissions/8ccb402f-b84b-48c1-9c30-cc393bf622e8

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_Lemmas
import Theorems.Thm_Formalism_L2_Host_EQ_eq_adjoin
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
theorem _root_.solution {e q d : ℕ} {s s' : EQ e q d →ₐ[ℚ] Qb} {g : GG e}
    (h : ActsAs e q d s g) (h' : ActsAs e q d s' g) : s = s' := by
  obtain ⟨h1, h2, u, hu, hs⟩ := h
  obtain ⟨h1', h2', u', hu', hs'⟩ := h'
  refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (EQ_eq_adjoin e q d) ?_
  intro x hx
  rcases hx with (hx | hx) | ⟨z, hz, hzx⟩
  · exact (h1 _ hx).trans (h1' _ hx).symm
  · exact (h2 _ hx).trans (h2' _ hx).symm
  · have hz1 : z ^ (2 ^ (e + 2)) = 1 := hz
    have hz' : z⁻¹ ^ (2 ^ (e + 2)) = 1 := by rw [inv_pow, hz1, inv_one]
    have hval : z ^ (u : ZMod (2 ^ (e + 2))).val + z⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val =
        z ^ (u' : ZMod (2 ^ (e + 2))).val + z⁻¹ ^ (u' : ZMod (2 ^ (e + 2))).val := by
      have hq : (hcl e u : HGrp e) = hcl e u' := hu.trans hu'.symm
      rw [hcl, hcl, QuotientGroup.eq, Subgroup.mem_zpowers_iff] at hq
      obtain ⟨k, hk⟩ := hq
      rcases Int.even_or_odd k with he | ho
      · rw [he.neg_one_zpow, eq_comm, inv_mul_eq_one] at hk
        rw [hk]
      · rw [ho.neg_one_zpow, eq_comm, inv_mul_eq_iff_eq_mul, mul_neg_one] at hk
        rw [hk, Units.val_neg, pow_neg_val hz1, pow_neg_val hz', inv_inv, add_comm]
    exact ((hs _ z hz hzx.symm).trans hval).trans (hs' _ z hz hzx.symm).symm
end ActsAs
end Formalism.L2.Host
