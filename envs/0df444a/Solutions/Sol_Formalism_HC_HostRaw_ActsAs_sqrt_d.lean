-- Prove2me | solution 1 for Formalism.HC.HostRaw.ActsAs.sqrt_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:45:01.884158+00:00
-- url     : https://prove2.me/submissions/ab37683a-a1f9-4a1e-8176-f9f69f05e3c9

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_AdjoinCycZeta
import Theorems.Thm_Formalism_HC_HostRaw_jOf_coe
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_L2_Host_jOf_coe
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.L2.Host.jOf_coe
attribute [local simp] Formalism.L2.Host.restr_apply


attribute [local simp] Formalism.HC.HostRaw.jOf_coe

set_option autoImplicit false
noncomputable section
open IntermediateField NumberField
open Formalism Formalism.HC Formalism.HC.HostRaw
open Formalism.FrobeniusOrbits Formalism.L2.Host
variable {φ : Frame} (H : HostRaw φ)
variable {H}
namespace Formalism.HC.HostRaw
namespace ActsAs
theorem _root_.solution {s : H.EQ →ₐ[ℚ] Qb} {g : φ.GG} (h : H.ActsAs s g) (x : H.EQ) (hx : (x : Qb) ∈ sqrts (-(H.d : ℤ))) :
    s x = (((g.1.2 : ℤˣ) : ℤ) : Qb) * x := by
  obtain ⟨j⟩ := H.nonempty_emb
  obtain ⟨y, rfl⟩ := (H.jOf j).surjective x
  have hy : y ^ 2 = H.sqd ^ 2 := by
    apply j.toRingHom.injective
    show j (y ^ 2) = j (H.sqd ^ 2)
    rw [H.sqd_sq, map_pow, show j y ^ 2 = ((-(H.d : ℤ) : ℤ) : Qb) from hx]; simp
  have h1 := H.gal_sqd (H.gal.symm g)
  rw [MulEquiv.apply_symm_apply] at h1
  refine (h j y).trans ?_
  rw [jOf_coe]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with rfl | rfl
  · rw [h1, map_mul, map_intCast]
  · rw [map_neg, h1, map_neg, map_neg, map_mul, map_intCast, mul_neg]
end ActsAs
end Formalism.HC.HostRaw
