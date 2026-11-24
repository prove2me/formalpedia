-- Prove2me | solution 1 for Formalism.HC.HostRaw.artin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:03:21.228859+00:00
-- url     : https://prove2.me/submissions/a5aa0004-b6db-4e8a-b43a-c279272e13dd

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_AdjoinCycZeta
import Theorems.Thm_Formalism_HC_HostRaw_actsAs_of_one
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_aut


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
open Formalism Formalism.HC Formalism.HC.HostRaw
open Formalism.FrobeniusOrbits Formalism.L2.Host
variable {φ : Frame} (H : HostRaw φ)
variable {H}
variable (H)
namespace Formalism.HC.HostRaw
theorem _root_.solution (s : Qb ≃ₐ[ℚ] Qb) (u : (ZMod H.condN)ˣ) (hs : ∀ z ∈ mus H.condN, s z = z ^ (u : ZMod H.condN).val) :
    H.ActsAs (restr H.EQ s) (H.art u) := by
  let κ : Cond.Cyc H.condN →ₐ[ℚ] Qb := IsAlgClosed.lift
  obtain ⟨τ, hτ⟩ := Cond.aut H.condN (u : ZMod H.condN).val (ZMod.val_coe_unit_coprime u)
  have hτz := hτ H.cycZeta H.cycZeta_prim.pow_eq_one
  have hcomm : (s : Qb →ₐ[ℚ] Qb).comp κ = κ.comp (τ : Cond.Cyc H.condN →ₐ[ℚ] Cond.Cyc H.condN) := by
    refine AlgHom.ext_of_adjoin_eq_top (s := {H.cycZeta})
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top H.cycZeta_prim) ?_
    rintro _ rfl
    show s (κ H.cycZeta) = κ (τ H.cycZeta)
    rw [hτz, map_pow]
    refine hs _ ?_
    show κ H.cycZeta ^ H.condN = 1
    rw [← map_pow, H.cycZeta_prim.pow_eq_one, map_one]
  refine actsAs_of_one (κ.comp H.cycEmb) fun x => ?_
  show s (κ (H.cycEmb x)) = κ (H.cycEmb (H.gal.symm (H.art u) x))
  rw [H.art_spec u τ hτz x]
  exact DFunLike.congr_fun hcomm (H.cycEmb x)
end Formalism.HC.HostRaw
