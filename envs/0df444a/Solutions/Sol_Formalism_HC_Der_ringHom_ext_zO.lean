-- Prove2me | solution 1 for Formalism.HC.Der.ringHom_ext_zO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:31:27.841782+00:00
-- url     : https://prove2.me/submissions/f8ae5a82-99ff-4df7-8bab-a31767d0cc4e

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_z_spec
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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



set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable (N : ℕ) [NeZero N]
namespace Formalism.HC.Der
theorem _root_.solution {R : Type*} [CommRing R] (f g : 𝓞 (Cond.Cyc N) →+* R) (h : f (zO N) = g (zO N))
    (x : 𝓞 (Cond.Cyc N)) : f x = g x := by
  have hx : x ∈ Algebra.adjoin ℤ {zO N} := by
    rw [show Algebra.adjoin ℤ {zO N} = ⊤ from IsCyclotomicExtension.Rat.adjoin_singleton_eq_top (Cond.z_spec N)]
    exact Algebra.mem_top
  refine Algebra.adjoin_induction (p := fun x _ => f x = g x) (fun y hy => ?_) (fun r => ?_)
    (fun y z _ _ h1 h2 => ?_) (fun y z _ _ h1 h2 => ?_) hx
  · rw [Set.mem_singleton_iff.1 hy]
    exact h
  · simp only [algebraMap_int_eq, eq_intCast, map_intCast]
  · rw [map_add, map_add, h1, h2]
  · rw [map_mul, map_mul, h1, h2]
end Formalism.HC.Der
