-- Prove2me | solution 1 for Formalism.HC.EvenData.mem_cusp_forms_iff_automorphic_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:34:11.206583+00:00
-- url     : https://prove2.me/submissions/630ec122-c358-4987-8f4c-092b7d7f2971

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfChar
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.HC
open Formalism.FrobeniusOrbits
attribute [instance] EvenData.grp
namespace EvenData
variable (D : EvenData)
private theorem isoA_a0_eq_ofMul_gen : D.isoA D.frame.a0 = Additive.ofMul D.gen := by
  show (Fintype.equivFin (Additive D.R)).symm
    ((Fintype.equivFin (Additive D.R)).symm.symm (Additive.ofMul D.gen)) = _
  exact Equiv.apply_symm_apply _ _
section Host
variable {q d : ℕ} (hH : HostHyp q d)
variable (hc : Nat.Coprime D.m (q * d))
variable (he : 2 ≤ D.e) (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ D.m → jacobiSym (-(d : ℤ)) l = 1)
end Host
end EvenData
end Formalism.HC
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
attribute [instance] EvenData.grp
open Formalism.HC.EvenData
variable (D : EvenData)
namespace Formalism.HC.EvenData
theorem _root_.solution (t : D.frame.A) : t ∈ D.frame.A0 ↔ D.xiA (D.frame.iota t) = 1 := by
  show t ∈ AddSubgroup.zmultiples D.frame.a0 ↔ D.p2 (Additive.toMul (D.isoA t)) = 1
  rw [D.gen_spec, AddSubgroup.mem_zmultiples_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [map_zsmul, isoA_a0_eq_ofMul_gen, toMul_zsmul, toMul_ofMul]⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, D.isoA.injective ?_⟩
    rw [map_zsmul, isoA_a0_eq_ofMul_gen, ← ofMul_zpow, hk, ofMul_toMul]
end Formalism.HC.EvenData
