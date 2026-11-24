-- Prove2me | solution 1 for Formalism.HC.EvenData.o_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:08:06.083708+00:00
-- url     : https://prove2.me/submissions/da609464-7b69-4430-9c70-88d0f914a951

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfChar
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
import Theorems.Thm_Formalism_HC_EvenData_ord_eq
import Theorems.Thm_Formalism_HC_EvenData_range_xiA
import Theorems.Thm_Formalism_HC_D7_ord_eq

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
theorem _root_.solution : D.frame.o = Nat.card D.ξ.range := by
  have hz : Subgroup.zpowers D.gen = D.p2.ker :=
    Subgroup.ext fun x => (D.gen_spec x).symm.trans MonoidHom.mem_ker.symm
  have hn0 : D.frame.n0 = Nat.card D.p2.ker := by
    show addOrderOf D.frame.a0 = _
    rw [← addOrderOf_injective D.isoA.toAddMonoidHom D.isoA.injective D.frame.a0]
    show addOrderOf (D.isoA D.frame.a0) = _
    rw [isoA_a0_eq_ofMul_gen, addOrderOf_ofMul_eq_orderOf, ← Nat.card_zpowers, hz]
  have hr : D.p2.range = D.ξ.range := by
    rw [← D.range_xiA]
    show _ = (D.p2.comp D.iso.toMonoidHom).range
    have htop : D.iso.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr D.iso.surjective
    rw [MonoidHom.range_comp, htop, ← MonoidHom.range_eq_map]
  have hc : Nat.card D.R = Nat.card D.p2.range * Nat.card D.p2.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup D.p2.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange D.p2).toEquiv]
  have hpos : 0 < Nat.card D.p2.ker := Nat.card_pos
  show D.frame.ord / D.frame.n0 = _
  rw [D.ord_eq, hn0, hc, Nat.mul_div_cancel _ hpos, hr]
end Formalism.HC.EvenData
