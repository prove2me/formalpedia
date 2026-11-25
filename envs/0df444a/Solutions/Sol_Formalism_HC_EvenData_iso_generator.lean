-- Prove2me | solution 1 for Formalism.HC.EvenData.iso_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:59:42.038258+00:00
-- url     : https://prove2.me/submissions/73716f77-c27d-4624-87ac-6f434d14a18c

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
theorem _root_.solution : D.iso (D.frame.iota D.frame.a0) = D.gen := by
  show Additive.toMul (D.isoA D.frame.a0) = D.gen
  rw [isoA_a0_eq_ofMul_gen]
  rfl
end Formalism.HC.EvenData
