-- Prove2me | solution 1 for Formalism.HC.PChar.of_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:56.861526+00:00
-- url     : https://prove2.me/submissions/8790c130-1b26-4ad5-b860-c28c0f64e54a

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Analytic
import Definitions.Def_Formalism_StatementOC
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
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
namespace Level
variable (Λ : Level)
end Level
private theorem pchar_mk_eq_of_changeLevel_eq_self_of_primitive {N d : ℕ} [NeZero N] [NeZero d] (χ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ d) (hd : d ∣ N) (hc : DirichletCharacter.changeLevel hd ψ = χ)
    (h1 : ψ.IsPrimitive) (h2 : χ.IsPrimitive) (he : d = N) :
    PChar.mk d ψ h1 = PChar.mk N χ h2 := by
  subst he
  rw [DirichletCharacter.changeLevel_self] at hc
  subst hc
  rfl
namespace Frame
variable (φ : Frame)
end Frame
end Formalism.HC
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
namespace Formalism.HC
namespace PChar
theorem _root_.solution (ψ : PChar) : PChar.of ψ.χ = ψ := by
  haveI : NeZero ψ.χ.conductor := ⟨ψ.χ.conductor_ne_zero⟩
  exact pchar_mk_eq_of_changeLevel_eq_self_of_primitive ψ.χ ψ.χ.primitiveCharacter ψ.χ.conductor_dvd_level
    ψ.χ.changeLevel_primitiveCharacter ψ.χ.primitiveCharacter_isPrimitive ψ.prim ψ.prim
end PChar
end Formalism.HC
