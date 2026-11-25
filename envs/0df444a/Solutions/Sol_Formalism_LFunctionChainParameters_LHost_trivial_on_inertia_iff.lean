-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.trivial_on_inertia_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:46:19.23664+00:00
-- url     : https://prove2.me/submissions/a3dba75d-eb5a-4a26-a1b0-0114817a8cb2

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_dirChar_unit
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_mem_inertia_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LHost
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.LHost
theorem _root_.solution {N : ℕ} [NeZero N] (q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H))
    (ψ : AddChar (E0 × H) ℂ) (p : ℕ) :
    (∀ x ∈ (cftData q1 d r).inertia p, ψ x = 1) ↔ (dirChar r ψ).conductor ∣ ordCompl[p] N := by
  rw [← DirichletCharacter.mem_conductorSet_iff_conductor_dvd _ (Nat.ordCompl_dvd N p),
    DirichletCharacter.mem_conductorSet_iff,
    DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.ordCompl_dvd N p)]
  constructor
  · intro h u hu
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, dirChar_unit, Units.val_one]
    exact h _ ((mem_inertia_iff q1 d r p _).2 ⟨u, hu, rfl⟩)
  · intro h x hx
    obtain ⟨u, hu, rfl⟩ := (mem_inertia_iff q1 d r p _).1 hx
    have := h hu
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, dirChar_unit, Units.val_one] at this
    exact this
end Formalism.LFunctionChainParameters.LHost
