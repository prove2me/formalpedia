-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.cosetMean_eq_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:21:57.197971+00:00
-- url     : https://prove2.me/submissions/7291ad8d-c529-4675-a96d-f010cabceb9c

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_cast_eq_natCast_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_frobUnit_modEq
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_dirChar_unit
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_trivial_on_inertia_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_inertia_conductor
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_cosetMean_of_trivial
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_cosetMean_of_nontrivial

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
    (ψ : AddChar (E0 × H) ℂ) (p i : ℕ) (hp : p.Prime) (hi : i ≠ 0) :
    cosetMean ((cftData q1 d r).inertia p) (i • (cftData q1 d r).frob p) ψ
      = (dirChar r ψ).primitiveCharacter (p : ZMod (dirChar r ψ).conductor) ^ i := by
  by_cases h : ∀ x ∈ (cftData q1 d r).inertia p, ψ x = 1
  · rw [cosetMean_of_trivial _ _ _ h, AddChar.map_nsmul_eq_pow]
    congr 1
    have hc : (dirChar r ψ).conductor ∣ ordCompl[p] N := (trivial_on_inertia_iff q1 d r ψ p).1 h
    change ψ (Multiplicative.toAdd (r (frobUnit N p))) = _
    rw [← dirChar_unit]
    conv_lhs => rw [← DirichletCharacter.changeLevel_primitiveCharacter (dirChar r ψ)]
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
    congr 1
    rw [cast_eq_natCast_iff]
    exact (frobUnit_modEq hp).1.of_dvd hc
  · rw [cosetMean_of_nontrivial _ _ _ h]
    have hpc : p ∣ (dirChar r ψ).conductor := by
      by_contra hpc
      exact h ((inertia_conductor N q1 d r ψ p (NeZero.ne N) hp).2 hpc)
    rw [MulChar.map_nonunit, zero_pow hi]
    rw [ZMod.isUnit_iff_coprime]
    intro hcop
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hpc)
end Formalism.LFunctionChainParameters.LHost
