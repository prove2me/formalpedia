-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5a4_prime_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:34.500804+00:00
-- url     : https://prove2.me/submissions/34214efe-0141-40e4-a779-acc758cb743a

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {K : Type} [Field K] [NumberField K] (Q : Ideal (𝓞 K)) (hQ : Q.IsPrime)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpQ : (p : 𝓞 K) ∈ Q) (hqQ : (q : 𝓞 K) ∈ Q) : p = q := by
  by_contra hne
  have hco : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr hco
  obtain ⟨u, v, huv⟩ := hc
  have h1 : (1 : 𝓞 K) ∈ Q := by
    have e : (1 : 𝓞 K) = (u : 𝓞 K) * (p : 𝓞 K) + (v : 𝓞 K) * (q : 𝓞 K) := by
      have := congrArg (Int.cast : ℤ → 𝓞 K) huv
      push_cast at this ⊢; exact this.symm
    rw [e]; exact Q.add_mem (Q.mul_mem_left _ hpQ) (Q.mul_mem_left _ hqQ)
  exact hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr h1)
end Formalism.HermitianLatticeCounting.P
