-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.liesOver_span_of_natCast_mem_frobenius_orbits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:43:34.181859+00:00
-- url     : https://prove2.me/submissions/87178636-e7f8-49e2-85c9-a614aa4554ed

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply



set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Principal
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace Formalism.FrobeniusOrbits
theorem _root_.solution {M : Type} [Field M] [NumberField M] (P : Ideal (𝓞 M)) [P.IsPrime]
    (p : ℕ) (hp : p.Prime) (hm : ((p : ℤ) : 𝓞 M) ∈ P) : P.LiesOver (span {(p : ℤ)}) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hle : span {(p : ℤ)} ≤ P.under ℤ := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_comap.mpr (by simpa using hm)
  exact ⟨(Int.ideal_span_isMaximal_of_prime p).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle⟩
end Formalism.FrobeniusOrbits
