-- Prove2me | solution 1 for Formalism.HC.Der.exists_prime_liesOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:51:55.952014+00:00
-- url     : https://prove2.me/submissions/db12d126-f569-41a8-99f9-d249dd94b81a

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.HC.Der
theorem _root_.solution {M : Type} [Field M] [NumberField M] (P : Ideal (𝓞 M)) [hP : P.IsPrime] (h0 : P ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ P.LiesOver (span {(p : ℤ)}) := by
  have hne : Ideal.comap (algebraMap ℤ (𝓞 M)) P ≠ ⊥ := by
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)
  obtain ⟨g, hg⟩ : ∃ g : ℤ, Ideal.comap (algebraMap ℤ (𝓞 M)) P = Ideal.span {g} :=
    (Submodule.IsPrincipal.principal (Ideal.comap (algebraMap ℤ (𝓞 M)) P))
  have hg0 : g ≠ 0 := by
    rintro rfl
    apply hne
    rw [hg, Ideal.span_singleton_eq_bot]
  have hpr : (Ideal.span {g}).IsPrime := by rw [← hg]; infer_instance
  have hgp : Prime g := (Ideal.span_singleton_prime hg0).mp hpr
  refine ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hgp, ⟨?_⟩⟩
  rw [Int.span_natAbs]
  exact hg.symm
end Formalism.HC.Der
