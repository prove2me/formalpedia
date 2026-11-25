-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.exists_place3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:27:25.880826+00:00
-- url     : https://prove2.me/submissions/02da0590-b092-4c8a-90ed-15c7535d2661

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsWeightedConditional
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditions
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ErrSum
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_UnipotentNumeric
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditionsOfExact
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField IsDedekindDomain
noncomputable section
namespace Formalism.L2.Indef.Tree
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace OnConst
end OnConst
namespace OnObj
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst} (O : OnObj S P c)
end OnObj
section Leaves
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}
end Leaves
section Proof
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}
end Proof
section Examples₂
variable (K)
private theorem exists_place_lemma (p : ℕ) (hp : p.Prime) : ∃ w : HeightOneSpectrum (𝓞 K), plc w = p := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have hker : RingHom.ker (algebraMap ℤ (𝓞 K)) ≤ Ideal.span {(p : ℤ)} := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hx0 : x = 0 := (algebraMap ℤ (𝓞 K)).injective_int (by rw [hx, map_zero])
    rw [hx0]
    exact Ideal.zero_mem _
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (Ideal.span {(p : ℤ)}) hker
  have hpQ : ((p : ℕ) : 𝓞 K) ∈ Q := by
    have h1 : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      rw [hQ]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap] at h1
    simpa using h1
  have hQne : Q ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpQ
    exact hp.ne_zero (by exact_mod_cast hpQ)
  refine ⟨⟨Q, hQmax.isPrime, hQne⟩, ?_⟩
  haveI : Nontrivial (𝓞 K ⧸ Q) := by
    first
    | exact Ideal.Quotient.nontrivial_iff.mpr hQmax.ne_top
    | exact Ideal.Quotient.nontrivial hQmax.ne_top
    | exact (Ideal.Quotient.field Q).toNontrivial
  haveI : CharP (𝓞 K ⧸ Q) p := by
    rw [CharP.charP_iff_prime_eq_zero hp]
    have h2 := (Ideal.Quotient.eq_zero_iff_mem).mpr hpQ
    simpa using h2
  exact ringChar.eq (𝓞 K ⧸ Q) p
variable {K} (v0 : InfinitePlace K) (Tw0 : Finset (HeightOneSpectrum (𝓞 K)))
variable (h3 : ∀ w ∈ Tw0, plc w = 3)
include h3
omit h3
section Level
variable (h5 : ∀ w ∈ Tw0, plc w = 5)
include h5
end Level
end Examples₂
end Formalism.L2.Indef.Tree
end
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (K)
namespace Formalism.L2.Indef.Tree
theorem _root_.solution : ∃ w : HeightOneSpectrum (𝓞 K), plc w = 3 := by
  exact exists_place_lemma K 3 Nat.prime_three
end Formalism.L2.Indef.Tree
