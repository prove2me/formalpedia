-- Prove2me | solution 1 for Formalism.DivisionValues.DivisorInequalityBounds.goodFull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:56.650113+00:00
-- url     : https://prove2.me/submissions/4004dd32-6be9-41d2-ae84-b93700ff1312

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ScalarLiftLowerBoundFull
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_WeightedPlaceLogSum
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_GlobalBoundRefinements
import Theorems.Thm_Formalism_DivisionValues_WeightedPlaceLogSum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.DivisorInequalityBounds
namespace Formalism.DivisionValues.DivisorInequalityBounds
theorem _root_.solution {K Ω : Type} [Field K] [Field Ω] {n : ℕ} (j : K →+* Ω)
    (𝒯 : Set (Matrix (Fin n) (Fin n) K)) (e : Matrix (Fin n) (Fin n) K)
    (Z : Submodule K (Fin n → K)) (S : Set (Matrix (Fin n) (Fin n) K → Ω))
    (hZ : extSpan j Z = ⨆ χ ∈ S, (simEig j 𝒯 χ ⊓ simEig j {e} (fun _ => 1))) :
    IsFullEigSum j (𝒯 ∪ {e}) Z := by
  classical
  refine ⟨{χ' | χ' e = 1 ∧ ∃ χ ∈ S, ∀ T ∈ 𝒯, χ' T = χ T}, ?_⟩
  rw [hZ]
  apply le_antisymm
  · refine iSup₂_le fun χ hχ => ?_
    by_cases h : e ∈ 𝒯 ∧ χ e ≠ 1
    · rintro x ⟨hx, hx1⟩
      have h1 := hx e h.1
      rw [hx1 e rfl, one_smul] at h1
      have h2 : (1 - χ e) • x = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
      rcases smul_eq_zero.mp h2 with h3 | h3
      · exact absurd (sub_eq_zero.mp h3).symm h.2
      · rw [h3]; exact Submodule.zero_mem _
    · have hupd : ∀ T ∈ 𝒯, Function.update χ e 1 T = χ T := by
        intro T hT
        by_cases hTe : T = e
        · subst hTe
          rw [Function.update_self]
          by_contra hne
          exact h ⟨hT, fun h' => hne h'.symm⟩
        · rw [Function.update_of_ne hTe]
      have hmem : Function.update χ e 1 ∈ {χ' : Matrix (Fin n) (Fin n) K → Ω |
          χ' e = 1 ∧ ∃ χ ∈ S, ∀ T ∈ 𝒯, χ' T = χ T} :=
        ⟨Function.update_self _ _ _, χ, hχ, hupd⟩
      refine le_trans ?_ (le_iSup₂ (f := fun χ' _ => simEig j (𝒯 ∪ {e}) χ') _ hmem)
      rintro x ⟨hx, hx1⟩ T hT
      rcases hT with hT | hT
      · rw [hupd T hT]
        exact hx T hT
      · rw [Set.mem_singleton_iff.mp hT, Function.update_self]
        exact hx1 e rfl
  · refine iSup₂_le fun χ' hχ' => ?_
    obtain ⟨h1, χ, hχ, h2⟩ := hχ'
    refine le_trans ?_ (le_iSup₂ (f := fun χ _ => simEig j 𝒯 χ ⊓ simEig j {e} (fun _ => 1)) χ hχ)
    intro x hx
    refine ⟨fun T hT => ?_, fun T hT => ?_⟩
    · rw [← h2 T hT]; exact hx T (Or.inl hT)
    · rw [Set.mem_singleton_iff.mp hT, ← h1]; exact hx e (Or.inr rfl)
end Formalism.DivisionValues.DivisorInequalityBounds
