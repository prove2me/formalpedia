-- Prove2me | solution 1 for Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.principalStable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:01:41.384157+00:00
-- url     : https://prove2.me/submissions/405cc21f-1f75-49f8-b96e-2b15cf639704

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_idealConjugateFactorizationUnique
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_cm_smul
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_int_mem_smul
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_key
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_excl
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_HostHyp_toHypOdd
import Theorems.Thm_Formalism_FrobeniusOrbits_Principal_diff_smul_eq
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_FrobeniusOrbits_hostDiffSupport
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_HypQD_toHypOdd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.FiltrationBoundaryCriterion
open Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
open NumberField IntermediateField Ideal
open scoped Pointwise
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
theorem _root_.solution : PrincipalStable := by
  intro e q d hH L _ _ ζ a b h c hc 𝔭₂ 𝔭q h𝔭₂ h𝔭q h2 hq
  have hqd := hH.toHypOdd
  have hD0 : differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) ≠ ⊥ := by
    have := differentIdeal_ne_bot (A := 𝓞 (KinE ζ a b)) (B := 𝓞 (hostE ζ a b))
    exact this
  let f : (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) → (Ideal (𝓞 (hostE ζ a b)) ≃* Ideal (𝓞 (hostE ζ a b))) :=
    fun σ => (MulSemiringAction.toRingEquiv (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
      (Ideal (𝓞 (hostE ζ a b))) σ).toMulEquiv
  have hf : ∀ σ I, f σ I = σ • I := fun σ I => rfl
  have hcop : Nat.Coprime 2 q := by
    rw [Nat.coprime_two_left, Nat.odd_iff]
    have := hH.2.2.1; omega
  obtain ⟨B, hB1, hB2, hB3, hB4, hB5⟩ := idealConjugateFactorizationUnique _ hD0 (f c)
    (by rw [hf]; exact Principal.diff_smul_eq hqd h c)
    (fun P => cm P = 𝔭₂ ∨ cm P = 𝔭q)
    (by
      intro P hP
      rw [hf]
      rw [Ideal.mem_normalizedFactors_iff hD0] at hP
      obtain ⟨hPp, hle⟩ := hP
      have hdvd : P ∣ differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) := Ideal.dvd_iff_le.mpr hle
      rcases hostDiffSupport e q d hH L ζ a b h P hPp hdvd with hm | hm
      · have hm' : (((2 : ℕ) : ℤ) : 𝓞 (hostE ζ a b)) ∈ P := by exact_mod_cast hm
        have h2' : (((2 : ℕ) : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭₂ := by exact_mod_cast h2
        rw [or_iff_left (excl 2 q hcop 𝔭q hq (c • P) (int_mem_smul c _ P hm')),
          or_iff_left (excl 2 q hcop 𝔭q hq P hm')]
        exact key hH h c hc 2 (Or.inl rfl) 𝔭₂ h2' P hm'
      · have h2' : (((2 : ℕ) : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭₂ := by exact_mod_cast h2
        rw [or_iff_right (excl q 2 hcop.symm 𝔭₂ h2' (c • P) (int_mem_smul c _ P hm)),
          or_iff_right (excl q 2 hcop.symm 𝔭₂ h2' P hm)]
        exact key hH h c hc q (Or.inr rfl) 𝔭q hq P hm)
  refine ⟨B, hB1, hB2, hB3, ?_, hB5⟩
  intro σ hσ
  refine hB4 (f σ) (by rw [hf]; exact Principal.diff_smul_eq hqd h σ) ?_
  intro P _
  rw [hf, cm_smul hqd h σ hσ]
end Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN
