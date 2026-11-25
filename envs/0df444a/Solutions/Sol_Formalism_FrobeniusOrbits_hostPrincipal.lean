-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostPrincipal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:25:02.139718+00:00
-- url     : https://prove2.me/submissions/905556c6-b8f2-4ef7-8346-59296fd13e71

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal
import Theorems.Thm_Formalism_FrobeniusOrbits_hostDiffSupport
import Theorems.Thm_Formalism_FrobeniusOrbits_Principal_diff_smul_eq
import Theorems.Thm_Formalism_FrobeniusOrbits_Principal_pairing
import Theorems.Thm_Formalism_FrobeniusOrbits_liesOver_span_of_natCast_mem_frobenius_orbits
import Theorems.Thm_Formalism_FrobeniusOrbits_HostHyp_toHypOdd
import Theorems.Thm_Formalism_FrobeniusOrbits_galE_injective
import Theorems.Thm_Formalism_FrobeniusOrbits_galE_one
import Theorems.Thm_Formalism_FrobeniusOrbits_hostDecompConj
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_HypQD_toHypOdd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Principal
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostPrincipal := by
  intro e q d hH L _ _ ζ a b h σ hσ
  have hqd := hH.toHypOdd
  let f := MulSemiringAction.toRingEquiv (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
    (Ideal (𝓞 (hostE ζ a b))) σ
  have hf : ∀ I, f I = σ • I := fun I => rfl
  have hσσ : σ * σ = 1 := by
    apply galE_injective (e := e) hqd h
    rw [galE_mul hqd h, hσ, galE_one hqd h]
    exact Prod.ext (show c0 * c0 = (1 : G0) by decide) (mul_one _)
  have hD0 : differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) ≠ ⊥ := by
    have := differentIdeal_ne_bot (A := 𝓞 (KinE ζ a b)) (B := 𝓞 (hostE ζ a b))
    exact this
  obtain ⟨B, hB1, hB2⟩ := Principal.pairing _ hD0 f.toMulEquiv
    (by show f _ = _; rw [hf]; exact Principal.diff_smul_eq hqd h σ)
    (fun I => by show f (f I) = I; rw [hf, hf, smul_smul, hσσ, one_smul])
    (by
      intro P hP
      show f P ≠ P
      rw [hf]
      rw [Ideal.mem_normalizedFactors_iff hD0] at hP
      obtain ⟨hPp, hle⟩ := hP
      have hdvd : P ∣ differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) := Ideal.dvd_iff_le.mpr hle
      intro hfix
      have hst : σ ∈ MulAction.stabilizer _ P := hfix
      rcases hostDiffSupport e q d hH L ζ a b h P hPp hdvd with h2 | hq
      · have : P.LiesOver (span {((2 : ℕ) : ℤ)}) :=
          liesOver_span_of_natCast_mem_frobenius_orbits P 2 Nat.prime_two (by exact_mod_cast h2)
        exact hostDecompConj e q d hH L ζ a b h σ hσ 2 (Or.inl rfl) P hst
      · have : P.LiesOver (span {(q : ℤ)}) := liesOver_span_of_natCast_mem_frobenius_orbits P q hH.1 hq
        exact hostDecompConj e q d hH L ζ a b h σ hσ q (Or.inr (Or.inl rfl)) P hst)
  exact ⟨B, hB1, hB2⟩
end Formalism.FrobeniusOrbits
