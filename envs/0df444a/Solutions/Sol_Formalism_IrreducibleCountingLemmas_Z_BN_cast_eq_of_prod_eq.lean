-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.BN.cast_eq_of_prod_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:52:46.968345+00:00
-- url     : https://prove2.me/submissions/ca4b3bef-df6b-439e-8e86-76fcd4fa47d5

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z Formalism.IrreducibleCountingLemmas.Z.BN
namespace Formalism.IrreducibleCountingLemmas.Z.BN
theorem _root_.solution {K Γ ι : Type} [Field K] (t : Finset ι) (f : ι → Γ → K[X])
    (hm : ∀ i ∈ t, ∀ g, (f i g).Monic)
    (hli : ∀ c : ι → K, (∀ g, ∑ i ∈ t, c i * (f i g).nextCoeff = 0) → ∀ i ∈ t, c i = 0)
    (a b : ι → ℕ) (h : ∀ g, ∏ i ∈ t, f i g ^ a i = ∏ i ∈ t, f i g ^ b i) :
    ∀ i ∈ t, (a i : K) = (b i : K) := by
  have key : ∀ g, ∑ i ∈ t, ((a i : K) - (b i : K)) * (f i g).nextCoeff = 0 := by
    intro g
    have h1 := congrArg Polynomial.nextCoeff (h g)
    rw [Monic.nextCoeff_prod _ _ (fun i hi => (hm i hi g).pow _),
      Monic.nextCoeff_prod _ _ (fun i hi => (hm i hi g).pow _)] at h1
    have e1 : ∀ (c : ι → ℕ), ∑ i ∈ t, (f i g ^ c i).nextCoeff
        = ∑ i ∈ t, (c i : K) * (f i g).nextCoeff := by
      intro c
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(hm i hi g).nextCoeff_pow, nsmul_eq_mul]
    rw [e1, e1] at h1
    simp only [sub_mul, Finset.sum_sub_distrib, h1, sub_self]
  intro i hi
  exact sub_eq_zero.mp (hli _ key i hi)
end Formalism.IrreducibleCountingLemmas.Z.BN
