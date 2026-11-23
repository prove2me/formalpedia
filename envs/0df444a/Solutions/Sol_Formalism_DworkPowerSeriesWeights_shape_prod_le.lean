-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.shape_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:05:05.969578+00:00
-- url     : https://prove2.me/submissions/f929a189-852f-44b6-a438-448079acda9d

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementH
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MinorProductSupportTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial
variable {σ : Type}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {R : Type u} [CommRing R] {ι : Type*} (g : (σ →₀ ℕ) → ℕ) (hg0 : g 0 = 0)
    (hgadd : ∀ a b, g (a + b) = g a + g b) (f : ι → MvPolynomial σ R) (a : ι → ℕ) (s : Finset ι)
    (h : ∀ c ∈ s, ∀ mono ∈ (f c).support, g mono ≤ a c) :
    ∀ mono ∈ (∏ c ∈ s, f c).support, g mono ≤ ∑ c ∈ s, a c := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro _ mono hm
    rw [Finset.prod_empty, MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
    split_ifs at hm with h0
    · rw [← h0, hg0, Finset.sum_empty]
    · exact absurd rfl hm
  | insert c s hc ih =>
    intro h mono hm
    rw [Finset.prod_insert hc] at hm
    obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
    rw [hgadd, Finset.sum_insert hc]
    exact Nat.add_le_add (h c (Finset.mem_insert_self c s) m1 hm1)
      (ih (fun c' hc' => h c' (Finset.mem_insert_of_mem hc')) m2 hm2)
end Formalism.DworkPowerSeriesWeights
