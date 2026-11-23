-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.special_det_monomial_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:05:23.880379+00:00
-- url     : https://prove2.me/submissions/1f7bb546-c210-4fb6-8ba7-215abbf0ef2c

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special

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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {n σ R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    [Nontrivial R] (E : n → n → σ →₀ ℕ)
    (hE : Function.Injective fun p : Equiv.Perm n => ∑ c, E (p c) c) :
    (Matrix.of fun r c => (MvPolynomial.monomial (E r c) (1 : R))).det ≠ 0 := by
  classical
  intro h
  have h2 := congrArg (MvPolynomial.coeff (∑ c, E c c)) h
  rw [Matrix.det_apply, MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at h2
  simp only [Matrix.of_apply, ← MvPolynomial.monomial_sum_one] at h2
  rw [Finset.sum_eq_single (1 : Equiv.Perm n)] at h2
  · simp [MvPolynomial.coeff_monomial] at h2
  · intro p _ hp
    have hne : ∑ c, E (p c) c ≠ ∑ c, E c c := fun he => hp (hE (by simpa using he))
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hs | hs <;>
      simp [hs, MvPolynomial.coeff_monomial, hne]
  · simp
end Formalism.DworkPowerSeriesWeights
