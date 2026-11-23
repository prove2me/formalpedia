-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_coeff_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:30.645633+00:00
-- url     : https://prove2.me/submissions/b1c5bdfb-9950-4dcc-b3f7-40528288ef37

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_lin_pow_val
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_coeff_prod
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnxN_apply
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs


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
open MvPowerSeries Formalism.IncomingBounds
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (a b : ZMod d → K) (f : MvPowerSeries (ZMod d) K) (m : V2 d →₀ ℕ) :
    coeff m (subst (bnxA a b) f) = coeff (bnxN m) f *
      ∏ s, (a s ^ m (false, s) * b s ^ m (true, s) *
        ((m (false, s) + m (true, s)).choose (m (false, s)) : K)) := by
  have ha : HasSubst (bnxA a b) := hasSubst_of_constantCoeff_zero fun s => by simp [bnxA]
  rw [coeff_subst ha]
  have hterm : ∀ dd : ZMod d →₀ ℕ, coeff m (dd.prod fun s e => bnxA a b s ^ e) =
      ∏ s, (if m (false, s) + m (true, s) = dd s then
        a s ^ m (false, s) * b s ^ m (true, s) * ((dd s).choose (m (false, s)) : K) else 0) := by
    intro dd
    rw [Finsupp.prod_fintype _ _ (fun s => pow_zero _), bnx_coeff_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    have hres : bnxRes m s = Finsupp.single (false, s) (m (false, s)) +
        Finsupp.single (true, s) (m (true, s)) := rfl
    rw [hres]
    exact bnx_lin_pow_val (x := (false, s)) (y := (true, s)) (by simp) (a s) (b s) (dd s) _ _
  rw [finsum_eq_single _ (bnxN m)]
  · rw [hterm, smul_eq_mul]
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [if_pos (bnxN_apply m s).symm, bnxN_apply]
  · intro dd hdd
    have hex : ∃ s, dd s ≠ bnxN m s := by
      by_contra hc
      push_neg at hc
      exact hdd (Finsupp.ext hc)
    obtain ⟨s, hs⟩ := hex
    rw [hterm, Finset.prod_eq_zero (Finset.mem_univ s), smul_zero]
    rw [if_neg]
    intro h
    apply hs
    rw [← h, bnxN_apply]
end Formalism.DworkPowerSeriesWeights
