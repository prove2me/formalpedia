-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.gauss_sum_powers
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:40.540802+00:00
-- url     : https://prove2.me/submissions/d5cfd29f-6acf-4b17-8a03-3205c75c725b

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bddAbove_norm_coeff

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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : GaussPow := by
  classical
  intro F K _ _ φ σ Y h k hk Q n
  let E : (σ →₀ ℕ) → (σ →₀ ℕ) := fun n =>
    Finsupp.onFinset n.support (fun y => k y * n y) (fun y hy => by
      rw [Finsupp.mem_support_iff]
      exact fun h0 => hy (by rw [h0, Nat.mul_zero]))
  have hEa : ∀ n y, E n y = k y * n y := fun n y => rfl
  have hE : Function.Injective E := by
    intro n n' hnn
    ext y
    have := congrArg (fun f => f y) hnn
    simp only [hEa] at this
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (hk y)) this
  let Q' : MvPolynomial σ F := ∑ n ∈ Q.support, MvPolynomial.monomial (E n) (MvPolynomial.coeff n Q)
  have h1 : MvPolynomial.eval₂ φ Y Q' = MvPolynomial.eval₂ φ (fun y => Y y ^ k y) Q := by
    rw [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_eq]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [MvPolynomial.eval₂_monomial, Finsupp.onFinset_prod _ (fun _ => pow_zero _)]
    congr 1
    refine Finset.prod_congr rfl fun y _ => ?_
    rw [pow_mul]
  have hc : ∀ n, MvPolynomial.coeff (E n) Q' = MvPolynomial.coeff n Q := by
    intro n
    simp only [Q', MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hE.eq_iff]
    rw [Finset.sum_ite_eq' Q.support n]
    split_ifs with hn
    · rfl
    · exact (MvPolynomial.notMem_support_iff.1 hn).symm
  rw [← h1, h, ← hc]
  exact le_ciSup (bddAbove_norm_coeff Q') (E n)
end Formalism.DworkPowerSeriesWeights
