-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdicNeighbourhood.Adic.taylor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:14.107232+00:00
-- url     : https://prove2.me/submissions/1216ff5a-8eda-411a-9644-c6f169d3a940

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_Adic_unit_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_prod_expand
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_inverse_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdicNeighbourhood
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.AdicNeighbourhood
namespace Adic
theorem _root_.solution (h : Adic R ϖ) (m a : ℕ) (D : K) (x xi v : Fin m → K) (μ : K)
    (hμ : μ ∈ I R (ϖ : K)) (hx : ∀ k, x k * xi k = 1) (hxi : ∀ k, (ϖ : K) ^ a * xi k ∈ R)
    (hv : ∀ k, ∃ r ∈ R, v k = (ϖ : K) ^ a * μ * r) :
    ∃ ρ ∈ R, g0 D (x + v) = g0 D x + ∑ k, v k * (1 - D * (xi k * ∏ i, xi i)) +
      D * (∏ i, xi i) * μ ^ 2 * ρ := by
  obtain ⟨μ', hμ', eμ⟩ := hμ
  have hμR : μ ∈ R := by rw [eμ]; exact R.mul_mem h.mem hμ'
  have hu : ∀ k, ∃ ρ ∈ R, v k * xi k = μ * ρ := by
    intro k
    obtain ⟨r, hr, e⟩ := hv k
    exact ⟨r * ((ϖ : K) ^ a * xi k), R.mul_mem hr (hxi k), by rw [e]; ring⟩
  have hw : ∀ k, ∃ w ∈ R, (1 + v k * xi k) * w = 1 := by
    intro k
    obtain ⟨ρ, hρ, e⟩ := hu k
    exact h.unit_one _ ⟨μ' * ρ, R.mul_mem hμ' hρ, by rw [e, eμ]; ring⟩
  choose w hwR hw1 using hw
  have hw2 : ∀ k, ∃ e ∈ R, w k = 1 - v k * xi k + μ ^ 2 * e := by
    intro k
    obtain ⟨ρ, hρ, e⟩ := hu k
    refine ⟨ρ ^ 2 * w k, R.mul_mem (R.pow_mem hρ 2) (hwR k), ?_⟩
    have e2 : μ ^ 2 * (ρ ^ 2 * w k) = (v k * xi k) ^ 2 * w k := by rw [e]; ring
    rw [e2]
    linear_combination (1 - v k * xi k) * hw1 k
  obtain ⟨ρ, hρ, -, -, -, e2⟩ := prod_expand hμR Finset.univ w (fun k => v k * xi k)
    (fun k _ => hu k) (fun k _ => hw2 k)
  refine ⟨ρ, hρ, ?_⟩
  have i1 : Ring.inverse (∏ k, x k) = ∏ i, xi i := inverse_eq (by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one fun k _ => hx k)
  have i2 : Ring.inverse (∏ k, (x + v) k) = (∏ i, xi i) * ∏ i, w i := inverse_eq (by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    show (x k + v k) * (xi k * w k) = 1
    linear_combination hw1 k + w k * hx k)
  have s1 : ∑ k, v k * (1 - D * (xi k * ∏ i, xi i)) =
      ∑ k, v k - D * (∏ i, xi i) * ∑ k, v k * xi k := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have s2 : ∑ k, (x + v) k = ∑ k, x k + ∑ k, v k := by
    rw [← Finset.sum_add_distrib]; rfl
  unfold g0
  rw [i1, i2, s1, s2, e2]
  ring
end Adic
end Formalism.FourierDecayAlt.P.AdicNeighbourhood
