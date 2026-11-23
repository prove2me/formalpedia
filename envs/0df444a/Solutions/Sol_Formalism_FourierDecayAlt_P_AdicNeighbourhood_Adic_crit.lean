-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdicNeighbourhood.Adic.crit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:00.873937+00:00
-- url     : https://prove2.me/submissions/641fbe22-b768-4ed5-95d3-38ad666505d0

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_Adic_near_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_Adic_root
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_Near_prod

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
theorem _root_.solution (h : Adic R ϖ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (m a : ℕ)
    (B : AddSubgroup K) (hB : (B : Set K) ∈ 𝓝 (0 : K)) :
    ∃ j : ℕ, ∀ (D : Kˣ) (x xi : Fin m → K), (∀ k, x k * xi k = 1) →
      (∀ k, (ϖ : K) ^ a * x k ∈ R) →
      (∀ k, 1 - (D : K) * (xi k * ∏ i, xi i) ∈ I R ((ϖ : K) ^ j)) →
      ∃ z : Kˣ, z ^ (m + 1) = D ∧ ∀ k, x k - (z : K) ∈ B := by
  obtain ⟨b, hb⟩ := h.basis _ hB
  obtain ⟨v, hv⟩ := hn (m + 1) (by omega)
  obtain ⟨e, he⟩ := h.absorb (((v⁻¹ : Kˣ) : K) ^ 2)
  refine ⟨a + b + 1 + e, fun D x xi hx hxa hg => ?_⟩
  obtain ⟨πi, hπ⟩ : ∃ p : K, p = ∏ i, xi i := ⟨_, rfl⟩
  obtain ⟨π, hπx⟩ : ∃ p : K, p = ∏ i, x i := ⟨_, rfl⟩
  rw [← hπ] at hg
  have hvv : ((m + 1 : ℕ) : K) * ((v⁻¹ : Kˣ) : K) = 1 := by rw [← hv]; simp
  have hϖj : (ϖ : K) ^ (a + b + 1 + e) ∈ R := R.pow_mem h.mem _
  have hck : ∀ k, Near R ((ϖ : K) ^ (a + b + 1 + e)) ((D : K) * (xi k * πi)) := by
    intro k
    obtain ⟨r, hr, e1⟩ := hg k
    exact ⟨-r, R.neg_mem hr, by linear_combination -e1⟩
  obtain ⟨r0, hr0, e0⟩ := Near.prod hϖj Finset.univ (fun k => (D : K) * (xi k * πi)) (fun k _ => hck k)
  have hb1 : Near R (((m + 1 : ℕ) : K) ^ 2 * (ϖ : K) ^ (a + b + 1)) (∏ k, (D : K) * (xi k * πi)) :=
    ⟨(ϖ : K) ^ e * ((v⁻¹ : Kˣ) : K) ^ 2 * r0, R.mul_mem he hr0, by
      rw [e0]
      have : ((m + 1 : ℕ) : K) ^ 2 * ((v⁻¹ : Kˣ) : K) ^ 2 = 1 := by rw [← mul_pow, hvv, one_pow]
      rw [pow_add (ϖ : K) (a + b + 1) e]
      linear_combination (-(ϖ : K) ^ (a + b + 1) * (ϖ : K) ^ e * r0) * this⟩
  have hcI : (ϖ : K) ^ (a + b + 1) ∈ I R (ϖ : K) := ⟨(ϖ : K) ^ (a + b), R.pow_mem h.mem _, by ring⟩
  obtain ⟨κ, hκ, hκs⟩ := h.root (m + 1) hcI hb1
  have hscI : ((m + 1 : ℕ) : K) * (ϖ : K) ^ (a + b + 1) ∈ I R (ϖ : K) :=
    ⟨((m + 1 : ℕ) : K) * (ϖ : K) ^ (a + b),
      R.mul_mem (natCast_mem R (m + 1)) (R.pow_mem h.mem _), by ring⟩
  obtain ⟨w, hκw, -, hw⟩ := h.near_inv hscI hκ
  have hprod : ∏ k, (D : K) * (xi k * πi) = (D : K) ^ m * πi ^ (m + 1) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← hπ]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  have hππ : π * πi = 1 := by
    rw [hπ, hπx, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => hx k
  have hDD : (D : K) * ((D⁻¹ : Kˣ) : K) = 1 := by simp
  have hz1 : (D : K) * πi * w * (((D⁻¹ : Kˣ) : K) * π * κ) = 1 := by
    linear_combination (π * πi * κ * w) * hDD + (κ * w) * hππ + hκw
  refine ⟨⟨(D : K) * πi * w, ((D⁻¹ : Kˣ) : K) * π * κ, hz1, by rw [mul_comm]; exact hz1⟩, ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    show ((D : K) * πi * w) ^ (m + 1) = (D : K)
    have h1 : κ ^ (m + 1) * w ^ (m + 1) = 1 := by rw [← mul_pow, hκw, one_pow]
    rw [hκs, hprod] at h1
    linear_combination (D : K) * h1
  · intro k
    show x k - (D : K) * πi * w ∈ B
    obtain ⟨r1, hr1, eκ⟩ := hκ
    obtain ⟨rk, hrk, ek⟩ := hck k
    have : x k - (D : K) * πi * w = (ϖ : K) ^ b * (((ϖ : K) ^ a * x k) * w *
        (((m + 1 : ℕ) : K) * (ϖ : K) * r1 - (ϖ : K) ^ (1 + e) * rk)) := by
      linear_combination (-x k) * hκw + ((D : K) * πi * w) * hx k + (x k * w) * eκ - (x k * w) * ek
    rw [this]
    exact hb _ (R.mul_mem (R.mul_mem (hxa k) hw) (R.sub_mem
      (R.mul_mem (R.mul_mem (natCast_mem R (m + 1)) h.mem) hr1)
      (R.mul_mem (R.pow_mem h.mem _) hrk)))
end Adic
end Formalism.FourierDecayAlt.P.AdicNeighbourhood
