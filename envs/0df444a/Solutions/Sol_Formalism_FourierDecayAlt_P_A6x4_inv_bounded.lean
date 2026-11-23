-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x4.inv_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:21.911883+00:00
-- url     : https://prove2.me/submissions/1e960f34-0c93-4a9f-bc1e-c4febb31ba8d

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_ringInv_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_one_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x4
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x4
theorem _root_.solution (hD : LocalDatum K R ψ) (hQ : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) {p q : K}
    (hpq : p * q = 1) (hp : p ∈ R) (hex : ∀ x : K, ∃ m : ℕ, p ^ m * x ∈ R) {Om : Set K}
    (hOm : IsCompact Om) (hu : ∀ z ∈ Om, IsUnit z) :
    ∃ k : ℕ, ∀ z ∈ Om, p ^ k * Ring.inverse z ∈ R := by
  obtain ⟨k, hk⟩ := hOm.elim_directed_cover
    (fun k : ℕ => {z : K | ∃ w, z * w = 1 ∧ p ^ k * w ∈ R})
    (fun k => by
      rw [isOpen_iff_mem_nhds]
      rintro z₀ ⟨w₀, hw₀, hk⟩
      have hN : (fun z => q * w₀ * (z - z₀)) ⁻¹' (R : Set K) ∈ 𝓝 z₀ := by
        apply (hD.isOpen.preimage (by fun_prop)).mem_nhds
        show q * w₀ * (z₀ - z₀) ∈ R
        rw [sub_self, mul_zero]
        exact R.zero_mem
      refine mem_of_superset hN ?_
      intro z hz
      obtain ⟨w', hw', _, hw'R⟩ := one_add hD hQ hpq hp hex hz
      refine ⟨w₀ * w', ?_, ?_⟩
      · have e : z = z₀ * (1 + p * (q * w₀ * (z - z₀))) := by
          linear_combination (-(z - z₀)) * hw₀ - (z₀ * w₀ * (z - z₀)) * hpq
        calc z * (w₀ * w') = z₀ * (1 + p * (q * w₀ * (z - z₀))) * (w₀ * w') := by rw [← e]
          _ = (z₀ * w₀) * ((1 + p * (q * w₀ * (z - z₀))) * w') := by ring
          _ = 1 := by rw [hw₀, hw', one_mul]
      · rw [← mul_assoc]
        exact R.mul_mem hk hw'R)
    (fun z hz => by
      obtain ⟨w, hw⟩ := (hu z hz).exists_right_inv
      obtain ⟨m, hm⟩ := hex w
      exact Set.mem_iUnion.2 ⟨m, w, hw, hm⟩)
    (by
      apply Monotone.directed_le
      rintro m m' h x ⟨w, hw, hx⟩
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      have e : p ^ (m + d) * w = p ^ d * (p ^ m * w) := by ring
      refine ⟨w, hw, ?_⟩
      rw [e]
      exact R.mul_mem (R.pow_mem hp d) hx)
  refine ⟨k, fun z hz => ?_⟩
  obtain ⟨w, hw, h⟩ := hk hz
  rw [ringInv_eq hw]
  exact h
end Formalism.FourierDecayAlt.P.A6x4
