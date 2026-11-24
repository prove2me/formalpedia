-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DeterminantVectorSums.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:36:28.860662+00:00
-- url     : https://prove2.me/submissions/d78218fb-3aa4-4cdb-a13a-cff6df446e55

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StarSumLemmas
import Theorems.Thm_Formalism_FourierDecayAlt_P_DeterminantVectorSums_aeval_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_DeterminantVectorSums_ch
import Theorems.Thm_Formalism_FourierDecayAlt_P_DeterminantVectorSums_basis_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DeterminantVectorSums
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {W : Type} [AddCommGroup W] [Module ℂ W]
namespace Formalism.FourierDecayAlt.P.DeterminantVectorSums
theorem _root_.solution (hPV : PolyVanish) (G : Submodule ℂ W) (K : Module.End ℂ W) (hK : ∀ x ∈ G, K x ∈ G)
    (A : ℕ → Module.End ℂ W) (N : ℕ) (r : Fin (N + 1) → ℂ) (hr : Function.Injective r)
    (h : ∀ x ∈ G, ∀ u : ℂ, (∑ s ∈ range (N + 1), u ^ s • A s) (u • x - K x) = (∏ j, (u - r j)) • x) :
    ∀ x ∈ G, ∃ Φ : Fin (N + 1) → W, (∀ i, Φ i ∈ G) ∧ ∑ i, Φ i = x ∧
      ∀ i u, (∑ s ∈ range (N + 1), u ^ s • A s) (Φ i) = (∏ j ∈ univ.erase i, (u - r j)) • Φ i := by
  intro x hx
  have hP : (∏ j, (X - C (r j))).natDegree < (N + 1) + 1 := by
    simp
  have hev : ∀ (S : Finset (Fin (N + 1))) (u : ℂ), (∏ j ∈ S, (X - C (r j))).eval u = ∏ j ∈ S, (u - r j) := by
    intro S u
    rw [Polynomial.eval_prod]
    simp
  have hch := ch hPV G K hK A (N + 1) (∏ j, (X - C (r j))) hP (by intro x hx u; rw [hev]; exact h x hx u)
  refine ⟨fun i => aeval K (Lagrange.basis univ r i) x, fun i => aeval_mem G K hK _ x hx, ?_, ?_⟩
  · rw [← LinearMap.sum_apply, ← map_sum, Lagrange.sum_basis (hr.injOn) Finset.univ_nonempty, map_one]
    rfl
  intro i u
  set φ := aeval K (Lagrange.basis univ r i) x with hφ
  have hφG : φ ∈ G := aeval_mem G K hK _ x hx
  have hKφ : K φ = r i • φ := by
    have h1 : aeval K ((X - C (r i)) * Lagrange.basis univ r i) x = 0 := by
      rw [basis_mul, map_mul, Module.End.mul_apply, hch x hx, map_zero]
    rw [map_mul, Module.End.mul_apply, ← hφ, map_sub, aeval_X, aeval_C, LinearMap.sub_apply, sub_eq_zero] at h1
    rw [h1]
    rfl
  have hQ : (∏ j ∈ univ.erase i, (X - C (r j))).natDegree < N + 1 := by
    simp
  have h2 := hPV W (N + 1) (fun s => A s φ - (∏ j ∈ univ.erase i, (X - C (r j))).coeff s • φ) {r i} ?_
  · have h3 : ∑ s ∈ range (N + 1), u ^ s • (A s φ - (∏ j ∈ univ.erase i, (X - C (r j))).coeff s • φ) = 0 :=
      Finset.sum_eq_zero (fun s hs => by rw [h2 s hs, smul_zero])
    simp only [smul_sub, Finset.sum_sub_distrib, sub_eq_zero] at h3
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply]
    rw [h3, ← hev, Polynomial.eval_eq_sum_range' hQ, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [smul_smul, mul_comm]
  intro u hu
  have hne : u - r i ≠ 0 := sub_ne_zero.2 (by simpa using hu)
  have h4 := h φ hφG u
  rw [hKφ, ← sub_smul, map_smul, ← Finset.mul_prod_erase univ _ (Finset.mem_univ i), mul_smul] at h4
  have h5 := smul_right_injective W hne h4
  simp only [smul_sub, Finset.sum_sub_distrib, sub_eq_zero]
  rw [LinearMap.sum_apply] at h5
  simp only [LinearMap.smul_apply] at h5
  rw [h5, ← hev, Polynomial.eval_eq_sum_range' hQ, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [smul_smul, mul_comm]
end Formalism.FourierDecayAlt.P.DeterminantVectorSums
