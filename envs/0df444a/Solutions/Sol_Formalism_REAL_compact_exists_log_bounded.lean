-- Prove2me | solution 1 for Formalism.REAL.compact_exists_log_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:24:12.385515+00:00
-- url     : https://prove2.me/submissions/9be2f034-2366-47a6-912e-e3006be2f102

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactExponentialSurjective
import Theorems.Thm_Formalism_REAL_norm_log_sq_le_unit_circle
import Theorems.Thm_Formalism_REAL_frobenius_eq_trace
import Theorems.Thm_Formalism_REAL_frobenius_nonneg_matrix
import Theorems.Thm_Formalism_REAL_Jm_conjTranspose


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧ NormedSpace.exp Y = k ∧ hs Y ≤ 3 * hs (k - 1) := by
  obtain ⟨hu, hJ⟩ := hk
  have hN : IsStarNormal k := isStarNormal_of_mem_unitary hu
  have hcont : ∀ f : ℂ → ℂ, ContinuousOn f (spectrum ℂ k) :=
    fun f => (Matrix.finite_spectrum k).continuousOn f
  have hcirc : ∀ z ∈ spectrum ℂ k, ‖z‖ = 1 := fun z hz => spectrum.norm_eq_one_of_unitary hu hz
  have hJs : star (Jm ε) = Jm ε := by rw [Matrix.star_eq_conjTranspose, Jm_conjTranspose]
  have hstarJ : star k * Jm ε = Jm ε * star k := by
    have := congrArg star hJ
    simp only [star_mul, hJs] at this
    exact this.symm
  set Y := cfc Complex.log k with hY
  have hcomm : Commute Y (Jm ε) := Commute.cfc hJ hstarJ Complex.log
  have hstarY : star Y = -Y := by
    rw [hY, ← cfc_star, ← cfc_neg Complex.log k]
    refine cfc_congr fun z hz => ?_
    have h1 := hcirc z hz
    apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]
  refine ⟨Y, ⟨?_, hcomm.eq⟩, ?_, ?_⟩
  · show Yᴴ * Jm ε + Jm ε * Y = 0
    rw [← Matrix.star_eq_conjTranspose, hstarY, neg_mul, hcomm.eq]
    exact neg_add_cancel _
  · rw [← CFC.complex_exp_eq_normedSpace_exp, hY,
      ← cfc_comp Complex.exp Complex.log k (hg := Complex.continuous_exp.continuousOn) (hf := hcont _)]
    rw [cfc_congr (g := id) (fun z hz => by
      have h1 := hcirc z hz
      have h0 : z ≠ 0 := by
        rintro rfl
        simp at h1
      simp [Complex.exp_log h0])]
    exact cfc_id ℂ k
  · (have hF : cfc (fun z => 3 * (star (z - 1) * (z - 1)) - star (Complex.log z) * Complex.log z) k =
        (3 : ℂ) • (star (k - 1) * (k - 1)) - star Y * Y := by
       rw [cfc_sub (fun z => 3 * (star (z - 1) * (z - 1))) (fun z => star (Complex.log z) * Complex.log z) k
         (hcont _) (hcont _)]
       rw [cfc_const_mul 3 (fun z => star (z - 1) * (z - 1)) k (hcont _)]
       rw [cfc_mul (fun z => star (z - 1)) (fun z => z - 1) k (hcont _) (hcont _)]
       rw [cfc_mul (fun z => star (Complex.log z)) Complex.log k (hcont _) (hcont _)]
       rw [cfc_star (fun z => z - 1) k, cfc_star Complex.log k]
       rw [cfc_sub (fun z => z) (fun _ => 1) k (hcont _) (hcont _), cfc_id' ℂ k, cfc_const_one ℂ k]
     set G := cfc (fun z => ((Real.sqrt (3 * ‖z - 1‖ ^ 2 - ‖Complex.log z‖ ^ 2) : ℝ) : ℂ)) k with hG
     have hFG : cfc (fun z => 3 * (star (z - 1) * (z - 1)) - star (Complex.log z) * Complex.log z) k =
         star G * G := by
       rw [hG, ← cfc_star, ← cfc_mul _ _ k (hcont _) (hcont _)]
       refine cfc_congr fun z hz => ?_
       have hsc := norm_log_sq_le_unit_circle z (hcirc z hz)
       have hnn : 0 ≤ 3 * ‖z - 1‖ ^ 2 - ‖Complex.log z‖ ^ 2 := by linarith
       simp only [Complex.star_def, Complex.conj_ofReal]
       rw [Complex.conj_mul', Complex.conj_mul', ← Complex.ofReal_mul, Real.mul_self_sqrt hnn]
       push_cast
       ring
     have htr := congrArg Matrix.trace (hF.symm.trans hFG)
     rw [Matrix.trace_sub, Matrix.trace_smul, ← frobenius_eq_trace, ← frobenius_eq_trace, ← frobenius_eq_trace,
       smul_eq_mul] at htr
     have h4 : (3 : ℂ) * (hs (k - 1) : ℂ) - (hs Y : ℂ) = ((3 * hs (k - 1) - hs Y : ℝ) : ℂ) := by push_cast; ring
     rw [h4] at htr
     have h5 := Complex.ofReal_injective htr
     have h6 := frobenius_nonneg_matrix G
     linarith)
end Formalism.REAL
