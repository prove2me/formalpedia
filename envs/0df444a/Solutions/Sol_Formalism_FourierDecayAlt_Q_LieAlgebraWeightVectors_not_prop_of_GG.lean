-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.not_prop_of_GG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:50:36.069033+00:00
-- url     : https://prove2.me/submissions/e522ec90-9f7c-416c-ad47-1dd78369d12c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_glev_unit
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_glev_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
private theorem gA_mulVec {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    Hpk k r *ᵥ v = fun i => Hpk k r i i * v i := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · intro j _ hji
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hv j hj, mul_zero]
    · push Not at hj
      have hij : i ≠ j := fun h => hji h.symm
      have h0 : Hpk k r i j = 0 := by
        simp only [Hpk]
        rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => hij h.2.2)]
      rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h
private theorem gA_herm {v w : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    herm (Hpk k r) v w = ∑ i, star (w i) * (Hpk k r i i * v i) := by
  simp only [herm, dotProduct, gA_mulVec hv, Pi.star_apply]
private theorem gA_term {x : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (i : Fin (2 * r + k + 1)) :
    star (x i) * (Hpk k r i i * x i) =
      ((Complex.normSq (x i) - 2 * (if i = gAlast k r then Complex.normSq (x i) else 0) : ℝ) : ℂ) := by
  by_cases hi : i.val < r ∨ r + k < i.val
  · simp [hx i hi]
  · push Not at hi
    have e : star (x i) * x i = (Complex.normSq (x i) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply]
    have hH : Hpk k r i i = if i.val = r + k then -1 else 1 := by
      simp only [Hpk]
      rw [if_neg (by omega), if_neg (by omega), if_pos ⟨hi.1, hi.2, trivial⟩]
    rw [hH]
    by_cases hl : i = gAlast k r
    · have hv : i.val = r + k := by rw [hl]; rfl
      rw [if_pos hv, if_pos hl, show star (x i) * (-1 * x i) = -(star (x i) * x i) by ring, e]
      push_cast
      ring
    · have hv : i.val ≠ r + k := fun h => hl (Fin.ext h)
      rw [if_neg hv, if_neg hl, one_mul, e]
      simp
private theorem gA_self {x : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) :
    herm (Hpk k r) x x = ((∑ i, Complex.normSq (x i) - 2 * Complex.normSq (x (gAlast k r)) : ℝ) : ℂ) := by
  rw [gA_herm hx]
  simp_rw [gA_term hx]
  rw [← Complex.ofReal_sum]
  congr 1
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq']
  simp
private theorem gA_hz {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    herm (Hpk k r) z z = ((-Tz k r z : ℝ) : ℂ) := by
  have h : Tz k r z = -(herm (Hpk k r) z z).re := rfl
  rw [h, gA_self hz]
  simp
private theorem gA_smul_left (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (c : ℂ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm H (c • v) w = c * herm H v w := by
  simp only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
private theorem gA_smul_right (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (c : ℂ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm H v (c • w) = star c * herm H v w := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]
private theorem gA_mul_star (c : ℂ) : c * star c = (Complex.normSq c : ℂ) := by rw [← starRingEnd_apply, Complex.mul_conj]
private theorem gA_normSq_star (c : ℂ) : Complex.normSq (star c) = Complex.normSq c := by rw [← starRingEnd_apply, Complex.normSq_conj]
private theorem gA_fvec (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  simp [fvec]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
end
end

set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {g : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r)) (hGG : GGl k r z z' g ≠ 0) :
    (∀ c : ℂ, g⁻¹ *ᵥ z ≠ c • z') ∧ ∀ c : ℂ, g *ᵥ z' ≠ c • z := by
  constructor
  · intro c hc
    apply hGG
    have hz_eq : z = c • (g *ᵥ z') := by
      have h := congrArg (g *ᵥ ·) hc
      simp only [Matrix.mulVec_mulVec, (glev_unit hg).2, Matrix.one_mulVec, Matrix.mulVec_smul] at h
      exact h
    have hu : herm (Hpk k r) (g *ᵥ z') (g *ᵥ z') = ((-Tz k r z' : ℝ) : ℂ) := by
      rw [glev_herm hg, gA_hz hz']
    have hzeta : zetaL k r z z' (Fin.last r) g = star c * ((-Tz k r z' : ℝ) : ℂ) := by
      simp only [zetaL, gA_fvec]
      rw [show herm (Hpk k r) (g *ᵥ z') z = herm (Hpk k r) (g *ᵥ z') (c • (g *ᵥ z')) by rw [← hz_eq],
        gA_smul_right, hu]
    have hT : Tz k r z = Complex.normSq c * Tz k r z' := by
      have h : Tz k r z = -(herm (Hpk k r) z z).re := rfl
      rw [h, hz_eq, gA_smul_left, gA_smul_right, ← mul_assoc, gA_mul_star, hu, ← Complex.ofReal_mul,
        Complex.ofReal_re]
      ring
    simp only [GGl]
    rw [hzeta, hT, Complex.normSq_mul, gA_normSq_star, Complex.normSq_ofReal]
    ring
  · intro c hc
    apply hGG
    have hzeta : zetaL k r z z' (Fin.last r) g = c * ((-Tz k r z : ℝ) : ℂ) := by
      simp only [zetaL, gA_fvec]
      rw [hc, gA_smul_left, gA_hz hz]
    have hT : Tz k r z' = Complex.normSq c * Tz k r z := by
      have h1 : herm (Hpk k r) z' z' = herm (Hpk k r) (g *ᵥ z') (g *ᵥ z') := (glev_herm hg z' z').symm
      rw [hc, gA_smul_left, gA_smul_right, ← mul_assoc, gA_mul_star, gA_hz hz] at h1
      have h : Tz k r z' = -(herm (Hpk k r) z' z').re := rfl
      rw [h, h1, ← Complex.ofReal_mul, Complex.ofReal_re]
      ring
    simp only [GGl]
    rw [hzeta, hT, Complex.normSq_mul, Complex.normSq_ofReal]
    ring
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
