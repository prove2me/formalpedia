-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.gb_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:11:18.093818+00:00
-- url     : https://prove2.me/submissions/be07d159-349b-474b-91bc-0ef356a53d41

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_ExistsFrameOfPositiveVector
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_herm
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
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {z v : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (hv : inWb k r v)
    (hvz : herm (Hpk k r) v z = 0) (hv0 : v ≠ 0) : 0 < (herm (Hpk k r) v v).re := by
  classical
  obtain ⟨t, htv⟩ : ∃ t : Fin (2 * r + k + 1), t.val = r + k := ⟨⟨r + k, by omega⟩, rfl⟩
  have key : ∀ a b : Fin (2 * r + k + 1) → ℂ, inWb k r a →
      herm (Hpk k r) a b = -(star (b t) * a t) + ∑ i ∈ Finset.univ.erase t, star (b i) * a i := by
    intro a b ha
    rw [gb_herm ha, ← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
    congr 1
    · rw [if_pos htv]; ring
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hne : i.val ≠ r + k := fun h => Finset.ne_of_mem_erase hi (Fin.ext (by rw [htv]; exact h))
      rw [if_neg hne]; ring
  have nsq : ∀ x : ℂ, (star x * x).re = ‖x‖ ^ 2 := by
    intro x
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring
  have hre : ∀ a : Fin (2 * r + k + 1) → ℂ, inWb k r a →
      (herm (Hpk k r) a a).re = (∑ i ∈ Finset.univ.erase t, ‖a i‖ ^ 2) - ‖a t‖ ^ 2 := by
    intro a ha
    rw [key a a ha, Complex.add_re, Complex.neg_re, nsq, Complex.re_sum]
    simp only [nsq]
    ring
  have hzz : (∑ i ∈ Finset.univ.erase t, ‖z i‖ ^ 2) < ‖z t‖ ^ 2 := by
    have h1 := hre z hz
    unfold Tz at hT
    linarith
  have hvz' : ∑ i ∈ Finset.univ.erase t, star (z i) * v i = star (z t) * v t := by
    have h1 := key v z hv
    rw [hvz] at h1
    linear_combination -h1
  have cs1 : ‖z t‖ * ‖v t‖ ≤ ∑ i ∈ Finset.univ.erase t, ‖z i‖ * ‖v i‖ := by
    have e : ‖z t‖ * ‖v t‖ = ‖∑ i ∈ Finset.univ.erase t, star (z i) * v i‖ := by
      rw [hvz', norm_mul, norm_star]
    rw [e]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_mul, norm_star]
  have cs2 : (∑ i ∈ Finset.univ.erase t, ‖z i‖ * ‖v i‖) ^ 2 ≤
      (∑ i ∈ Finset.univ.erase t, ‖z i‖ ^ 2) * ∑ i ∈ Finset.univ.erase t, ‖v i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hS0 : 0 ≤ ‖z t‖ * ‖v t‖ := by positivity
  have hab : (‖z t‖ * ‖v t‖) ^ 2 ≤
      (∑ i ∈ Finset.univ.erase t, ‖z i‖ ^ 2) * ∑ i ∈ Finset.univ.erase t, ‖v i‖ ^ 2 := by
    nlinarith [mul_le_mul cs1 cs1 hS0 (hS0.trans cs1)]
  have hNz : 0 ≤ ∑ i ∈ Finset.univ.erase t, ‖z i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have hNv : 0 ≤ ∑ i ∈ Finset.univ.erase t, ‖v i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  rw [hre v hv]
  by_contra hneg
  push_neg at hneg
  have hle : (∑ i ∈ Finset.univ.erase t, ‖v i‖ ^ 2) ≤ ‖v t‖ ^ 2 := by linarith
  have hb : ‖v t‖ ^ 2 ≤ 0 := by
    nlinarith [mul_nonneg hNz (sub_nonneg.2 hle), sq_nonneg ‖v t‖]
  have hvt : v t = 0 := by
    have h2 : ‖v t‖ ^ 2 = 0 := le_antisymm hb (sq_nonneg _)
    simpa using h2
  have hNv0 : ∑ i ∈ Finset.univ.erase t, ‖v i‖ ^ 2 = 0 := by linarith
  have hvE : ∀ i ∈ Finset.univ.erase t, v i = 0 := by
    intro i hi
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 hNv0 i hi
    simpa using h3
  apply hv0
  funext i
  by_cases hi : i = t
  · subst hi; simpa using hvt
  · simpa using hvE i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
