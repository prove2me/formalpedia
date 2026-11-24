-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.norm_of_inverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:38:00.421306+00:00
-- url     : https://prove2.me/submissions/6ebff851-76fe-4af5-83c2-812beea16ebb

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x6_euclid_cs
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x6_Hpk_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x6_mul_Hpk_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x6_normSq_sgn
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_sig


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x5 C2x6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.NormInv := by
  intro k r g hg
  have hH := GBasic.Hpk_herm k r
  have hsq := GBasic.Hpk_sq k r
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg

  have hleft : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hsq]
  have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv hleft
  have hright : g * g⁻¹ = 1 := by
    rw [hinv]
    first
    | exact Matrix.mul_eq_one_comm.mp hleft
    | exact mul_eq_one_comm.mp hleft
  have hsum : ∑ i, ∑ j, Complex.normSq (g⁻¹ i j) = ∑ i, ∑ j, Complex.normSq (g i j) := by
    have he : ∀ i j, Complex.normSq (g⁻¹ i j) =
        Complex.normSq (g (GBasic.sig k r j) (GBasic.sig k r i)) := by
      intro i j
      rw [hinv, mul_Hpk_apply, Hpk_mul_apply, Matrix.conjTranspose_apply, Complex.normSq_mul,
        Complex.normSq_mul, normSq_sgn, normSq_sgn, Complex.star_def, Complex.normSq_conj]
      ring
    simp only [he]
    let σ : Equiv.Perm (Fin (2 * r + k + 1)) :=
      Function.Involutive.toPerm _ (GBasic.sig_sig k r)
    rw [Finset.sum_comm]
    refine Fintype.sum_equiv σ _ _ fun j => ?_
    exact Fintype.sum_equiv σ _ _ fun i => rfl
  refine ⟨by simp only [B.gN, hsum], ?_⟩

  set i0 : Fin (2 * r + k + 1) := ⟨0, by omega⟩
  have hcs := euclid_cs (fun l => g⁻¹ l i0) (fun l => star (g i0 l))
  have h1 : star (fun l => star (g i0 l)) ⬝ᵥ (fun l => g⁻¹ l i0) = 1 := by
    have := congrFun (congrFun hright i0) i0
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
    simpa [dotProduct] using this
  rw [h1, Complex.normSq_one] at hcs
  have hgN : ∀ h : B.Mat k r, B.gN h ^ 2 = ∑ i, ∑ j, Complex.normSq (h i j) := fun h =>
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)
  have hA : ∑ l, Complex.normSq (g⁻¹ l i0) ≤ B.gN g⁻¹ ^ 2 := by
    rw [hgN, Finset.sum_comm]
    exact Finset.single_le_sum (f := fun j => ∑ l, Complex.normSq (g⁻¹ l j))
      (fun j _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ i0)
  have hB : ∑ l, Complex.normSq (star (g i0 l)) ≤ B.gN g ^ 2 := by
    rw [hgN]
    simp only [Complex.star_def, Complex.normSq_conj]
    exact Finset.single_le_sum (f := fun i => ∑ l, Complex.normSq (g i l))
      (fun i _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ i0)
  have hN0 : 0 ≤ B.gN g := Real.sqrt_nonneg _
  have hEq : B.gN g⁻¹ = B.gN g := by simp only [B.gN, hsum]
  rw [hEq] at hA
  have h4 : 1 ≤ B.gN g ^ 2 * B.gN g ^ 2 :=
    hcs.trans (mul_le_mul hA hB (Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _)
      (sq_nonneg _))
  by_contra hlt
  push_neg at hlt
  have : B.gN g ^ 2 * B.gN g ^ 2 < 1 := by
    have h5 : B.gN g ^ 2 < 1 := by nlinarith
    nlinarith [sq_nonneg (B.gN g)]
  linarith
end Formalism.FourierDecayAlt.P
