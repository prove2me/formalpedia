-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.hermitian_gauss_sum_ring
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:05:35.562528+00:00
-- url     : https://prove2.me/submissions/09379bc7-a18b-40d0-b8a6-905c94fb5ae2

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : HermGaussRing := by
  intro S _ _ _ n Gm ψ φ hdet hφ hadd
  classical
  set yv : (Fin n → S) → Fin n → S := fun d => Gm.mulVec (fun j => star (d j)) with hyv
  have hB : ∀ u d : Fin n → S, ∑ i, ∑ j, u i * Gm i j * star (d j) = ∑ i, u i * yv d i := by
    intro u d
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hyv, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  simp only [hB] at hadd
  set T : (Fin n → S) → ℂ := fun d => ∑ v : Fin n → S, ψ (∑ i, v i * yv d i) with hT
  have h1 : ((‖∑ u, φ u‖ ^ 2 : ℝ) : ℂ) = ∑ d, φ d * T d := by
    push_cast
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum, Finset.sum_comm]
    have : ∀ v : Fin n → S, ∑ u, φ u * (starRingEnd ℂ) (φ v) = ∑ d, φ d * ψ (∑ i, v i * yv d i) := by
      intro v
      rw [← Fintype.sum_equiv (Equiv.addLeft v) (fun d => φ (v + d) * (starRingEnd ℂ) (φ v)) _ (fun d => rfl)]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [hadd]
      have : φ v * (starRingEnd ℂ) (φ v) = 1 := by rw [Complex.mul_conj', hφ]; simp
      linear_combination (φ d * ψ (∑ i, v i * yv d i)) * this
    simp_rw [this, hT, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hTle : ∀ d, ‖T d‖ ≤ (Fintype.card S : ℝ) ^ n := by
    intro d
    calc ‖T d‖ ≤ ∑ v : Fin n → S, ‖ψ (∑ i, v i * yv d i)‖ := norm_sum_le _ _
      _ = _ := by simp [AddChar.norm_apply]
  have hT0 : ∀ d, (¬ ∀ i c, ψ (c * yv d i) = 1) → T d = 0 := by
    intro d hd
    push Not at hd
    obtain ⟨i, c, hc⟩ := hd
    have : T d = ψ (c * yv d i) * T d := by
      conv_lhs => rw [hT]
      simp only
      rw [← Fintype.sum_equiv (Equiv.addRight (Pi.single i c : Fin n → S))
        (fun v : Fin n → S => ψ (∑ k, (v + (Pi.single i c : Fin n → S)) k * yv d k)) _ (fun v => rfl), hT, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [← AddChar.map_add_eq_mul]
      congr 1
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      rw [add_comm]
      congr 1
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk; simp [Pi.single_eq_of_ne hk]
      · simp
    have h2 : (1 - ψ (c * yv d i)) * T d = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (sub_eq_zero.1 h3).symm hc
    · exact h3
  have hinj : Function.Injective yv := by
    intro d d' hdd
    have h3 : ∀ x : Fin n → S, Gm⁻¹.mulVec (Gm.mulVec x) = x := fun x => by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Gm hdet, Matrix.one_mulVec]
    have h4 : (fun j => star (d j)) = fun j => star (d' j) := by
      rw [← h3 (fun j => star (d j)), ← h3 (fun j => star (d' j))]
      exact congrArg _ hdd
    ext j
    exact star_injective (congrFun h4 j)
  have hcount : ((univ.filter fun d => ∀ i c, ψ (c * yv d i) = 1).card : ℝ)
      ≤ (Nat.card {y : S // ∀ c, ψ (c * y) = 1} : ℝ) ^ n := by
    have : (univ.filter fun d => ∀ i c, ψ (c * yv d i) = 1).card
        ≤ Nat.card (Fin n → {y : S // ∀ c, ψ (c * y) = 1}) := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      refine Nat.card_le_card_of_injective
        (fun d : {d // ∀ i c, ψ (c * yv d i) = 1} => fun i => (⟨yv d.1 i, d.2 i⟩ : {y : S // ∀ c, ψ (c * y) = 1})) ?_
      intro d d' hdd
      apply Subtype.ext
      apply hinj
      ext i
      exact congrArg Subtype.val (congrFun hdd i)
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at this
    exact_mod_cast this
  have h2 : ‖∑ u, φ u‖ ^ 2 = ‖∑ d, φ d * T d‖ := by
    rw [← h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [h2]
  calc ‖∑ d, φ d * T d‖ ≤ ∑ d, ‖φ d * T d‖ := norm_sum_le _ _
    _ = ∑ d, ‖T d‖ := by simp [hφ]
    _ ≤ ∑ d, if (∀ i c, ψ (c * yv d i) = 1) then (Fintype.card S : ℝ) ^ n else 0 := by
        refine Finset.sum_le_sum fun d _ => ?_
        split_ifs with hd
        · exact hTle d
        · rw [hT0 d hd, norm_zero]
    _ = ((univ.filter fun d => ∀ i c, ψ (c * yv d i) = 1).card : ℝ) * (Fintype.card S : ℝ) ^ n := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        rw [mul_comm]
        gcongr
end Formalism.HermitianLatticeCounting.P.S4aux
