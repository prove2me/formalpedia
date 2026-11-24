-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.cauchyBinetMax
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:50.289073+00:00
-- url     : https://prove2.me/submissions/0ea80477-9278-4b83-897f-cb2c8636fb51

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ParameterInequalities
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_DetMulEqSumPrincipal
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_det_mul_eq_sum_principal
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_principal_minor_factor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Finset Matrix Polynomial
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : CauchyBinetMax := by
  intro i N r M hM hNr
  classical
  let g : Finset (Fin N) → ℝ := fun S =>
    if h : S.card = i then ‖(M.submatrix id (S.orderEmbOfFin h)).det‖ ^ 2 else 0
  have h1 : (1 : ℂ) = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard i,
      ((Mᴴ * M).submatrix (Subtype.val : S → Fin N) Subtype.val).det := by
    rw [← det_mul_eq_sum_principal M Mᴴ, hM, Matrix.det_one]
  have h2 : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard i,
      ((Mᴴ * M).submatrix (Subtype.val : S → Fin N) Subtype.val).det = ((g S : ℝ) : ℂ) := by
    intro S hS
    have hc := (Finset.mem_powersetCard.1 hS).2
    rw [principal_minor_factor M Mᴴ S hc]
    simp only [g, dif_pos hc]
    have e : Mᴴ.submatrix (S.orderEmbOfFin hc) id = (M.submatrix id (S.orderEmbOfFin hc))ᴴ := by
      ext a b
      simp [Matrix.conjTranspose_apply]
    rw [e, Matrix.det_conjTranspose, Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  have h3 : (1 : ℝ) = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard i, g S := by
    have := h1.trans (Finset.sum_congr rfl h2)
    exact_mod_cast this
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard i, g S < (2 : ℝ) ^ (-(r : ℝ)) := by
    intro S hS
    have hc := (Finset.mem_powersetCard.1 hS).2
    simp only [g, dif_pos hc]
    have h4 := hcon _ (S.orderEmbOfFin hc).strictMono
    have h5 : ‖(M.submatrix id (S.orderEmbOfFin hc)).det‖ ^ 2 < ((2 : ℝ) ^ (-(r : ℝ) / 2)) ^ 2 :=
      pow_lt_pow_left₀ h4 (norm_nonneg _) (by norm_num)
    have h6 : ((2 : ℝ) ^ (-(r : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ (-(r : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    exact h5.trans_eq h6
  by_cases hne : ((Finset.univ : Finset (Fin N)).powersetCard i).Nonempty
  · have h6 := Finset.sum_lt_sum_of_nonempty hne hlt
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin] at h6
    have h7 : ((N.choose i : ℕ) : ℝ) ≤ (2 : ℝ) ^ (N : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast Nat.choose_le_two_pow N i
    have h8 : (2 : ℝ) ^ (N : ℝ) * (2 : ℝ) ^ (-(r : ℝ)) ≤ 1 := by
      rw [← Real.rpow_add (by norm_num)]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      have : (N : ℝ) ≤ r := by exact_mod_cast hNr
      linarith
    have h9 : ((N.choose i : ℕ) : ℝ) * (2 : ℝ) ^ (-(r : ℝ)) ≤ (2 : ℝ) ^ (N : ℝ) * (2 : ℝ) ^ (-(r : ℝ)) :=
      mul_le_mul_of_nonneg_right h7 (by positivity)
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at h3
    norm_num at h3
end Formalism.LatticeBaseChangeAlt
