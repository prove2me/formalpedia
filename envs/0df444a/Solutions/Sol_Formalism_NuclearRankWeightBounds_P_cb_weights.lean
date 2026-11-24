-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.cb_weights
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:28:02.583765+00:00
-- url     : https://prove2.me/submissions/e408f348-6dd8-4a3f-9ef9-ccd3aa1344c8

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_DetMulDiagonalMulEqSum
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_det_mul_diagonal_mul_eq_sum
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_coeff_prod_one_add
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_moment
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_two_coeff_two_det
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_sum_castLE_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Matrix Polynomial Finset
open scoped ComplexOrder
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution : Formalism.NuclearRankWeightBounds.D.CBWeights := by
  intro N Y hY i hi
  set U : Matrix (Fin N) (Fin N) ℂ := (hY.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) with hUdef
  set D : Fin N → ℂ := RCLike.ofReal ∘ hY.eigenvalues with hDdef
  have hD : ∀ j, D j = (hY.eigenvalues j : ℂ) := fun j => rfl
  have hUU : U * Uᴴ = 1 := by
    simpa [U, star_eq_conjTranspose] using Unitary.coe_mul_star_self hY.eigenvectorUnitary
  have hUU' : Uᴴ * U = 1 := by
    simpa [U, star_eq_conjTranspose] using Unitary.coe_star_mul_self hY.eigenvectorUnitary
  have hspec : Y = U * diagonal D * Uᴴ := by
    conv_lhs => rw [hY.spectral_theorem]
    simp [U, D, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  set c : Fin i → Fin N := Fin.castLE hi with hc
  set A : Matrix (Fin i) (Fin N) ℂ := U.submatrix c id with hA
  have hsub : ∀ d : Fin N → ℂ, (U * diagonal d * Uᴴ).submatrix c c = A * diagonal d * Aᴴ := by
    intro d; ext a b; simp [A, Matrix.mul_apply, conjTranspose_apply]
  have hAA : A * Aᴴ = 1 := by
    have := hsub (fun _ => 1)
    rw [diagonal_one, Matrix.mul_one, Matrix.mul_one, hUU] at this
    rw [← this]; ext a b; simp [one_apply, c]
  set W : Finset (Fin N) → ℂ := fun J =>
    ((Aᴴ * A).submatrix (fun x : J => (x : Fin N)) (fun x : J => (x : Fin N))).det with hWdef
  have hWnn : ∀ J, 0 ≤ W J := by
    intro J
    have e : (Aᴴ * A).submatrix (fun x : J => (x : Fin N)) (fun x : J => (x : Fin N))
        = (A.submatrix id (fun x : J => (x : Fin N)))ᴴ * A.submatrix id (fun x : J => (x : Fin N)) := by
      rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
        Matrix.conjTranspose_submatrix A id (fun x : J => (x : Fin N))]
    have hp := posSemidef_conjTranspose_mul_self (A.submatrix id (fun x : J => (x : Fin N)))
    rw [← e] at hp
    exact hp.det_nonneg
  set w : Finset (Fin N) → ℝ := fun J => (W J).re with hwdef
  have hw0 : ∀ J, 0 ≤ w J := fun J => (Complex.nonneg_iff.mp (hWnn J)).1
  have hW : ∀ J, W J = (w J : ℂ) := fun J => by
    have := (Complex.nonneg_iff.mp (hWnn J)).2
    apply Complex.ext <;> simp [w, this.symm]
  have key : ∀ d : Fin N → ℂ, (A * diagonal d * Aᴴ).det
      = ∑ J ∈ powersetCard i (univ : Finset (Fin N)), (∏ j ∈ J, d j) * (w J : ℂ) := by
    intro d; rw [det_mul_diagonal_mul_eq_sum]
    refine sum_congr rfl fun J _ => ?_
    rw [← hW J]
  have mom : ∀ (ν : Fin N → ℂ) (m : ℕ),
      ∑ J ∈ powersetCard i (univ : Finset (Fin N)), (∏ j ∈ J, (1 + X * C (ν j))).coeff m * (w J : ℂ)
      = (det (1 + (X : ℂ[X]) • (A * diagonal ν * Aᴴ).map C)).coeff m := by
    intro ν m
    rw [← moment A hAA ν m]
    refine sum_congr rfl fun J _ => ?_
    rw [← hW J]
  have hdiag : ∀ a, ((Y a a).re : ℂ) = Y a a := fun a => by simpa using hY.coe_re_apply_self a

  have m1 : ∑ J ∈ powersetCard i (univ : Finset (Fin N)), (w J : ℂ) * (∑ j ∈ J, D j)
      = ∑ a : Fin i, Y (c a) (c a) := by
    have h := mom D 1
    rw [coeff_det_one_add_X_smul_one, ← hsub, ← hspec] at h
    rw [show ∑ a : Fin i, Y (c a) (c a) = trace (Y.submatrix c c) from rfl, ← h]
    refine sum_congr rfl fun J _ => ?_
    rw [(coeff_prod_one_add D J).2.1, mul_comm]
  refine ⟨w, hw0, ?_, ?_, ?_, ?_⟩
  · have h := key (fun _ => 1)
    rw [diagonal_one, Matrix.mul_one, hAA, det_one] at h
    simp only [prod_const_one, one_mul] at h
    exact_mod_cast h.symm
  · have hexp : NormedSpace.exp Y = U * diagonal (fun j => Complex.exp (D j)) * Uᴴ := by
      let u : (Matrix (Fin N) (Fin N) ℂ)ˣ := ⟨U, Uᴴ, hUU, hUU'⟩
      have h := Matrix.exp_units_conj u (diagonal D)
      rw [hspec]
      change NormedSpace.exp ((u : Matrix (Fin N) (Fin N) ℂ) * diagonal D * ((u⁻¹ : (Matrix (Fin N) (Fin N) ℂ)ˣ) : Matrix (Fin N) (Fin N) ℂ)) = _
      rw [h, Matrix.exp_diagonal, Pi.exp_def]
      simp only [← Complex.exp_eq_exp_ℂ]
      rfl
    unfold Formalism.NuclearRankWeightBounds.D.lead
    rw [dif_pos hi, hexp]
    change ((U * _ * Uᴴ).submatrix c c).det = _
    rw [hsub, key]
    push_cast
    refine sum_congr rfl fun J _ => ?_
    rw [mul_comm, ← Complex.exp_sum]
    simp only [hD]
  · apply Complex.ofReal_injective
    push_cast
    simp_rw [hdiag]
    rw [← sum_castLE_eq hi, ← m1]
    simp only [hD]
  · set F := univ.filter (fun a : Fin N => a.val < i) with hF
    set G := univ.filter (fun b : Fin N => i ≤ b.val) with hGdef
    have h2 := mom D 2
    rw [← hsub, ← hspec] at h2
    have h3 := two_coeff_two_det (Y.submatrix c c) (hY.submatrix c)
    have hYY : Y * Y = U * diagonal (fun j => D j * D j) * Uᴴ := by
      rw [hspec]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hUU', Matrix.one_mul, ← Matrix.mul_assoc (diagonal D) (diagonal D),
        diagonal_mul_diagonal]
    have hq := mom (fun j => D j * D j) 1
    rw [coeff_det_one_add_X_smul_one, ← hsub, ← hYY] at hq
    have hsplit : ∀ J : Finset (Fin N), (∑ j ∈ J, D j) ^ 2
        = (∏ j ∈ J, (1 + X * C (D j * D j))).coeff 1 + 2 * (∏ j ∈ J, (1 + X * C (D j))).coeff 2 := by
      intro J
      rw [(coeff_prod_one_add _ J).2.1, (coeff_prod_one_add D J).2.2]
      simp [pow_two]
    have hcx : ∑ J ∈ powersetCard i (univ : Finset (Fin N)), (w J : ℂ) * (∑ j ∈ J, D j) ^ 2
        = trace ((Y * Y).submatrix c c) + ((trace (Y.submatrix c c)) ^ 2
            - trace (Y.submatrix c c * Y.submatrix c c)) := by
      rw [← h3, ← hq, ← h2, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun J _ => ?_
      rw [hsplit]; ring
    have t1 : trace ((Y * Y).submatrix c c) = ∑ a : Fin i, ∑ b : Fin N, Y (c a) b * Y b (c a) := by
      simp [trace, mul_apply]
    have t2 : trace (Y.submatrix c c * Y.submatrix c c)
        = ∑ a : Fin i, ∑ a' : Fin i, Y (c a) (c a') * Y (c a') (c a) := by
      simp [trace, mul_apply]
    have t0 : trace (Y.submatrix c c) = ∑ a : Fin i, Y (c a) (c a) := rfl
    have hG : ∀ f : Fin N → ℂ, ∑ b, f b = ∑ b ∈ F, f b + ∑ b ∈ G, f b := by
      intro f
      rw [← sum_filter_add_sum_filter_not univ (fun b : Fin N => b.val < i)]
      simp only [not_lt, F, G]
    have hrow : ∀ a : Fin i, ∑ b : Fin N, Y (c a) b * Y b (c a)
        = ∑ a' : Fin i, Y (c a) (c a') * Y (c a') (c a) + ∑ b ∈ G, Y (c a) b * Y b (c a) := by
      intro a
      rw [hG, sum_castLE_eq hi (fun b => Y (c a) b * Y b (c a))]
    have hn : ∀ x b : Fin N, ((‖Y x b‖ : ℂ)) ^ 2 = Y x b * Y b x := by
      intro x b
      rw [← hY.apply b x, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    apply Complex.ofReal_injective
    push_cast
    simp_rw [hdiag]
    rw [← sum_castLE_eq hi (fun a => Y a a),
      ← sum_castLE_eq hi (fun a => ∑ b ∈ G, (‖Y a b‖ : ℂ) ^ 2)]
    simp_rw [hn]
    simp only [← hD]
    rw [hcx, t0, t1, t2]
    simp_rw [hrow]
    rw [sum_add_distrib]
    ring
end Formalism.NuclearRankWeightBounds.P
