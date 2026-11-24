-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TheSec.theSecB_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:07:10.050547+00:00
-- url     : https://prove2.me/submissions/9cb7a70c-504e-4c41-b033-a95237b891b4

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSection
import Theorems.Thm_Formalism_FourierDecayAlt_P_TheSec_gA_spec
import Theorems.Thm_Formalism_FourierDecayAlt_P_TheSec_gB_spec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.TheSec
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction
variable (k : ℕ)
private theorem herm_mulVec_of_conjTranspose_mul_eq (H g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hg : gᴴ * H * g = H)
    (x y : Fin (k + 1) → ℂ) : herm H (g *ᵥ x) (g *ᵥ y) = herm H x y := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]
private theorem mul_conjTranspose_form_preserving (H A B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : Aᴴ * H * A = H)
    (hB : Bᴴ * H * B = H) : (A * B)ᴴ * H * (A * B) = H := by
  rw [Matrix.conjTranspose_mul]
  calc Bᴴ * Aᴴ * H * (A * B) = Bᴴ * (Aᴴ * H * A) * B := by simp only [Matrix.mul_assoc]
    _ = H := by rw [hA, hB]
private theorem nu_apply' (hk : 1 ≤ k) (w s : ℂ) (l m : Fin (k + 1)) :
    nu k w s l m =
      if m = 0 then (if l = 0 then star w else if l = Fin.last k then s else 0)
      else if m = Fin.last k then (if l = 0 then s else if l = Fin.last k then w else 0)
      else (if l = m then 1 else 0) := by
  have h0L : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at h'
    omega
  unfold nu
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.add_apply,
    Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hm0 : m = 0
  · subst hm0
    by_cases hl0 : l = 0
    · subst hl0
      simp [h0L]
    · by_cases hlL : l = Fin.last k
      · subst hlL
        simp [h0L, h0L.symm]
      · simp [hl0, hlL, h0L]
  · by_cases hmL : m = Fin.last k
    · subst hmL
      by_cases hl0 : l = 0
      · subst hl0
        simp [h0L, h0L.symm]
      · by_cases hlL : l = Fin.last k
        · subst hlL
          simp [h0L.symm]
        · simp [hl0, hlL, h0L.symm]
    · simp [hm0, hmL]
private theorem nu_conjTranspose_mul_Hb_mul_nu (hk : 1 ≤ k) (w s : ℂ) (hs : star s = s)
    (hws : star w * w - s * s = 1) : (nu k w s)ᴴ * Hb k * nu k w s = Hb k := by
  have h0L : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at h'
    omega
  ext i j
  rw [Matrix.mul_apply]
  simp only [Hb, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
    nu_apply' k hk]
  by_cases hi0 : i = 0
  · subst hi0
    rw [Fintype.sum_eq_add 0 (Fin.last k) h0L]
    · by_cases hj0 : j = 0
      · subst hj0
        simp only [h0L, h0L.symm, hs, star_star, eq_self_iff_true, if_true, if_false,
          ↓reduceIte, mul_one, one_mul, mul_neg, neg_mul]
        linear_combination hws
      · by_cases hjL : j = Fin.last k
        · subst hjL
          simp only [h0L, h0L.symm, hs, star_star, eq_self_iff_true, if_true, if_false,
            ↓reduceIte, mul_one, one_mul, mul_neg, neg_mul]
          ring
        · simp [h0L, h0L.symm, hj0, hjL, Ne.symm hj0, Ne.symm hjL]
    · intro x hx
      simp [hx.1, hx.2]
  · by_cases hiL : i = Fin.last k
    · subst hiL
      rw [Fintype.sum_eq_add 0 (Fin.last k) h0L]
      · by_cases hj0 : j = 0
        · subst hj0
          simp only [h0L, h0L.symm, hs, star_star, eq_self_iff_true, if_true, if_false,
            ↓reduceIte, mul_one, one_mul, mul_neg, neg_mul]
          ring
        · by_cases hjL : j = Fin.last k
          · subst hjL
            simp only [h0L, h0L.symm, hs, star_star, eq_self_iff_true, if_true, if_false,
              ↓reduceIte, mul_one, one_mul, mul_neg, neg_mul]
            linear_combination (-1 : ℂ) * hws
          · simp [h0L, h0L.symm, hj0, hjL, Ne.symm hj0, Ne.symm hjL]
      · intro x hx
        simp [hx.1, hx.2]
    · rw [Fintype.sum_eq_single i]
      · simp only [hi0, hiL, if_false, if_true, ↓reduceIte, eq_self_iff_true, star_one, one_mul]
        by_cases hj0 : j = 0
        · subst hj0
          simp [hi0, hiL]
        · by_cases hjL : j = Fin.last k
          · subst hjL
            simp [hi0, hiL]
          · by_cases hij : i = j
            · subst hij
              simp [hi0, hiL]
            · simp [hj0, hjL, hij, Ne.symm hij]
      · intro x hx
        simp [hi0, hiL, hx]
private theorem nu_mulVec_single_last (hk : 1 ≤ k) (w s : ℂ) :
    nu k w s *ᵥ Pi.single (Fin.last k) 1 = s • Pi.single 0 1 + w • Pi.single (Fin.last k) 1 := by
  have h0L : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at h'
    omega
  funext l
  have e : (nu k w s *ᵥ Pi.single (Fin.last k) 1) l = nu k w s l (Fin.last k) := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e, nu_apply' k hk]
  by_cases hl0 : l = 0
  · subst hl0
    simp [h0L.symm, h0L]
  · by_cases hlL : l = Fin.last k
    · subst hlL
      simp [h0L.symm]
    · simp [hl0, hlL, h0L.symm]
end Formalism.FourierDecayAlt.P.TheSec
end
end

set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TheSec
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction
variable (k : ℕ)
namespace Formalism.FourierDecayAlt.P.TheSec
theorem _root_.solution (hk : 1 ≤ k) (a b : Fin (k + 1) → ℂ) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T')
    (ha : herm (Hb k) a a = -(T : ℂ)) (hb : herm (Hb k) b b = -(T' : ℂ)) :
    (∀ i j, ContDiffOn ℝ ∞ (fun ζ => theSecB k a b T T' ζ i j) {ζ : ℂ | T * T' < Complex.normSq ζ}) ∧
      ∀ ζ : ℂ, T * T' < Complex.normSq ζ →
        (theSecB k a b T T' ζ)ᴴ * Hb k * theSecB k a b T T' ζ = Hb k ∧
          herm (Hb k) (theSecB k a b T T' ζ *ᵥ b) a = ζ := by
  have hTT : 0 < T * T' := mul_pos hT hT'
  let S : Set ℂ := {ζ : ℂ | T * T' < Complex.normSq ζ}
  have hw : ContDiff ℝ ∞ (fun ζ : ℂ => wZ T T' ζ) := by
    unfold wZ
    exact contDiff_const.mul contDiff_id
  have hws : ContDiff ℝ ∞ (fun ζ : ℂ => star (wZ T T' ζ)) := Complex.conjCLE.contDiff.comp hw
  have hsz : ContDiffOn ℝ ∞ (fun ζ : ℂ => sZ T T' ζ) S := by
    unfold sZ
    have hn2 : ContDiff ℝ ∞ (fun ζ : ℂ => Complex.normSq ζ) := by
      have e : (fun ζ : ℂ => Complex.normSq ζ) = fun ζ => ‖ζ‖ ^ 2 := by
        funext ζ
        exact Complex.normSq_eq_norm_sq ζ
      rw [e]
      exact contDiff_norm_sq ℝ
    have hn : ContDiff ℝ ∞ (fun ζ : ℂ => Complex.normSq ζ / (T * T') - 1) :=
      (hn2.div_const _).sub contDiff_const
    have hsq : ContDiffOn ℝ ∞ (fun ζ : ℂ => Real.sqrt (Complex.normSq ζ / (T * T') - 1)) S := by
      refine hn.contDiffOn.sqrt ?_
      intro ζ hζ
      have h1 : 1 < Complex.normSq ζ / (T * T') := by
        rw [lt_div_iff₀ hTT, one_mul]
        exact hζ
      linarith
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn hsq
  have hnu : ∀ y x, ContDiffOn ℝ ∞ (fun ζ => nu k (wZ T T' ζ) (sZ T T' ζ) y x) S := by
    intro y x
    simp only [nu_apply' k hk]
    split_ifs
    all_goals first
      | exact contDiffOn_const
      | exact hws.contDiffOn
      | exact hw.contDiffOn
      | exact hsz
  refine ⟨?_, ?_⟩
  · intro i j
    simp only [theSecB, Matrix.mul_apply]
    apply ContDiffOn.sum
    intro x _
    apply ContDiffOn.mul _ contDiffOn_const
    apply ContDiffOn.sum
    intro y _
    exact contDiffOn_const.mul (hnu y x)
  · intro ζ hζ
    have h0L : (0 : Fin (k + 1)) ≠ Fin.last k := by
      intro h
      have h' := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_last] at h'
      omega
    have hsr : star (sZ T T' ζ) = sZ T T' ζ := by
      unfold sZ
      exact Complex.conj_ofReal _
    have hkey : star (wZ T T' ζ) * wZ T T' ζ - sZ T T' ζ * sZ T T' ζ = 1 := by
      have hx : 0 ≤ Complex.normSq ζ / (T * T') - 1 := by
        have h1 : 1 < Complex.normSq ζ / (T * T') := by
          rw [lt_div_iff₀ hTT, one_mul]
          exact hζ
        linarith
      have h1 : Complex.normSq (wZ T T' ζ) = Complex.normSq ζ / (T * T') := by
        unfold wZ
        rw [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_inv, Complex.normSq_ofReal]
        rw [show Real.sqrt T * Real.sqrt T' * (Real.sqrt T * Real.sqrt T') =
            (Real.sqrt T * Real.sqrt T) * (Real.sqrt T' * Real.sqrt T') by ring,
          Real.mul_self_sqrt hT.le, Real.mul_self_sqrt hT'.le, div_eq_inv_mul]
      have h2 : star (wZ T T' ζ) * wZ T T' ζ = (Complex.normSq (wZ T T' ζ) : ℂ) :=
        Complex.normSq_eq_conj_mul_self.symm
      have h3 : sZ T T' ζ * sZ T T' ζ = ((Complex.normSq ζ / (T * T') - 1 : ℝ) : ℂ) := by
        unfold sZ
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx]
      rw [h2, h3, h1]
      push_cast
      ring
    have hA := gA_spec k hT ha
    have hB := gB_spec k hT' hb
    refine ⟨?_, ?_⟩
    · unfold theSecB
      exact mul_conjTranspose_form_preserving k _ _ _ (mul_conjTranspose_form_preserving k _ _ _ hA.1 (nu_conjTranspose_mul_Hb_mul_nu k hk _ _ hsr hkey)) hB.1
    · unfold theSecB
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hB.2]
      conv_lhs => arg 3; rw [← hA.2]
      rw [herm_mulVec_of_conjTranspose_mul_eq k _ _ hA.1, Matrix.mulVec_smul, nu_mulVec_single_last k hk]
      have hcs : star ((Real.sqrt T : ℝ) : ℂ) = ((Real.sqrt T : ℝ) : ℂ) := Complex.conj_ofReal _
      have hT0 : ((Real.sqrt T : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hT).ne'
      have hT0' : ((Real.sqrt T' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hT').ne'
      unfold herm Hb
      rw [dotProduct, Finset.sum_eq_single (Fin.last k)]
      · simp only [Matrix.mulVec_diagonal, Pi.star_apply, Pi.smul_apply, Pi.add_apply,
          Pi.single_eq_same, Pi.single_eq_of_ne h0L.symm, smul_eq_mul, mul_one, mul_zero,
          zero_add, star_mul', star_one, eq_self_iff_true, if_true, ↓reduceIte]
        rw [hcs]
        unfold wZ
        push_cast
        field_simp
      · intro i _ hi
        simp [Pi.single_apply, hi]
      · intro h
        exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.TheSec
