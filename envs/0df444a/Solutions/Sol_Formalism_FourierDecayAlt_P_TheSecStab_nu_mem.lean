-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TheSecStab.nu_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:37:49.878175+00:00
-- url     : https://prove2.me/submissions/85094caa-3a8e-43b5-b1a3-297e25d90892

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSection
import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSectionStab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
noncomputable section
namespace Formalism.FourierDecayAlt.P.TheSecStab
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec
section block
variable {k : ℕ}
end block
section block2
variable {k : ℕ}
private theorem nu_apply_lemma (hk : 1 ≤ k) (w s : ℂ) (l m : Fin (k + 1)) :
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
private theorem nu_unit_lemma_5 (hk : 1 ≤ k) (w s : ℂ) (hs : star s = s)
    (hws : star w * w - s * s = 1) : (nu k w s)ᴴ * Hb k * nu k w s = Hb k := by
  have h0L : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at h'
    omega
  ext i j
  rw [Matrix.mul_apply]
  simp only [Hb, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
    nu_apply_lemma hk]
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
end block2
section full
variable {k r : ℕ}
end full
end Formalism.FourierDecayAlt.P.TheSecStab
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end

set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TheSecStab
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec
variable {k : ℕ}
namespace Formalism.FourierDecayAlt.P.TheSecStab
theorem _root_.solution (hk : 1 ≤ k) {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') {ζ : ℂ} (hζ : T * T' < Complex.normSq ζ) :
    nu k (wZ T T' ζ) (sZ T T' ζ) ∈ UH (Hb k) := by
  have hTT : 0 < T * T' := mul_pos hT hT'
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
  exact nu_unit_lemma_5 hk _ _ hsr hkey
end Formalism.FourierDecayAlt.P.TheSecStab
