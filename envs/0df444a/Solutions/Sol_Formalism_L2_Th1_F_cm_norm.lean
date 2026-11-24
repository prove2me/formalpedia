-- Prove2me | solution 1 for Formalism.L2.Th1.F.cm_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:26:14.539669+00:00
-- url     : https://prove2.me/submissions/478f64f5-92ab-4867-8a7e-af30c95dcedf

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_CMQuasiPeriodConst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm
import Theorems.Thm_Formalism_L2_Th1_F_Cm1_sqrt_mul_self
import Theorems.Thm_P2M_Formalism_L2_Th1_F_Cm1_sqrt_pos__6116e0f222b9
import Theorems.Thm_Formalism_L2_Th1_F_Cm1_coord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.F
namespace Cm1
private theorem cmTheta_eq_half_b_add_sqrt_half_I (b : ℤ) (d : ℕ) :
    Formalism.L2.Th1.F.cmTheta b d = (((b : ℝ) / 2 : ℝ) : ℂ) + ((Real.sqrt d / 2 : ℝ) : ℂ) * Complex.I := by
  unfold Formalism.L2.Th1.F.cmTheta; push_cast; ring
private theorem re_ofReal_add_ofReal_mul_I (u v : ℝ) : ((u : ℂ) + (v : ℂ) * Complex.I).re = u := by simp
private theorem im_ofReal_add_ofReal_mul_I (u v : ℝ) : ((u : ℂ) + (v : ℂ) * Complex.I).im = v := by simp
end Cm1
open Cm1
private theorem area_cmPair (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    area (cmPair a b d ha hd) = (a : ℝ) * Real.sqrt d / 2 := by
  have key : conj (a : ℂ) * cmTheta b d
      = (((a : ℝ) * b / 2 : ℝ) : ℂ) + (((a : ℝ) * Real.sqrt d / 2 : ℝ) : ℂ) * Complex.I := by
    rw [map_natCast, _root_.Formalism.L2.Th1.F.Cm1.cmTheta_eq_half_b_add_sqrt_half_I]; push_cast; ring
  unfold area
  show |(conj (a : ℂ) * cmTheta b d).im| = _
  rw [key, _root_.Formalism.L2.Th1.F.Cm1.im_ofReal_add_ofReal_mul_I]
  exact abs_of_nonneg (by positivity)
private theorem ofReal_add_mul_I_mul_conj (u v u' v' : ℝ) :
    ((u : ℂ) + (v : ℂ) * Complex.I) * conj ((u' : ℂ) + (v' : ℂ) * Complex.I)
      = ((u * u' + v * v' : ℝ) : ℂ) + ((v * u' - u * v' : ℝ) : ℂ) * Complex.I := by
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  linear_combination (-((v : ℂ) * (v' : ℂ))) * Complex.I_sq
private theorem ofReal_add_mul_I_div_ofReal (u v r : ℝ) :
    ((u : ℂ) + (v : ℂ) * Complex.I) / (r : ℂ) = ((u / r : ℝ) : ℂ) + ((v / r : ℝ) : ℂ) * Complex.I := by
  push_cast; ring
private theorem intCast_mul_add_mul_cmTheta_eq (a : ℕ) (b : ℤ) (d : ℕ) (m n : ℤ) :
    (m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d
      = (((m : ℝ) * a + n * b / 2 : ℝ) : ℂ) + (((n : ℝ) * Real.sqrt d / 2 : ℝ) : ℂ) * Complex.I := by
  rw [_root_.Formalism.L2.Th1.F.Cm1.cmTheta_eq_half_b_add_sqrt_half_I]; push_cast; ring
private theorem four_mul_a_mul_c_real_of_int (a : ℕ) (b c : ℤ) (d : ℕ) (h : 4 * (a : ℤ) * c = b ^ 2 + d) :
    (4 : ℝ) * (a : ℝ) * (c : ℝ) = (b : ℝ) ^ 2 + (d : ℝ) := by
  have h' := congrArg (fun t : ℤ => (t : ℝ)) h
  push_cast at h'
  linear_combination h'
private theorem normSq_coords_eq_a_mul_cmForm (a : ℕ) (b c : ℤ) (d : ℕ) (h : 4 * (a : ℤ) * c = b ^ 2 + d) (m n : ℤ) :
    ((m : ℝ) * a + n * b / 2) * ((m : ℝ) * a + n * b / 2)
      + ((n : ℝ) * Real.sqrt d / 2) * ((n : ℝ) * Real.sqrt d / 2)
      = (a : ℝ) * (cmForm a b c m n : ℝ) := by
  have hsd := Formalism.L2.Th1.F.Cm1.sqrt_mul_self d
  have hr := four_mul_a_mul_c_real_of_int a b c d h
  unfold cmForm
  push_cast
  linear_combination ((n : ℝ) ^ 2 / 4) * hsd - ((n : ℝ) ^ 2 / 4) * hr
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Cm1
namespace Formalism.L2.Th1.F
theorem _root_.solution : CmNorm := by
  intro a b c d ha hd h m n
  have hsd : Real.sqrt d ≠ 0 := (Formalism.L2.Th1.F.Cm1.sqrt_pos' d hd).ne'
  have hA : (a : ℝ) * Real.sqrt d / 2 ≠ 0 :=
    (div_pos (mul_pos (by exact_mod_cast ha) (Formalism.L2.Th1.F.Cm1.sqrt_pos' d hd)) two_pos).ne'
  have hN := normSq_coords_eq_a_mul_cmForm a b c d h m n
  have hnorm : Complex.normSq ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d)
      = (a : ℝ) * (cmForm a b c m n : ℝ) := by
    rw [intCast_mul_add_mul_cmTheta_eq, Complex.normSq_apply, _root_.Formalism.L2.Th1.F.Cm1.re_ofReal_add_ofReal_mul_I, _root_.Formalism.L2.Th1.F.Cm1.im_ofReal_add_ofReal_mul_I]; exact hN
  refine ⟨hnorm, ?_, ?_⟩
  · unfold herm
    rw [area_cmPair, intCast_mul_add_mul_cmTheta_eq, ofReal_add_mul_I_mul_conj, ofReal_add_mul_I_div_ofReal]
    apply Complex.ext
    · rw [_root_.Formalism.L2.Th1.F.Cm1.re_ofReal_add_ofReal_mul_I, Complex.ofReal_re, hN, div_eq_div_iff hA hsd]; ring
    · rw [_root_.Formalism.L2.Th1.F.Cm1.im_ofReal_add_ofReal_mul_I, Complex.ofReal_im]; ring
  · intro hmn
    have hz : (m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d ≠ 0 := by
      intro h0
      obtain ⟨h1, h2⟩ := Formalism.L2.Th1.F.Cm1.coord a b d ha hd (m : ℝ) (n : ℝ) (by exact_mod_cast h0)
      have hm : m = 0 := by exact_mod_cast h1
      have hn : n = 0 := by exact_mod_cast h2
      exact hmn (by rw [hm, hn])
    have hpos := Complex.normSq_pos.mpr hz
    rw [hnorm] at hpos
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hQ : (0 : ℝ) < (cmForm a b c m n : ℝ) := by
      by_contra hneg
      have hneg' := not_lt.mp hneg
      nlinarith
    have hQ' : (0 : ℤ) < cmForm a b c m n := by exact_mod_cast hQ
    omega
end Formalism.L2.Th1.F
