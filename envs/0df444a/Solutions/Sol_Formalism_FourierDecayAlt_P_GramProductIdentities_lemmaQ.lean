-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GramProductIdentities.lemmaQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:31.844973+00:00
-- url     : https://prove2.me/submissions/80b9d771-1abe-435e-8e18-9b3f6db0c9fa

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_prod_bounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_qProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GramProductIdentities
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace Formalism.FourierDecayAlt.P.GramProductIdentities
theorem _root_.solution : LemmaQ := by
  intro S _ _ q w N dl Y hN hw hdl hpts hq
  have hN' : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hdlpos : 0 < dl := by nlinarith
  set g : Letter ℝ S → ℝ := fun l => if l.plus then 1 + 1 / (Y - l.pt) else 1 + 1 / (l.pt - Y - 1)
    with hg
  have hfac : ∀ l ∈ w, |g l - 1| ≤ 1 / dl := by
    intro l hl
    have h := hpts l hl
    cases hp : l.plus
    · simp only [hp, Bool.false_eq_true, if_false] at h
      simp only [hg, hp, Bool.false_eq_true, if_false, add_sub_cancel_left, abs_div, abs_one]
      have : |l.pt - Y - 1| = |Y - (l.pt - 1)| := by rw [← abs_neg]; ring_nf
      rw [this]
      exact one_div_le_one_div_of_le hdlpos h.2
    · simp only [hp, if_true] at h
      simp only [hg, hp, if_true, add_sub_cancel_left, abs_div, abs_one]
      exact one_div_le_one_div_of_le hdlpos h
  have hreg : ∀ l ∈ w, if l.plus then Y - l.pt ≠ 0 else l.pt - Y - 1 ≠ 0 := by
    intro l hl
    have h := hpts l hl
    cases hp : l.plus
    · simp only [hp, Bool.false_eq_true, if_false] at h ⊢
      intro h0
      have : |Y - (l.pt - 1)| = 0 := by rw [abs_eq_zero]; linarith
      linarith [h.2]
    · simp only [hp, if_true] at h ⊢
      intro h0
      rw [h0, abs_zero] at h
      linarith
  have hprod := qProduct S q w Y hq hreg
  have hε : 1 / dl ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  obtain ⟨hlo, hhi⟩ := prod_bounds g (1 / dl) hε w hfac
  have hlen : (w.length : ℝ) ≤ N := by exact_mod_cast hw
  have hkey : 1 / dl * w.length ≤ 1 / 4 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hdlpos]
    nlinarith
  rw [hprod]
  constructor
  · refine le_trans (Real.exp_le_exp.mpr ?_) hlo
    nlinarith
  · refine le_trans hhi (Real.exp_le_exp.mpr ?_)
    linarith
end Formalism.FourierDecayAlt.P.GramProductIdentities
