-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wirtingerIBP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:03.540857+00:00
-- url     : https://prove2.me/submissions/9757f705-4b45-473c-9726-386c2184c19e

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_wir_dir
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_wir_lin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution : WirtingerIBP := by
  intro d β t Ω g ht hΩ hg V _ _ _ b k hb hc hsupp
  obtain ⟨a1, a2, a3⟩ := wir_dir β t hΩ hg hb hc hsupp (Pi.single k 1)
  obtain ⟨c1, c2, c3⟩ := wir_dir β t hΩ hg hb hc hsupp (Pi.single k Complex.I)
  rw [muPi_eq, integral_smul_nnreal_measure, integral_smul_nnreal_measure, ← smul_neg]
  congr 1
  have e1 : ∀ x, psi β (g x / t) • wirt k b x =
      (1 / 2 : ℂ) • (psi β (g x / t) • fderiv ℝ b x (Pi.single k 1)) -
        (Complex.I / 2) • (psi β (g x / t) • fderiv ℝ b x (Pi.single k Complex.I)) := by
    intro x
    simp only [wirt, smul_sub, smul_smul]
    congr 2 <;> ring
  have hI : (Pi.single k Complex.I : Fin d → ℂ) = Complex.I • Pi.single k 1 := by
    rw [← Pi.single_smul]; simp
  have e2 : ∀ x, (Complex.I * β * fderiv ℂ g x (Pi.single k 1) / (2 * t) * psi β (g x / t)) • b x =
      (1 / 2 : ℂ) • ((psi β (g x / t) *
          (Complex.I * (((β / t * fderiv ℂ g x (Pi.single k 1)).re : ℝ) : ℂ))) • b x) -
        (Complex.I / 2) • ((psi β (g x / t) *
          (Complex.I * (((β / t * fderiv ℂ g x (Pi.single k Complex.I)).re : ℝ) : ℂ))) • b x) := by
    intro x
    rw [smul_smul, smul_smul, ← sub_smul]
    congr 1
    rw [hI, map_smul, smul_eq_mul]
    set w : ℂ := β / t * fderiv ℂ g x (Pi.single k 1) with hw
    have h1 : β / t * (Complex.I * fderiv ℂ g x (Pi.single k 1)) = Complex.I * w := by rw [hw]; ring
    have h2 : Complex.I * β * fderiv ℂ g x (Pi.single k 1) / (2 * t) = Complex.I * w / 2 := by
      rw [hw]; field_simp
    rw [h1, h2]
    have h3 : (Complex.I * w).re = -w.im := by simp
    rw [h3]
    conv_lhs => rw [← Complex.re_add_im w]
    push_cast
    ring
  simp_rw [e1, e2]
  rw [wir_lin _ _ _ _ a1 c1, wir_lin _ _ _ _ a2 c2, a3, c3]
  simp only [smul_neg]
  abel
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
