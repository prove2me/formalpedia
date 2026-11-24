-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.form_add_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:06:33.023451+00:00
-- url     : https://prove2.me/submissions/c811525e-4761-44cd-b2e3-e59927720340

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pairAt_add_smul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (μ : Measure (Mt k r)) (i : Fin (r + 1)) (u y y' : Ix S → RadSp k r z z' π π')
    (c : Fin r → ℂ) (a : ℂ)
    (hin : ∀ (c' : Cf r i) (b : Ix S), Integrable (fun g : Mt k r =>
      B.hsInner ((u b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((y b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ)
    (hin' : ∀ (c' : Cf r i) (b : Ix S), Integrable (fun g : Mt k r =>
      B.hsInner ((u b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((y' b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ)
    (hout : Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ (u b) (y b) (glue i c c')))
    (hout' : Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ (u b) (y' b) (glue i c c'))) :
    form μ i u (y + a • y') c = form μ i u y c + conj a * form μ i u y' c := by
  unfold form
  have hpt : (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ (u b) ((y + a • y') b) (glue i c c')) =
      fun c' => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (u b) (y b) (glue i c c') +
        conj a * (((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (u b) (y' b) (glue i c c')) := by
    funext c'
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [Finset.sum_congr rfl fun b _ => pairAt_add_smul_right μ (u b) (y b) (y' b) _ a (hin c' b) (hin' c' b),
      Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hpt, integral_add hout (hout'.const_mul (conj a)), integral_const_mul]
end Formalism.FourierDecayAlt.P5
