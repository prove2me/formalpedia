-- Prove2me | solution 1 for ClassicalComplexWPT.summable_changeOrigin_weighted_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:00:06.859696+00:00
-- url     : https://prove2.me/submissions/3dedc253-3edc-427f-87b0-1fe76e269d3a

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Theorems.Thm_ClassicalComplexWPT_summable_nnnorm_changeOriginSeries_mul_pow
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero



set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (s r : ℝ≥0)
    (hsr : (s + r : ℝ≥0∞) < p.radius) :
    Summable (fun l : ℕ ↦
      (∑' k : ℕ, ‖p.changeOriginSeries k l‖₊ * r ^ k) * s ^ l) := by
  let J := Σ k m : ℕ, {t : Finset (Fin (k + m)) // t.card = m}
  let K := Σ m k : ℕ, {t : Finset (Fin (k + m)) // t.card = m}
  let e : K → J := fun q ↦ ⟨q.2.1, q.1, q.2.2⟩
  have he : Function.Injective e := by
    rintro ⟨m, k, t⟩ ⟨m', k', t'⟩ h
    dsimp only [e] at h
    cases h
    rfl
  have hbig : Summable (fun q : J ↦
      ‖p (q.1 + q.2.1)‖₊ * s ^ q.2.1 * r ^ q.1) :=
    p.changeOriginSeries_summable_aux₁ hsr
  have hswap : Summable (fun q : K ↦
      ‖p (q.2.1 + q.1)‖₊ * s ^ q.1 * r ^ q.2.1) := by
    simpa [Function.comp_def, e] using NNReal.summable_comp_injective hbig he
  have hr : (r : ℝ≥0∞) < p.radius := by
    exact (show (r : ℝ≥0∞) ≤ s + r by simp).trans_lt hsr
  have hK := NNReal.summable_sigma.1 hswap
  refine NNReal.summable_of_le (fun l ↦ ?_) hK.2
  have hKl := NNReal.summable_sigma.1 (hK.1 l)
  have hleft : Summable (fun k : ℕ ↦
      (‖p.changeOriginSeries k l‖₊ * r ^ k) * s ^ l) :=
    (summable_nnnorm_changeOriginSeries_mul_pow p r hr l).mul_right (s ^ l)
  calc
    (∑' k : ℕ, ‖p.changeOriginSeries k l‖₊ * r ^ k) * s ^ l =
        ∑' k : ℕ, (‖p.changeOriginSeries k l‖₊ * r ^ k) * s ^ l := by
      rw [NNReal.tsum_mul_right]
    _ ≤ ∑' k : ℕ, ∑' t : {t : Finset (Fin (k + l)) // t.card = l},
        ‖p (k + l)‖₊ * s ^ l * r ^ k := by
      apply Summable.tsum_le_tsum
      · intro k
        calc
          (‖p.changeOriginSeries k l‖₊ * r ^ k) * s ^ l ≤
              ((∑' _ : {t : Finset (Fin (k + l)) // t.card = l}, ‖p (k + l)‖₊) *
                r ^ k) * s ^ l := by
            gcongr
            exact p.nnnorm_changeOriginSeries_le_tsum k l
          _ = ∑' _ : {t : Finset (Fin (k + l)) // t.card = l},
              ‖p (k + l)‖₊ * s ^ l * r ^ k := by
            calc
              ((∑' _ : {t : Finset (Fin (k + l)) // t.card = l}, ‖p (k + l)‖₊) *
                  r ^ k) * s ^ l =
                  (∑' _ : {t : Finset (Fin (k + l)) // t.card = l},
                    ‖p (k + l)‖₊ * r ^ k) * s ^ l := by
                exact congrArg (fun x ↦ x * s ^ l)
                  (NNReal.tsum_mul_right
                    (fun _ : {t : Finset (Fin (k + l)) // t.card = l} ↦ ‖p (k + l)‖₊)
                    (r ^ k)).symm
              _ = ∑' _ : {t : Finset (Fin (k + l)) // t.card = l},
                    (‖p (k + l)‖₊ * r ^ k) * s ^ l := by
                exact (NNReal.tsum_mul_right
                  (fun _ : {t : Finset (Fin (k + l)) // t.card = l} ↦
                    ‖p (k + l)‖₊ * r ^ k) (s ^ l)).symm
              _ = ∑' _ : {t : Finset (Fin (k + l)) // t.card = l},
                    ‖p (k + l)‖₊ * s ^ l * r ^ k := by
                apply tsum_congr
                intro t
                ac_rfl
      · exact hleft
      · exact hKl.2
    _ = ∑' q : Σ k : ℕ, {t : Finset (Fin (k + l)) // t.card = l},
        ‖p (q.1 + l)‖₊ * s ^ l * r ^ q.1 := by
      exact (Summable.tsum_sigma'
        (f := fun q : Σ k : ℕ, {t : Finset (Fin (k + l)) // t.card = l} ↦
          ‖p (q.1 + l)‖₊ * s ^ l * r ^ q.1) hKl.1 (hK.1 l)).symm
end ClassicalComplexWPT
