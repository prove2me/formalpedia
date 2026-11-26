-- Prove2me | solution 1 for ClassicalComplexWPT.summable_nnnorm_changeOriginSeries_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:59:04.626503+00:00
-- url     : https://prove2.me/submissions/cde95192-24b0-45f9-9dfc-f5628088d516

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
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
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (l : ℕ) :
    Summable (fun k : ℕ ↦ ‖p.changeOriginSeries k l‖₊ * r ^ k) := by
  rcases ENNReal.lt_iff_exists_add_pos_lt.1 hr with ⟨s, hs, hrs⟩
  have hsr : (s + r : ℝ≥0∞) < p.radius := by simpa [add_comm] using hrs
  let I := Σ k : ℕ, {t : Finset (Fin (k + l)) // t.card = l}
  let J := Σ k m : ℕ, {t : Finset (Fin (k + m)) // t.card = m}
  let e : I → J := fun q ↦ ⟨q.1, l, q.2⟩
  have he : Function.Injective e := by
    rintro ⟨k, t⟩ ⟨k', t'⟩ h
    dsimp only [e] at h
    cases h
    rfl
  have hbig : Summable (fun q : J ↦
      ‖p (q.1 + q.2.1)‖₊ * s ^ q.2.1 * r ^ q.1) :=
    p.changeOriginSeries_summable_aux₁ hsr
  have hfixedS : Summable (fun q : I ↦
      ‖p (q.1 + l)‖₊ * s ^ l * r ^ q.1) := by
    simpa [Function.comp_def, e] using NNReal.summable_comp_injective hbig he
  have hspow : s ^ l ≠ 0 := pow_ne_zero l hs.ne'
  have hfixed : Summable (fun q : I ↦ ‖p (q.1 + l)‖₊ * r ^ q.1) := by
    simpa [mul_assoc, mul_left_comm, mul_comm, hspow] using
      hfixedS.mul_right (s ^ l)⁻¹
  have houter : Summable (fun k : ℕ ↦
      ∑' t : {t : Finset (Fin (k + l)) // t.card = l},
        ‖p (k + l)‖₊ * r ^ k) :=
    (NNReal.summable_sigma.1 hfixed).2
  refine NNReal.summable_of_le (fun k ↦ ?_) houter
  calc
    ‖p.changeOriginSeries k l‖₊ * r ^ k ≤
        (∑' _ : {t : Finset (Fin (k + l)) // t.card = l}, ‖p (k + l)‖₊) * r ^ k := by
      gcongr
      exact p.nnnorm_changeOriginSeries_le_tsum k l
    _ = ∑' _ : {t : Finset (Fin (k + l)) // t.card = l},
        ‖p (k + l)‖₊ * r ^ k := by rw [NNReal.tsum_mul_right]
end ClassicalComplexWPT
