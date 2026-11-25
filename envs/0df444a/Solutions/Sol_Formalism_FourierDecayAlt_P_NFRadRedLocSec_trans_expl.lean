-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedLocSec.trans_expl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:16:09.252936+00:00
-- url     : https://prove2.me/submissions/dbc161d9-1f52-4119-8313-3db2665cb6e8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedLocSec
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_add_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_qrefl_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_qrefl_mulVec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFRadRedLocSec
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)
variable {H}
namespace Formalism.FourierDecayAlt.P.NFRadRedLocSec
theorem _root_.solution (hH : Hᴴ = H) (a b : Fin m → ℂ) (q : ℝ) (hq : q ≠ 0)
    (ha : herm H a a = q) (hb : herm H b b = q) (θ : ℂ) (t : ℝ) (hθ : θ * star θ = 1)
    (ht : star θ * herm H a b = t) (hqt : q * t ≤ 0) :
    TwoByOneBlock.qrefl H b ((star θ - 1) / q) * TwoByOneBlock.qrefl H (a + (-θ) • b) (-1 / ((q : ℂ) - t)) ∈ UH H ∧
    (TwoByOneBlock.qrefl H b ((star θ - 1) / q) * TwoByOneBlock.qrefl H (a + (-θ) • b) (-1 / ((q : ℂ) - t))) *ᵥ a = b ∧
    ∀ x, herm H x a = 0 → herm H x b = 0 →
      (TwoByOneBlock.qrefl H b ((star θ - 1) / q) * TwoByOneBlock.qrefl H (a + (-θ) • b) (-1 / ((q : ℂ) - t))) *ᵥ x = x := by
  have hq' : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hq
  have hsq : star (q : ℂ) = q := Complex.conj_ofReal q
  have hst : star (t : ℂ) = t := Complex.conj_ofReal t
  have hqt' : (q : ℂ) - t ≠ 0 := by
    rw [← Complex.ofReal_sub]
    refine Complex.ofReal_ne_zero.2 fun h0 => hq ?_
    have e : t = q := by linarith
    rw [e] at hqt
    exact mul_self_eq_zero.1 (le_antisymm hqt (mul_self_nonneg q))
  have hba : herm H b a = star (herm H a b) := TwoByOneBlock.herm_symm H hH a b
  have ht' : θ * herm H b a = t := by
    have e := congrArg star ht
    rw [star_mul', star_star, hst] at e
    rw [hba]; exact e

  have mul_mem : ∀ g h : Matrix (Fin m) (Fin m) ℂ, g ∈ UH H → h ∈ UH H → g * h ∈ UH H := by
    intro g h hg hh
    have hg' : gᴴ * H * g = H := hg
    have hh' : hᴴ * H * h = H := hh
    show (g * h)ᴴ * H * (g * h) = H
    calc (g * h)ᴴ * H * (g * h) = hᴴ * (gᴴ * H * g) * h := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [hg', hh']
  have hc1 : (star θ - 1) / (q : ℂ) + star ((star θ - 1) / (q : ℂ)) +
      (star θ - 1) / (q : ℂ) * star ((star θ - 1) / (q : ℂ)) * herm H b b = 0 := by
    have hs1 : star ((star θ - 1) / (q : ℂ)) = (θ - 1) / q := by
      rw [star_div₀, star_sub, star_star, star_one, hsq]
    rw [hs1, hb]
    have e : (star θ - 1) / (q : ℂ) + (θ - 1) / q + (star θ - 1) / q * ((θ - 1) / q) * q =
        (θ * star θ - 1) / q := by
      field_simp
      ring
    rw [e, hθ, sub_self, zero_div]
  have hD : herm H (a + (-θ) • b) (a + (-θ) • b) = 2 * ((q : ℂ) - t) := by
    rw [TwoByOneBlock.herm_add_left, TwoByOneBlock.herm_add_right, TwoByOneBlock.herm_add_right, TwoByOneBlock.herm_smul_left,
      TwoByOneBlock.herm_smul_left, TwoByOneBlock.herm_smul_right, TwoByOneBlock.herm_smul_right, ha, hb, star_neg]
    linear_combination (-1 : ℂ) * ht + (-1 : ℂ) * ht' + (q : ℂ) * hθ
  have hc2 : -1 / ((q : ℂ) - t) + star (-1 / ((q : ℂ) - t)) +
      -1 / ((q : ℂ) - t) * star (-1 / ((q : ℂ) - t)) * herm H (a + (-θ) • b) (a + (-θ) • b) = 0 := by
    have hs2 : star (-1 / ((q : ℂ) - t)) = -1 / ((q : ℂ) - t) := by
      rw [star_div₀, star_neg, star_one, star_sub, hsq, hst]
    rw [hs2, hD]
    field_simp
    ring
  have hA : herm H a (a + (-θ) • b) = (q : ℂ) - t := by
    rw [TwoByOneBlock.herm_add_right, TwoByOneBlock.herm_smul_right, ha, ← ht, star_neg]
    ring
  have h2a : TwoByOneBlock.qrefl H (a + (-θ) • b) (-1 / ((q : ℂ) - t)) *ᵥ a = θ • b := by
    rw [TwoByOneBlock.qrefl_mulVec, hA, div_mul_cancel₀ _ hqt']
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h1b : TwoByOneBlock.qrefl H b ((star θ - 1) / q) *ᵥ (θ • b) = b := by
    rw [TwoByOneBlock.qrefl_mulVec, TwoByOneBlock.herm_smul_left, hb]
    have e : (star θ - 1) / (q : ℂ) * (θ * q) = 1 - θ := by
      rw [mul_comm θ, ← mul_assoc, div_mul_cancel₀ _ hq']
      linear_combination hθ
    rw [e]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨mul_mem _ _ (TwoByOneBlock.qrefl_mem H hH b _ hc1) (TwoByOneBlock.qrefl_mem H hH _ _ hc2), ?_, ?_⟩
  · rw [← Matrix.mulVec_mulVec, h2a, h1b]
  · intro x hxa hxb
    have hxd : herm H x (a + (-θ) • b) = 0 := by
      rw [TwoByOneBlock.herm_add_right, TwoByOneBlock.herm_smul_right, hxa, hxb]
      ring
    rw [← Matrix.mulVec_mulVec, TwoByOneBlock.qrefl_mulVec H (a + (-θ) • b) _ x, hxd, mul_zero, zero_smul, add_zero,
      TwoByOneBlock.qrefl_mulVec, hxb, mul_zero, zero_smul, add_zero]
end Formalism.FourierDecayAlt.P.NFRadRedLocSec
