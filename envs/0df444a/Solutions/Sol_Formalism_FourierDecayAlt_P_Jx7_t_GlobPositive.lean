-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.t_GlobPositive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:46.231803+00:00
-- url     : https://prove2.me/submissions/6a81728f-5ef2-4bf2-9439-5f5f2332fdbb

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution : GlobPositive := by
  intro CDel Cb hCDel hCb
  refine ⟨max 3 ⌈2 / Cb⌉₊, ?_⟩
  intro ι _ G bb hk hyp
  have hk3 : 3 ≤ G.k := le_trans (le_max_left _ _) hk
  have hkC : 2 / Cb ≤ (G.k : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hk)
  have hk3r : (3 : ℝ) ≤ G.k := by exact_mod_cast hk3
  have hk0 : (0 : ℝ) < G.k := by linarith
  have hbb := hyp.hbb
  have hbb0 : 0 < bb := by linarith
  have hpos : 0 < ((G.k : ℝ) * bb) ^ 8 := by positivity
  have hg1 : 0 < G.g1 := by
    have : (0 : ℝ) < G.g1 := lt_of_lt_of_le hpos hyp.hg1
    exact_mod_cast this
  have hg2 : 0 < G.g2 := by
    have : (0 : ℝ) < G.g2 := lt_of_lt_of_le hpos hyp.hg2
    exact_mod_cast this
  refine ⟨hg1, hg2, ?_⟩
  have hm2 : 2 ≤ G.m := by unfold Sz.Glob.m; omega
  have hf2 : 2 ≤ G.f := le_trans hm2 hyp.hmf
  have hne : Nonempty ι := by
    apply Fintype.card_pos_iff.1
    have : G.f = Fintype.card ι := rfl
    omega
  obtain ⟨w⟩ := hne
  have h1 : (G.k : ℝ) ^ Cb ≤ G.b w 1 := hyp.hnode w 1 le_rfl (by omega)
  have h2 : G.b w 1 ≤ bb ^ 2 := (hyp.hsmall w).hbj 1 le_rfl (by
    show 1 ≤ 2 * G.r + 2
    omega)
  have h3 : (G.k : ℝ) ^ Cb ≤ bb ^ 2 := le_trans h1 h2
  have h4 : Cb * Real.log G.k ≤ 2 * Real.log bb := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hk0 Cb) h3
    rw [Real.log_rpow hk0, Real.log_pow] at this
    exact_mod_cast this
  have hlogk : 1 ≤ Real.log G.k := by
    rw [Real.le_log_iff_exp_le hk0]
    have := Real.exp_one_lt_d9
    linarith
  have hlogbb : Cb / 2 ≤ Real.log bb := by nlinarith
  have hkCb : 2 ≤ (G.k : ℝ) * Cb := by
    rw [div_le_iff₀ hCb] at hkC
    exact hkC
  have hf2r : (2 : ℝ) ≤ G.f := by exact_mod_cast hf2
  have hbase : 2 ≤ (G.k : ℝ) * G.f * Real.log bb := by
    have e1 : (G.k : ℝ) * 2 * (Cb / 2) ≤ (G.k : ℝ) * G.f * Real.log bb := by
      apply mul_le_mul _ hlogbb (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hf2r hk0.le
    nlinarith
  have h16 : (16 : ℝ) ≤ ((G.k : ℝ) * G.f * Real.log bb) ^ CDel := by
    calc (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ CDel := Real.rpow_le_rpow_of_exponent_le (by norm_num) hCDel.le
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) hbase (by linarith)
  have hD : 16 ≤ G.Del := le_trans h16 hyp.hDel
  unfold Sz.Glob.lenI
  linarith
end Formalism.FourierDecayAlt.P.Jx7
