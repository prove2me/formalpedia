-- Prove2me | solution 1 for Formalism.L2.Th1.F.OnePole.simple_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:24:59.726426+00:00
-- url     : https://prove2.me/submissions/73ce3009-23d5-470f-84c2-85d50ff49b5d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_AnalyticIdentityTheoremsZetaFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_OnePole

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.OnePole
open AnalyticIdentityTheoremsZetaFacts
namespace Formalism.L2.Th1.F.OnePole
theorem _root_.solution {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p) (ho : -1 ≤ meromorphicOrderAt f p) :
    ∃ (r : ℂ) (k : ℂ → ℂ), AnalyticAt ℂ k p ∧ ∀ᶠ w in 𝓝[≠] p, f w = r / (w - p) + k w := by
  cases h : meromorphicOrderAt f p with
  | top =>
    refine ⟨0, fun _ => 0, analyticAt_const, ?_⟩
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h] with w hw
    simp [hw]
  | coe n =>
    obtain ⟨g, hg, -, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 h
    have hn : (-1 : ℤ) ≤ n := by
      rw [h] at ho
      have h2 : ((-1 : ℤ) : WithTop ℤ) ≤ (n : WithTop ℤ) := by simpa using ho
      exact WithTop.coe_le_coe.1 h2
    rcases eq_or_lt_of_le hn with hn | hn
    · subst hn
      obtain ⟨q, hq⟩ := hg
      refine ⟨g p, dslope g p, ⟨_, hq.has_fpower_series_dslope_fslope⟩, ?_⟩
      filter_upwards [hfg, self_mem_nhdsWithin] with w hw hwp
      have hwp' : w ≠ p := hwp
      have hne : w - p ≠ 0 := sub_ne_zero.2 hwp'
      rw [hw, zpow_neg_one, smul_eq_mul, dslope_of_ne _ hwp', slope_def_field]
      field_simp
      ring
    · have hn0 : 0 ≤ n := by omega
      lift n to ℕ using hn0
      refine ⟨0, fun w => (w - p) ^ n * g w, by fun_prop, ?_⟩
      filter_upwards [hfg] with w hw
      rw [hw]
      simp [zpow_natCast, smul_eq_mul]
end Formalism.L2.Th1.F.OnePole
