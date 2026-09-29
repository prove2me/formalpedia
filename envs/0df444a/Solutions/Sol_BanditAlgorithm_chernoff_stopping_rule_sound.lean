-- Prove2me | solution 1 for BanditAlgorithm.chernoff_stopping_rule_sound
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T19:13:14.038111+00:00
-- url     : https://prove2.me/submissions/4f45953a-a05b-486e-ac1f-37bcc80999ac

import Theorems.Thm_BanditAlgorithm_chernoff_stopping_rule_wellformed
import Theorems.Thm_BanditAlgorithm_chernoff_glr_never_favours_suboptimal_arm

/-!
# L&S Lemma 33.7

The lemma has three clauses.  The two structural ones — that `τ_δ` is a stopping
time and that `ψ_δ` is `𝓕_{τ_δ}`-measurable — are supplied by
`chernoff_stopping_rule_wellformed`, together with the extra pointwise
information that whenever the learner stops, it stops in a round `n` at which the
firing condition holds and at which the recommended arm attains the empirical
maximum.

Soundness is then a set inclusion.  On the event `{τ_δ < ∞ ∧ Δ_ψ(ν) > 0}` the
learner stopped in some round `n`; the firing condition holds at `n`, the
recommendation is an empirical maximiser at `n`, and it is suboptimal — which is
precisely membership in the event bounded by
`chernoff_glr_never_favours_suboptimal_arm`.  Monotonicity of the measure
finishes the proof.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem _root_.solution {k : ℕ} [NeZero k]
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (π : BanditAlgorithm.BanditPolicy k) :
    ∃ hτ : BanditAlgorithm.IsBanditStoppingTime
        (BanditAlgorithm.chernoffStoppingTime (k := k) δ),
      Measurable[hτ.measurableSpace] (BanditAlgorithm.chernoffRecommendation (k := k) δ) ∧
        BanditAlgorithm.IsSoundBAI δ π (BanditAlgorithm.chernoffStoppingTime (k := k) δ)
          (BanditAlgorithm.chernoffRecommendation (k := k) δ)
          (Set.range (BanditAlgorithm.gaussianBandit (k := k))) := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  obtain ⟨hτ, hψ, hstop⟩ :=
    BanditAlgorithm.chernoff_stopping_rule_wellformed (k := k) hk hδ.1
  refine ⟨hτ, hψ, fun ν hν ↦ ?_⟩
  refine le_trans (measure_mono ?_)
    (BanditAlgorithm.chernoff_glr_never_favours_suboptimal_arm δ hδ π ν hν)
  rintro ω ⟨hlt, hgap⟩
  obtain ⟨n, hfire, hmax⟩ := hstop ω hlt
  exact ⟨n, BanditAlgorithm.chernoffRecommendation (k := k) δ ω, hfire, hmax, hgap⟩
