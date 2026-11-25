-- Prove2me | solution 1 for Formalism.landauEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:38:12.376451+00:00
-- url     : https://prove2.me/submissions/0f8bbbfc-dfcf-47d1-92b2-71a483015b9a

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_LandauLemma
import Definitions.Def_Formalism_ZetaNonvanishing_MellinDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_LandauEq
import Theorems.Thm_Formalism_LandauMellinIdentity_imel_differentiableOn
import Theorems.Thm_Formalism_landauLemma_of
import Theorems.Thm_Formalism_mellinDeriv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
open LandauMellinIdentity
namespace Formalism
theorem _root_.solution : LandauEq := by
  intro H a b hab hH hpos hb Φ hΦ1 hΦ2 hΦeq
  have hint : ∀ σ : ℝ, a < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1) :=
    landauLemma_of mellinDeriv H a b hab hH hpos hb Φ hΦ1 hΦ2 hΦeq
  intro σ hσ
  refine ⟨hint σ hσ, ?_⟩

  have hOpen : IsOpen {s : ℂ | a < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hIan : AnalyticOnNhd ℂ (Imel H) {s : ℂ | a < s.re} :=
    (imel_differentiableOn hH hpos hint).analyticOnNhd hOpen

  set A : Set ℂ := {s : ℂ | b < s.re} with hA
  set B : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Ioi a with hB
  have hb1A : ((b + 1 : ℝ) : ℂ) ∈ A := by simp [hA]
  have hb1B : ((b + 1 : ℝ) : ℂ) ∈ B := ⟨b + 1, by simp; linarith, rfl⟩
  have hAconv : Convex ℝ A := convex_halfSpace_re_gt b
  have hApc : IsPreconnected A := hAconv.isPreconnected
  have hBpc : IsPreconnected B :=
    (isPreconnected_Ioi).image _ Complex.continuous_ofReal.continuousOn
  have hTpc : IsPreconnected (A ∪ B) := IsPreconnected.union _ hb1A hb1B hApc hBpc
  have hTsub : A ∪ B ⊆ {s : ℂ | a < s.re} := by
    rintro s (hs | ⟨t, ht, rfl⟩)
    · show a < s.re
      have : b < s.re := hs
      linarith
    · show a < ((t : ℂ)).re
      simpa using ht
  have hΦan : AnalyticOnNhd ℂ Φ (A ∪ B) := by
    rintro s (hs | ⟨t, ht, rfl⟩)
    · exact hΦ1 s hs
    · by_cases htb : t ≤ b
      · exact hΦ2 t ht htb
      · exact hΦ1 _ (by simpa using lt_of_not_ge htb)
  have hev : Φ =ᶠ[𝓝 ((b + 1 : ℝ) : ℂ)] Imel H := by
    have hAo : IsOpen A := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hAo.mem_nhds hb1A] with s hs
    exact hΦeq s hs
  have heq := hΦan.eqOn_of_preconnected_of_eventuallyEq (hIan.mono hTsub) hTpc
    (Or.inl hb1A) hev
  exact heq (Or.inr ⟨σ, hσ, rfl⟩)
end Formalism
