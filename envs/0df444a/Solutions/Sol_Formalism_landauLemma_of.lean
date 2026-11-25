-- Prove2me | solution 1 for Formalism.landauLemma_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:29:59.104443+00:00
-- url     : https://prove2.me/submissions/8608b5f0-1ed2-4317-aa18-b0487b2f77b5

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LandauLemma
import Theorems.Thm_Formalism_landauIteratedDerivatives_good_mono
import Theorems.Thm_Formalism_landauIteratedDerivatives_key

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
open landauIteratedDerivatives
namespace Formalism
theorem _root_.solution (hMD : MellinDeriv) : LandauLemma := by
  intro H a b hab hH hpos hb Φ hΦ1 hΦ2 hΦeq σ hσ
  by_contra hbad
  set T : Set ℝ := {τ | a < τ ∧ ¬ Good H τ} with hT
  have hσT : σ ∈ T := ⟨hσ, hbad⟩
  have hbdd : BddAbove T := ⟨b, fun τ hτ => by
    by_contra h
    exact hτ.2 (hb τ (lt_of_not_ge h))⟩
  set σc := sSup T with hσc
  have hσσc : σ ≤ σc := le_csSup hbdd hσT
  have hσcb : σc ≤ b := csSup_le ⟨σ, hσT⟩ (fun τ hτ => by
    by_contra h
    exact hτ.2 (hb τ (lt_of_not_ge h)))
  have hgood : ∀ τ, σc < τ → Good H τ := by
    intro τ hτ
    by_contra h
    have : τ ≤ σc := le_csSup hbdd ⟨by linarith, h⟩
    linarith
  have hJ0 : ∀ s : ℂ, b < s.re → Φ s = J H 0 s := by
    intro s hs
    rw [hΦeq s hs]
    unfold J
    congr 1
    funext x
    simp
  obtain ⟨σ', hσ'lt, hσ'⟩ := key hMD hH hpos hσcb hgood hΦ1
    (fun τ h1 h2 => hΦ2 τ (by linarith) h2) hJ0
  have : σc ≤ σ' := csSup_le ⟨σ, hσT⟩ (fun τ hτ => by
    by_contra h
    exact hτ.2 (good_mono hH hσ' (le_of_lt (lt_of_not_ge h))))
  linarith
end Formalism
