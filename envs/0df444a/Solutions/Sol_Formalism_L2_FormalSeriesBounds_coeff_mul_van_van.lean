-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_mul_van_van
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:47:13.523577+00:00
-- url     : https://prove2.me/submissions/d26496ff-1219-4353-9a79-7f2647e6f226

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable {τ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {T : Set τ} {F G : MvPowerSeries τ C} (hF : Van T F) (hG : Van T G) (e : τ →₀ ℕ) (P : τ)
    (he : ∀ s ∈ T, e s ≠ 0 → s = P) (hP : e P ≤ 1) : coeff e (F * G) = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨a, b⟩ hab
  have hab' : a + b = e := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
  by_cases ha : ∀ w ∈ a.support, w ∉ T
  · rw [hF a ha, zero_mul]
  · by_cases hb : ∀ w ∈ b.support, w ∉ T
    · rw [hG b hb, mul_zero]
    · exfalso
      push Not at ha hb
      obtain ⟨s, hs, hsT⟩ := ha
      obtain ⟨s', hs', hsT'⟩ := hb
      have h1 : a s ≠ 0 := Finsupp.mem_support_iff.1 hs
      have h2 : b s' ≠ 0 := Finsupp.mem_support_iff.1 hs'
      have e1 : e s = a s + b s := by rw [← hab']; rfl
      have e2 : e s' = a s' + b s' := by rw [← hab']; rfl
      have hsP : s = P := he s hsT (by omega)
      have hsP' : s' = P := he s' hsT' (by omega)
      subst hsP
      subst hsP'
      omega
end Formalism.L2.FormalSeriesBounds
