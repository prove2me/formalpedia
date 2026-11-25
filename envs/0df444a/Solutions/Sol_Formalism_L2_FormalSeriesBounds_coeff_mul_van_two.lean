-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_mul_van_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:22:32.559514+00:00
-- url     : https://prove2.me/submissions/498777cf-f05f-46da-b904-e9e3e04f62ce

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_exchangeTwo_self_eq_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_elementary_pair_apply_second
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_elementary_pair_eq_zero_of_ne
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_elementary_pair_support
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
theorem _root_.solution {T1 T2 : Set τ} {F G : MvPowerSeries τ C} (hF : Van T1 F) (hG : Van T2 G) {P Q : τ}
    (hPQ : P ≠ Q) (hQ : Q ∉ T1) (hP : P ∉ T2) :
    coeff (E2 P Q) (F * G) = coeff (Finsupp.single P 1) F * coeff (Finsupp.single Q 1) G := by
  rw [coeff_mul]
  rw [Finset.sum_eq_single ((Finsupp.single P 1, Finsupp.single Q 1) : (τ →₀ ℕ) × (τ →₀ ℕ))]
  · rintro ⟨a, b⟩ hab hne
    have hab' : a + b = E2 P Q := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
    have hs : ∀ s, a s + b s = E2 P Q s := fun s => by rw [← hab']; rfl
    by_cases ha : ∀ w ∈ a.support, w ∉ T1
    · rw [hF a ha, zero_mul]
    · by_cases hb : ∀ w ∈ b.support, w ∉ T2
      · rw [hG b hb, mul_zero]
      · exfalso
        push Not at ha hb
        obtain ⟨s, hs1, hsT⟩ := ha
        obtain ⟨s', hs1', hsT'⟩ := hb
        have h1 : a s ≠ 0 := Finsupp.mem_support_iff.1 hs1
        have h2 : b s' ≠ 0 := Finsupp.mem_support_iff.1 hs1'
        have hsP : s = P := by
          rcases elementary_pair_support (P := P) (Q := Q) (s := s) (by have := hs s; omega) with h | h
          · exact h
          · exact absurd (h ▸ hsT) hQ
        have hsQ : s' = Q := by
          rcases elementary_pair_support (P := P) (Q := Q) (s := s') (by have := hs s'; omega) with h | h
          · exact absurd (h ▸ hsT') hP
          · exact h
        subst hsP
        subst hsQ
        have hP1 := hs s
        have hQ1 := hs s'
        rw [exchangeTwo_self_eq_one hPQ] at hP1
        rw [elementary_pair_apply_second hPQ] at hQ1
        apply hne
        have ea : a = Finsupp.single s 1 := by
          ext x
          by_cases hx : x = s
          · subst hx; simp; omega
          · by_cases hx' : x = s'
            · subst hx'; rw [Finsupp.single_apply, if_neg (Ne.symm hx)]; omega
            · have := hs x
              rw [elementary_pair_eq_zero_of_ne hx hx'] at this
              rw [Finsupp.single_apply, if_neg (Ne.symm hx)]; omega
        have eb : b = Finsupp.single s' 1 := by
          ext x
          by_cases hx' : x = s'
          · subst hx'; simp; omega
          · by_cases hx : x = s
            · subst hx; rw [Finsupp.single_apply, if_neg (Ne.symm hx')]; omega
            · have := hs x
              rw [elementary_pair_eq_zero_of_ne hx hx'] at this
              rw [Finsupp.single_apply, if_neg (Ne.symm hx')]; omega
        rw [ea, eb]
  · intro h
    refine absurd ?_ h
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    unfold E2
    rfl
end Formalism.L2.FormalSeriesBounds
