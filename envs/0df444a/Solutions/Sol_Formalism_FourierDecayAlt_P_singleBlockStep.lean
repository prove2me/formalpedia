-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.singleBlockStep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:14.919162+00:00
-- url     : https://prove2.me/submissions/7fa9840d-a03e-4289-b786-247640dd1b60

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FormDomination
import Theorems.Thm_Formalism_FourierDecayAlt_P_FormDomination_prob_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_FormDomination_baseGram_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_FormDomination_sum_baseGram_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_FormDomination_mean_dom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.P.FormDomination
open Classical
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TB.OneStep := by
  intro E W _ D ep hG hK hW hA hWv hP hL T ε hε i hi1 hi w hw hcnt R hR M hM
  obtain ⟨θ, hθ, hest⟩ := hWv ε hε i hi1 hi w hw hcnt
  obtain ⟨⟨he0, he1⟩, -, -, hdom⟩ := hA i 1 le_rfl hi1 hi
  have hii : i - 1 + 1 = i := Nat.sub_add_cancel hi1
  rw [hii] at hdom
  have hY : ∀ h ∈ T.X (i - 1), level h = i - 1 := fun h hh => ((T.isTower _ _).1 hh).1
  have hep : 0 ≤ ep := by simpa using hL.1 i hi1 hi ∅ (by simp)
  have hd := hdom R hR (T.X (i - 1)) hY
  have hd' : PSDOn (T.X (i - 1)) (fun a b => (((1 + D.e i : ℝ)) : ℂ) * D.Kr (i - 1) a b -
      ∑ t ∈ R, D.Th i 1 t a b) := by
    push_cast; exact hd
  have h1e : 0 ≤ 1 + D.e i := by linarith

  set g : Finset (Fin D.f) → E → ℝ := fun A t₀ => ∑ w' ∈ D.Wb (D.cnt w + D.K),
    θ A w' * D.N0 ε (i - 1) w' (T.X (i - 1)) (D.Th i 1 t₀) with hg
  have hg0 : ∀ A t₀, 0 ≤ g A t₀ := fun A t₀ =>
    prob_nonneg _ _ _ (hθ A) fun w' _ => baseGram_nonneg D hG hW hε _ _ _ _ (hK.2 i 1 t₀ _)
  have hstep : ∀ t₀ ∈ R, ∑ t ∈ (T.Sg i 1).filter (fun t => t - t₀ ∈ D.La i 1),
      (D.Nst ε i 1 w (T.X (i - 1)) (D.Th i 1 t₀) t t).re ≤
        D.N0 ε (i - 1) w (T.X (i - 1)) (D.Th i 1 t₀) + ep * ∑ A, g A t₀ := by
    intro t₀ _
    have hpsd := hK.2 i 1 t₀ (T.X (i - 1))
    obtain ⟨h0, hl⟩ := hest (T.X (i - 1)) hY _ hpsd
    have hbound : ∀ L : Finset E, (∀ l ∈ L, l ∈ D.Lad i ∧ l ≠ 0) →
        ∑ l ∈ L, ‖D.Nhat ε i w (T.X (i - 1)) (D.Th i 1 t₀) l‖ ≤ ep * ∑ A, g A t₀ := by
      intro L hLm
      have hG0 : 0 ≤ ∑ A, g A t₀ := Finset.sum_nonneg fun A _ => hg0 A t₀
      have h1 : ∀ l ∈ L, ‖D.Nhat ε i w (T.X (i - 1)) (D.Th i 1 t₀) l‖ ≤
          max (D.maj (D.szD i) l) 0 * ∑ A, g A t₀ := by
        intro l hl'
        obtain ⟨A, hA'⟩ := hl l (hLm l hl').1 (hLm l hl').2
        calc ‖D.Nhat ε i w (T.X (i - 1)) (D.Th i 1 t₀) l‖ ≤ D.maj (D.szD i) l * g A t₀ := hA'
          _ ≤ max (D.maj (D.szD i) l) 0 * g A t₀ :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (hg0 A t₀)
          _ ≤ max (D.maj (D.szD i) l) 0 * ∑ A, g A t₀ :=
              mul_le_mul_of_nonneg_left
                (Finset.single_le_sum (f := fun A => g A t₀) (fun A _ => hg0 A t₀)
                  (Finset.mem_univ A)) (le_max_right _ _)
      have h2 : ∑ l ∈ L, max (D.maj (D.szD i) l) 0 ≤ ep := by
        have h3 := hL.1 i hi1 hi (L.filter fun l => 0 ≤ D.maj (D.szD i) l)
          (fun l hl' => hLm l (Finset.mem_filter.1 hl').1)
        rw [Finset.sum_filter] at h3
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun l _ => ?_)) h3
        split_ifs with hh
        · exact max_eq_left hh
        · exact max_eq_right (not_le.1 hh).le
      calc ∑ l ∈ L, ‖D.Nhat ε i w (T.X (i - 1)) (D.Th i 1 t₀) l‖
          ≤ ∑ l ∈ L, max (D.maj (D.szD i) l) 0 * ∑ A, g A t₀ := Finset.sum_le_sum h1
        _ = (∑ l ∈ L, max (D.maj (D.szD i) l) 0) * ∑ A, g A t₀ := by rw [Finset.sum_mul]
        _ ≤ ep * ∑ A, g A t₀ := mul_le_mul_of_nonneg_right h2 hG0
    have hp := hP ε hε i hi1 hi w (T.X (i - 1)) hY _ hpsd t₀ _ hbound
      ((T.Sg i 1).filter (fun t => t - t₀ ∈ D.La i 1)) (fun t ht => by
        rw [Finset.mem_filter] at ht
        exact ⟨fun h0 => T.zero_not_mem _ _ (h0 ▸ ht.1), ht.2⟩)
    rw [h0, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (baseGram_nonneg D hG hW hε _ _ _ _ hpsd)] at hp
    exact hp
  have hsumG : ∑ t₀ ∈ R, ∑ A, g A t₀ ≤ 2 ^ D.f * ((1 + D.e i) * M) := by
    rw [Finset.sum_comm]
    calc ∑ A : Finset (Fin D.f), ∑ t₀ ∈ R, g A t₀
        ≤ ∑ _A : Finset (Fin D.f), (1 + D.e i) * M :=
          Finset.sum_le_sum fun A _ =>
            mean_dom D hG hW hε (i - 1) _ (θ A) (hθ A) _ R (1 + D.e i) h1e _ _ hd' M hM
      _ = 2 ^ D.f * ((1 + D.e i) * M) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast; ring
  calc ∑ t₀ ∈ R, ∑ t ∈ (T.Sg i 1).filter (fun t => t - t₀ ∈ D.La i 1),
            (D.Nst ε i 1 w (T.X (i - 1)) (D.Th i 1 t₀) t t).re
      ≤ ∑ t₀ ∈ R, (D.N0 ε (i - 1) w (T.X (i - 1)) (D.Th i 1 t₀) + ep * ∑ A, g A t₀) :=
        Finset.sum_le_sum hstep
    _ = ∑ t₀ ∈ R, D.N0 ε (i - 1) w (T.X (i - 1)) (D.Th i 1 t₀) +
          ep * ∑ t₀ ∈ R, ∑ A, g A t₀ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (1 + D.e i) * D.N0 ε (i - 1) w (T.X (i - 1)) (D.Kr (i - 1)) +
          ep * (2 ^ D.f * ((1 + D.e i) * M)) :=
        add_le_add (sum_baseGram_le D hG hW hε (i - 1) w _ R (1 + D.e i) _ _ hd')
          (mul_le_mul_of_nonneg_left hsumG hep)
    _ = (1 + D.e i) * (D.N0 ε (i - 1) w (T.X (i - 1)) (D.Kr (i - 1)) + 2 ^ D.f * ep * M) := by
        ring
end Formalism.FourierDecayAlt.P
