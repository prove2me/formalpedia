-- Prove2me | solution 1 for Formalism.IncomingBounds.corFromThmA_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:43:16.110993+00:00
-- url     : https://prove2.me/submissions/0dceec07-4241-4679-9314-f89d1630c926

import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_BaseTermLeTopTerm
import Theorems.Thm_Formalism_IncomingBounds_cor_gam_nonneg
import Theorems.Thm_Formalism_IncomingBounds_cor_gam_le
import Theorems.Thm_Formalism_IncomingBounds_baseTerm_le_topTerm

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
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution (hF : FlowAttained) (hA : LemmaFa) (hc : LemmaFc) (hI : IncomingBound) :
    CorFromThmA := by
  refine ⟨15, ?_⟩
  intro l d inst hl hd hev TT nu1 nu2 size N0 N1 a k c CA vK w E h21 h12 hk hw hE hoff hon hcap hThm
  classical
  have hl3 : (3:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0:ℝ) < l := by linarith
  have hk3 : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hg := cor_gam_nonneg hl
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ s : ZMod d, w s := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg (fun s _ => (hw s).le)
  obtain ⟨Ws, hWs⟩ : ∃ f : ZMod d → ℝ, f = fun s => ((k:ℝ) - 1) * w s := ⟨_, rfl⟩
  obtain ⟨Dr, hDr⟩ : ∃ f : ZMod d → ℝ, f = fun s => (Dl d TT nu1 size s : ℝ) := ⟨_, rfl⟩
  obtain ⟨E', hE'⟩ : ∃ f : ZMod d → ℝ, f = fun s => if s ∈ TT then 2 * w s else 0 := ⟨_, rfl⟩
  have hWsapp : ∀ s, Ws s = ((k:ℝ) - 1) * w s := fun s => by rw [hWs]
  have hDr0 : 0 ≤ Dr := fun s => by show (0:ℝ) ≤ Dr s; rw [hDr]; exact Nat.cast_nonneg _
  have hE'0 : 0 ≤ E' := fun s => by
    show (0:ℝ) ≤ E' s
    rw [hE']
    try dsimp only
    split_ifs
    · linarith [hw s]
    · exact le_rfl
  have hDE : Dr + E' = Ws + E := by
    funext s
    simp only [Pi.add_apply, hDr, hE', hWs]
    by_cases hs : s ∈ TT
    · rw [if_pos hs, hon s hs]; ring
    · rw [if_neg hs, hoff s hs]; ring

  obtain ⟨⟨sD, hsD, -, hFsD⟩, -⟩ := hA l d hl hd hev Dr hDr0
  have h2 := (hc l d hl hd hev Dr E' sD hDr0 hE'0 ⟨hsD, hFsD⟩).2
  rw [hDE] at h2
  have hE'sum : ∑ s, E' s ≤ 2 * S := by
    rw [hS, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    rw [hE']
    dsimp only
    split_ifs <;> linarith [hw s]

  have hWs0 : 0 ≤ Ws := fun s => by
    show (0:ℝ) ≤ Ws s
    rw [hWsapp]
    have := hw s
    have : (0:ℝ) ≤ (k:ℝ) - 1 := by linarith
    positivity
  obtain ⟨⟨sW, hsW, -, hFsW⟩, -⟩ := hA l d hl hd hev Ws hWs0
  have hoptW : IsOptDual l d Ws sW := ⟨hsW, hFsW⟩
  have h3 := (hc l d hl hd hev Ws E sW hWs0 (fun s => (hE s).1) hoptW).1
  have hinc := hI l d hl hd hev Ws sW hWs0 hoptW
  have hfilt : ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), w s ≤ S / l := by
    have e1 : ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), Ws s =
        ((k:ℝ) - 1) * ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), w s := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => hWsapp s)
    have e2 : ∑ s, Ws s = ((k:ℝ) - 1) * S := by
      rw [hS, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => hWsapp s)
    rw [e1, e2, mul_div_assoc] at hinc
    have hk1 : 0 < (k:ℝ) - 1 := by linarith
    exact le_of_mul_le_mul_left hinc hk1
  have hpt : ∀ s, E s * max (sW s - gam l) 0 ≤
      8 * w s / l + 4 * (if 2 / (l:ℝ) ≤ sW s then w s else 0) := by
    intro s
    obtain ⟨hE0, hE4⟩ := hE s
    have hs0 := (hsW.1 s).1
    have hs1 := (hsW.1 s).2
    have hws := hw s
    have hm0 : 0 ≤ max (sW s - gam l) 0 := le_max_right _ _
    have hq : 0 ≤ 8 * w s / l := by positivity
    split_ifs with hcase
    · have hm : max (sW s - gam l) 0 ≤ 1 := max_le (by linarith) zero_le_one
      calc E s * max (sW s - gam l) 0 ≤ E s * 1 := mul_le_mul_of_nonneg_left hm hE0
        _ ≤ 4 * w s := by linarith
        _ ≤ _ := by linarith
    · push Not at hcase
      have hm : max (sW s - gam l) 0 ≤ 2 / l := max_le (by linarith) (by positivity)
      calc E s * max (sW s - gam l) 0 ≤ (4 * w s) * (2 / l) :=
            mul_le_mul hE4 hm hm0 (by linarith)
        _ = 8 * w s / l + 4 * 0 := by ring
  have hsum3 : ∑ s, E s * max (sW s - gam l) 0 ≤ 12 * S / l := by
    calc ∑ s, E s * max (sW s - gam l) 0
        ≤ ∑ s, (8 * w s / l + 4 * (if 2 / (l:ℝ) ≤ sW s then w s else 0)) :=
          Finset.sum_le_sum (fun s _ => hpt s)
      _ = 8 * S / l + 4 * ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), w s := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_filter, ← Finset.sum_div,
            ← Finset.mul_sum, ← hS]
      _ ≤ 8 * S / l + 4 * (S / l) := by linarith
      _ = 12 * S / l := by ring

  have hgE : gam l * ∑ s, E' s ≤ 9 / 4 * S / l := by
    have hl' : (l:ℝ) ≠ 0 := ne_of_gt hl0
    calc gam l * ∑ s, E' s ≤ gam l * (2 * S) := mul_le_mul_of_nonneg_left hE'sum hg
      _ ≤ 9 / (8 * l) * (2 * S) := mul_le_mul_of_nonneg_right (cor_gam_le hl) (by linarith)
      _ = 9 / 4 * S / l := by field_simp; ring

  have h1 : ∑ s ∈ TT, baseTerm l d TT nu1 nu2 s ≤ ∑ s ∈ TT, topTerm l d TT nu1 nu2 s :=
    Finset.sum_le_sum (fun s _ => baseTerm_le_topTerm l d hl TT nu1 nu2 s)

  unfold ThmABound at hThm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hDr] at hThm
  rw [← hS, ← hWs]
  have hfin : 12 * S / l + 9 / 4 * S / l ≤ 15 * S / l := by
    rw [← add_div, div_le_div_iff_of_pos_right hl0]
    linarith
  linarith
end Formalism.IncomingBounds
