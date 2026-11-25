-- Prove2me | solution 1 for Formalism.DivisionValues.young_diagram_step_origin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:18:59.41327+00:00
-- url     : https://prove2.me/submissions/4412acfb-cb9f-47a8-9538-6e91316cff70

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRowsShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramTopExact
import Theorems.Thm_Formalism_DivisionValues_young_diagram_step_shift
import Theorems.Thm_Formalism_DivisionValues_young_diagram_origin_off
import Theorems.Thm_Formalism_DivisionValues_young_diagram_origin_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : RowsStepEOrigin := by
  intro J Pl _ _ TT _ n t jj s aT bT w u v νr ar blk sm ν ap fa a rd La k N S Sc η m b' C1 C0
    hLa h1 hk hm hN hb' hS hC2 hSc hC0 hj1 hjm hs hsw hwA hBlA hBl0 haA hfa hν hap hνr har hblk
    hint hoff htop
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have hk0 : 0 ≤ k := by linarith
  have hkN : k ≤ N := by
    have : 0 ≤ m * ((t : ℝ) + 1) := mul_nonneg hm (by linarith)
    linarith
  have hj1' : ∀ j, (1 : ℝ) ≤ (jj j : ℝ) := fun j => by exact_mod_cast hj1 j
  have hsN : ∀ j, (s j : ℝ) ≤ 1 * N := fun j => by
    have e1 : (jj j : ℝ) * ((t : ℝ) + 1) ≤ m * ((t : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right (hjm j) (by linarith)
    rw [hs j]
    nlinarith
  have hshN : ∀ j, ((jj j : ℝ) - 1) * (t : ℝ) ≤ 1 * N := fun j => by
    have e1 : (jj j : ℝ) * (t : ℝ) ≤ m * (t : ℝ) := mul_le_mul_of_nonneg_right (hjm j) ht0
    nlinarith
  have hwr : ∀ j ρ, (w j ρ - s j) + s j = w j ρ := fun j ρ => Nat.sub_add_cancel (hsw j ρ)
  have hs' : ∀ j, (s j : ℝ) = (((n : ℝ) + 2) + (2 * (jj j : ℝ) - 1) * ((t : ℝ) + 1)) / 2 := fun j => by
    rw [hs j, hk]
  refine young_diagram_step_shift J Pl TT n aT w (fun j ρ => w j ρ - s j) ν ap fa a rd La k N S Sc t η
    m b' 1 C1 C0 hLa h1 hk hkN hb' zero_le_one hS hC2 (by linarith) hSc hC0
    (fun j ρ => Nat.sub_le _ _) ?_ hwA hBlA hBl0 haA hfa ?_ ?_
  · intro j ρ
    have : ((w j ρ - s j : ℕ) : ℝ) = (w j ρ : ℝ) - (s j : ℝ) := Nat.cast_sub (hsw j ρ)
    rw [this]
    linarith [hsN j]
  · intro j ρ hρ
    rw [hν j ρ, hap j ρ]
    exact young_diagram_origin_off n (jj j) t (w j ρ) (s j) (w j ρ - s j) m Sc _ _ (u ρ) (v ρ) (νr j ρ)
      (ar j ρ) (blk j ρ) (sm j ρ) (hj1 j) (hs' j) (hwr j ρ) (fun i => by rw [hνr j ρ i, hk])
      (fun i => by rw [har j ρ i, hk]) (hint ρ) (by rw [← hk]; exact (hoff ρ hρ).1)
      (by rw [← hk]; exact (hoff ρ hρ).2) (hshN j) (hblk j ρ)
  · intro j ρ hρ
    rw [hν j ρ, hap j ρ]
    obtain ⟨t1, t2, t3, t4⟩ := htop ρ hρ
    exact young_diagram_origin_top n (jj j) t (w j ρ) (s j) (w j ρ - s j) (aT ρ) (bT ρ) m Sc _ _ (u ρ) (v ρ)
      (νr j ρ) (ar j ρ) (blk j ρ) (sm j ρ) (hj1 j) (hs' j) (hwr j ρ) (fun i => by rw [hνr j ρ i, hk])
      (fun i => by rw [har j ρ i, hk]) (hint ρ) (by rw [← hk]; exact t1) (by rw [← hk]; exact t2)
      (by rw [← hk]; exact t3) (by rw [← hk]; exact t4) (hshN j) (hblk j ρ)
end Formalism.DivisionValues
