-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.onExport_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:27.348574+00:00
-- url     : https://prove2.me/submissions/dbf03859-7616-4ddf-b2c5-6b8831f064a6

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OnExport
import Theorems.Thm_Formalism_DivisionValues_valuation_basic_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (hR : RamBasic) : OnExport := by
  classical
  intro K _ _ _ D hD Tup μ J _ d hd M T θ S e0 r0 ε0 F0 errl Jx vU0 gq dK EA Rb EJ δq E3 hδ h1 h2 hsh hv
    hdep htw hEA hRb hEJ hE3
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨hp, hr1, hpc, hrc, hell⟩ := hR K w
    have hρ : (1 : ℝ) ≤ (ramw w : ℝ) := by exact_mod_cast hr1
    obtain ⟨hv0, hvc, hvg⟩ := hv w hw
    have hl : (0 : ℝ) < (plc w : ℝ) ^ 2 := by
      have : (0 : ℝ) < (plc w : ℝ) := by exact_mod_cast hp.pos
      positivity
    have key : ∀ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
          (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ)) ≤
        (2 * ((ramw w : ℝ) * F0 w j) +
            (ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)))) * D +
          (ramw w : ℝ) * (ε0 w j + ε0 (conjPl w) j) := by
      intro j
      have a1 := h1 w hw j
      have a2 := h2 w hw j
      rw [hrc, hvc] at a2
      have hdj : (d j : ℝ) = D := by exact_mod_cast hd j
      rw [hdj] at a1 a2
      have a3 := hdep w hw j
      have a4 := hsh j
      have e1 : (r0 w j + dK j * vU0 w) / δq = r0 w j / δq + dK j / δq * vU0 w := by
        field_simp
      have e2 : (r0 (conjPl w) j + dK j * vU0 w) / δq = r0 (conjPl w) j / δq + dK j / δq * vU0 w := by
        field_simp
      have e3 : (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)) * D = r0 w j / δq + r0 (conjPl w) j / δq := by
        field_simp
      rw [e1] at a1
      rw [e2] at a2
      have b1 : dK j / δq * vU0 w ≤ 3 * (D : ℝ) * vU0 w := mul_le_mul_of_nonneg_right a4 hv0
      have b2 : (e0 w j + e0 (conjPl w) j + 8 * vU0 w) * (D : ℝ) ≤ (2 * F0 w j + errl w j) * D :=
        mul_le_mul_of_nonneg_right (by linarith) hDr.le
      have b3 : ((e0 w j + vU0 w) * (D : ℝ) + (r0 w j / δq + dK j / δq * vU0 w) + ε0 w j) +
          ((e0 (conjPl w) j + vU0 w) * (D : ℝ) + (r0 (conjPl w) j / δq + dK j / δq * vU0 w) +
            ε0 (conjPl w) j) ≤
          (2 * F0 w j + errl w j) * D + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)) * D +
            (ε0 w j + ε0 (conjPl w) j) := by
        rw [e3]; nlinarith
      have b4 := mul_le_mul_of_nonneg_left b3 (by linarith : (0 : ℝ) ≤ (ramw w : ℝ))
      calc _ ≤ _ := add_le_add a1 a2
        _ = (ramw w : ℝ) * (((e0 w j + vU0 w) * (D : ℝ) + (r0 w j / δq + dK j / δq * vU0 w) + ε0 w j) +
          ((e0 (conjPl w) j + vU0 w) * (D : ℝ) + (r0 (conjPl w) j / δq + dK j / δq * vU0 w) +
            ε0 (conjPl w) j)) := by ring
        _ ≤ _ := b4
        _ = _ := by ring
    calc _ ≤ _ := Finset.sum_le_sum (fun j _ => key j)
      _ = (∑ j, (2 * ((ramw w : ℝ) * F0 w j) +
            (ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ))))) * D +
          (ramw w : ℝ) * ∑ j, (ε0 w j + ε0 (conjPl w) j) := by
            rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      _ ≤ _ := by
        rw [hell, add_mul]
        have c1 := mul_le_mul_of_nonneg_left (htw w hw) (by linarith : (0 : ℝ) ≤ (ramw w : ℝ))
        have c2 : (ramw w : ℝ) * (1 / (plc w : ℝ) ^ 2) ≤ (ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2) * D := by
          have c3 : (0 : ℝ) ≤ (ramw w : ℝ) * (1 / (plc w : ℝ) ^ 2) := by positivity
          have c4 : (ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2) = 2 * ((ramw w : ℝ) * (1 / (plc w : ℝ) ^ 2)) := by
            ring
          rw [c4]; nlinarith
        linarith
  · intro j
    have hc : ∑ w ∈ S, lw w * ((ramw w : ℝ) * r0 (conjPl w) j) ≤ Rb j := by
      have hinj : Set.InjOn (conjPl (K := K)) S := by
        intro a _ b _ hab
        have := congrArg conjPl hab
        rwa [(valuation_basic_properties K a).2.2.2.1, (valuation_basic_properties K b).2.2.2.1] at this
      have := hRb j (S.image conjPl)
      rw [Finset.sum_image hinj] at this
      refine le_trans (le_of_eq ?_) this
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [(valuation_basic_properties K w).2.2.1, (hR K w).2.2.2.1]
    have hpos : (0 : ℝ) < δq * D := mul_pos hδ hDr
    have e : ∑ w ∈ S, lw w * ((ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ))) +
          Jx w j) =
        ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w j) +
          (∑ w ∈ S, lw w * ((ramw w : ℝ) * r0 w j) + ∑ w ∈ S, lw w * ((ramw w : ℝ) * r0 (conjPl w) j)) /
            (δq * (D : ℝ)) + ∑ w ∈ S, lw w * Jx w j := by
      rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      ring
    rw [e]
    have f1 : (∑ w ∈ S, lw w * ((ramw w : ℝ) * r0 w j) +
        ∑ w ∈ S, lw w * ((ramw w : ℝ) * r0 (conjPl w) j)) / (δq * (D : ℝ)) ≤ 2 * Rb j / (δq * (D : ℝ)) :=
      div_le_div_of_nonneg_right (by linarith [hRb j S]) hpos.le
    linarith [hEA j, hEJ j]
  · refine le_trans (le_of_eq ?_) hE3
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [(hR K w).2.2.2.2]
end Formalism.EigenvalueLevelCeiling
