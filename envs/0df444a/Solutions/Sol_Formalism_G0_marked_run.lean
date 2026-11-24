-- Prove2me | solution 1 for Formalism.G0.marked_run
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:25.312536+00:00
-- url     : https://prove2.me/submissions/90f40868-3198-4659-bcd5-11328a906c05

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_MarkedRun
import Theorems.Thm_Formalism_G0_MarkedRunP_mem_cell_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open MarkedRunP
namespace Formalism.G0
theorem _root_.solution : MarkedRun := by
  intro T r u s hu hM
  have hex : ∀ i : Fin (3 * r), ∃ x, T ∩ cell r u s (2 * i.val + 1 + 1) = {x} ∧ Even x :=
    fun i => (hM (2 * i.val + 1 + 1) (by omega) (by have := i.2; omega)).2 ⟨i.val + 1, by ring⟩
  choose f hf hfe using hex
  have hmem : ∀ i : Fin (3 * r), f i ∈ T ∧
      s * ((6 * r + 1) * u) + (2 * i.val + 1) * u ≤ f i ∧
      f i < s * ((6 * r + 1) * u) + (2 * i.val + 1) * u + u := by
    intro i
    have h1 : f i ∈ T ∩ cell r u s (2 * i.val + 1 + 1) := by
      rw [hf i]
      exact Finset.mem_singleton_self _
    rw [Finset.mem_inter, MarkedRunP.mem_cell_succ] at h1
    exact ⟨h1.1, h1.2⟩
  have hgap : ∀ (i : Fin (3 * r)) (h : i.val + 1 < 3 * r), f i + u < f ⟨i.val + 1, h⟩ := by
    intro i h
    have a := (hmem i).2.2
    have b : s * ((6 * r + 1) * u) + (2 * (i.val + 1) + 1) * u ≤ f ⟨i.val + 1, h⟩ :=
      (hmem ⟨i.val + 1, h⟩).2.1
    nlinarith
  have hmono : StrictMono f := by
    intro i j hij
    have a := (hmem i).2.2
    have b := (hmem j).2.1
    have hij' : i.val + 1 ≤ j.val := hij
    have c := Nat.mul_le_mul_right u (show 2 * i.val + 2 ≤ 2 * j.val + 1 by omega)
    nlinarith
  have hbd : ∀ i : Fin (3 * r), s * ((6 * r + 1) * u) + u ≤ f i ∧
      f i + u < (s + 1) * ((6 * r + 1) * u) := by
    intro i
    have a := (hmem i).2.1
    have b := (hmem i).2.2
    have c := Nat.mul_le_mul_right u (show 2 * i.val + 3 ≤ 6 * r + 1 by have := i.2; omega)
    have d := Nat.zero_le (i.val * u)
    constructor <;> nlinarith
  refine ⟨f, hmono, ?_, hfe, hgap, hbd⟩
  ext y
  simp only [Finset.mem_inter, Finset.mem_Ico, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hyT, hy1, hy2⟩
    obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le hy1
    have hu' : 0 < u := hu
    have hq1 : w / u * u ≤ w := Nat.div_mul_le_self w u
    have hq2 : w < w / u * u + u := Nat.lt_div_mul_add hu'
    have hw : w < (6 * r + 1) * u := by nlinarith
    have hq : w / u < 6 * r + 1 := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt hq1 hw)
    generalize w / u = Q at hq1 hq2 hq
    have hc : s * ((6 * r + 1) * u) + w ∈ cell r u s (Q + 1) := by
      rw [MarkedRunP.mem_cell_succ]
      constructor
      · linarith
      · linarith
    rcases Nat.even_or_odd (Q + 1) with ⟨m, hm⟩ | ho
    · have hm1 : Q + 1 = 2 * (m - 1) + 1 + 1 := by omega
      have hi : m - 1 < 3 * r := by omega
      have hin : s * ((6 * r + 1) * u) + w ∈ T ∩ cell r u s (2 * (m - 1) + 1 + 1) := by
        rw [← hm1]
        exact Finset.mem_inter.2 ⟨hyT, hc⟩
      have := hf ⟨m - 1, hi⟩
      simp only at this
      rw [this, Finset.mem_singleton] at hin
      exact ⟨⟨m - 1, hi⟩, hin.symm⟩
    · have h0 := (hM (Q + 1) (by omega) (by omega)).1 ho
      have hin : s * ((6 * r + 1) * u) + w ∈ T ∩ cell r u s (Q + 1) :=
        Finset.mem_inter.2 ⟨hyT, hc⟩
      rw [h0] at hin
      exact absurd hin (Finset.notMem_empty _)
  · rintro ⟨i, rfl⟩
    have a := (hmem i).2.1
    have b := hbd i
    exact ⟨(hmem i).1, by nlinarith, by omega⟩
end Formalism.G0
