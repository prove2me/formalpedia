-- Prove2me | solution 1 for CSeparatedNPComplete.partition_gadget_schedule_pointwise_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:56:27.534578+00:00
-- url     : https://prove2.me/submissions/8a5b0ff3-cdaa-4521-b86c-7f2db4aece14

module
public import Definitions.Def_CSeparatedNPComplete_CrossGadget
public import Definitions.Def_CSeparatedNPComplete_Gadget
public import Definitions.Def_CSeparatedNPComplete_Reciprocal
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Theorems.Thm_CSeparatedNPComplete_full_correction_eq_binary_iff
public import Theorems.Thm_CSeparatedNPComplete_full_correction_le_line
public import Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_hinge_form_prefix_m_ge_2
public import Theorems.Thm_CSeparatedNPComplete_hinge_form_nonneg
public import Theorems.Thm_CSeparatedNPComplete_is_binary_box_constraints
public import Theorems.Thm_CSeparatedNPComplete_perf_square_non_neg
public import Theorems.Thm_CSeparatedNPComplete_schedule_full_correction_eq_sum
public import Theorems.Thm_CSeparatedNPComplete_second_gadget_hinge_form_iff
public import Theorems.Thm_CSeparatedNPComplete_second_gadget_schedule_hinge_form_app


set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution
    (d : Nat) (a s : Vec d)
    (hd : 4 ≤ d) (hc : 1 ≤ dot s 1 / 2) (hs : perf_square_vec s) :
    (box_constraints a ∧ dot a 1 = (d : ℝ) / 2 ∧
      hinge_form (dot s 1 / 2) a (partition_gadget_schedule d s) ≤
        partition_schedule_threshold d s) ↔ is_ec_partition a s := by
  have hdreal : (4 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hm : (2 : ℝ) ≤ (d : ℝ) / 2 := by linarith
  have hs_nonneg := perf_square_non_neg hs
  have hn : 0 < d := by omega
  let c := dot s 1 / 2
  let C := c * (d : ℝ) * ((d : ℝ) + 1) / 2
  let G := hinge_form c a (second_gadget_instance ((d : ℝ) / 2) c s)
  let Corr := gaussian_schedule_hinge_correction a d
  have hdecomp (ha : box_constraints a) (hcard : dot a 1 = (d : ℝ) / 2) :
      hinge_form c a (partition_gadget_schedule d s) = G + (C - Corr) := by
    unfold partition_gadget_schedule second_gadget_partition_instance
    rw [second_gadget_schedule_hinge_form_app ((d : ℝ) / 2) c a s hm hc ha
      hs_nonneg hcard (by dsimp [c]; ring) hn]
    rw [gaussian_schedule_hinge_form_prefix_m_ge_2 d a hm hc ha.1 hcard]
  have hfull := schedule_full_correction_eq_sum a
  have hG_nonneg : 0 ≤ G := hinge_form_nonneg c a _
  constructor
  · rintro ⟨ha, hcard, hhinge⟩
    have hbound := full_correction_le_line a ha
    rw [hcard] at hbound
    rw [hdecomp ha hcard] at hhinge
    change G + (C - Corr) ≤ C - 3 * (d : ℝ) / 4 at hhinge
    have hzero : G = 0 := by dsimp [Corr] at hhinge; linarith
    have heq : (∑ i, (1 + a i)⁻¹) = (d : ℝ) - dot a 1 / 2 := by
      rw [hcard]
      dsimp [Corr] at hhinge
      linarith
    refine ⟨(full_correction_eq_binary_iff a ha).mp heq, hcard, ?_⟩
    exact (second_gadget_hinge_form_iff ((d : ℝ) / 2) c a s (by linarith) hc
      ha.1 hs_nonneg hcard).mp hzero
  · rintro ⟨hbin, hcard, hsum⟩
    have ha := is_binary_box_constraints hbin
    have heq := (full_correction_eq_binary_iff a ha).mpr hbin
    rw [hcard] at heq
    have hzero : G = 0 := (second_gadget_hinge_form_iff ((d : ℝ) / 2) c a s
      (by linarith) hc ha.1 hs_nonneg hcard).mpr hsum
    refine ⟨ha, hcard, ?_⟩
    rw [hdecomp ha hcard]
    change G + (C - Corr) ≤ C - 3 * (d : ℝ) / 4
    dsimp [Corr]
    linarith
end CSeparatedNPComplete
