-- Prove2me | solution 1 for CachonFisherInventory.LowerBound.policy_cost_lower_bound
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T11:42:15.937693+00:00
-- url     : https://prove2.me/submissions/e0f759f7-0431-4f6f-8d8a-c8b48a5b4b92

import Definitions.Def_CachonFisherInventory_LowerBound_Criteria

open CachonFisherInventory.LowerBound

noncomputable def cfiParams : Parameters where
  N := 1
  N_pos := Nat.one_pos
  Qr := 1
  Qr_pos := Nat.one_pos
  Qs := 1
  Qs_pos := Nat.one_pos
  Lr := 0
  Ls := 0
  dbar := 1
  dbar_pos := Nat.one_pos
  law := PMF.pure ⟨1, by decide⟩
  unit_pos := by simp
  hs := 1
  hr := 0
  pr := 0
  hs_pos := zero_lt_one
  hr_nonneg := le_rfl
  pr_nonneg := le_rfl

private lemma baseCharge_eq_zero_of_one_le (y : ℤ) (hy : 1 ≤ y) :
    baseCharge cfiParams y = 0 := by
  unfold baseCharge
  refine Finset.sum_eq_zero fun d _ => ?_
  have hsum : (∑ k : Fin (cfiParams.Lr + 1), ((d k).val : ℝ)) ≤ 1 := by
    change (∑ k : Fin 1, ((d k).val : ℝ)) ≤ 1
    rw [Fin.sum_univ_one]
    have hd_nat : (d 0).val ≤ 1 := Nat.le_of_lt_succ (d 0).isLt
    exact_mod_cast hd_nat
  have hy' : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hle : (∑ k : Fin (cfiParams.Lr + 1), ((d k).val : ℝ)) - (y : ℝ) ≤ 0 := by linarith
  rw [max_eq_right hle]
  have hhr : cfiParams.hr = 0 := rfl
  rw [hhr]
  ring

theorem solution : ¬ (∀ (P : Parameters),
    ∃ R : ℤ, PrintedCriticalPoint P R ∧ ∀ s : Stock P,
      supplierLowerValue P (relaxedInitial P s) R +
        ((P.N * retailerLowerValue P R : ℝ) : EReal) ≤ physicalValue P s) := by
  intro h
  rcases h cfiParams with ⟨R, ⟨_, h_ub⟩, _⟩
  let r : ℤ := max (R + 1) 1
  have hr1 : 1 ≤ r := le_max_right (R + 1) 1
  have hr2 : 1 ≤ r + (cfiParams.Qr : ℤ) := by
    change 1 ≤ r + 1
    omega
  have hmem : r ∈ {r' : ℤ | baseCharge cfiParams (r' + cfiParams.Qr) ≤ baseCharge cfiParams r'} := by
    change baseCharge cfiParams (r + cfiParams.Qr) ≤ baseCharge cfiParams r
    rw [baseCharge_eq_zero_of_one_le r hr1, baseCharge_eq_zero_of_one_le (r + cfiParams.Qr) hr2]
  have hle : r ≤ R := h_ub hmem
  have hgt : R + 1 ≤ r := le_max_left (R + 1) 1
  omega
