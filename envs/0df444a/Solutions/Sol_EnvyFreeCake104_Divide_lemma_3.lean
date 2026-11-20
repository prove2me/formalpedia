-- Prove2me | solution 1 for EnvyFreeCake104.Divide.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T06:47:39.401239+00:00
-- url     : https://prove2.me/submissions/fb6d2b42-ee28-45f2-897d-4ed1fbe607a9

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_lemma_6
import Theorems.Thm_EnvyFreeCake104_Divide_ordered_suffix_calculus__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
import Theorems.Thm_EnvyFreeCake104_Divide_core_equal_partition__p2m_285187a7_b6ea_4e38_bca1_5cfc5b97af68_a2
import Theorems.Thm_EnvyFreeCake104_Divide_permute_query_meter__p2m_285187a7_b6ea_4e38_bca1_5cfc5b97af68_a2

set_option autoImplicit false

open EnvyFreeCake104.Divide

private theorem value_mono__p2m_285187a7_b6ea_4e38_bca1_5cfc5b97af68_a2
    (v : Valuation) {S T : Set ℝ} (hST : S ⊆ T) :
    v.value S ≤ v.value T := by
  unfold Valuation.value
  apply MeasureTheory.setIntegral_mono_set
    (v.integrable.mono_set Set.inter_subset_right)
  · exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc v.nonneg)
  · exact Filter.Eventually.of_forall (fun x hx ↦ ⟨hST hx.1, hx.2⟩)

private theorem query_arithmetic__p2m_285187a7_b6ea_4e38_bca1_5cfc5b97af68_a2
    (n : ℕ) (hn : 2 ≤ n) :
    (n - 1) * (n + 1) + (n + 1) * (n.choose 2 * n.factorial ^ 2) ≤
      n ^ 3 * n.factorial ^ 2 := by
  have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hhalf : n.choose 2 * 2 ≤ n * (n - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.div_mul_le_self _ _
  have hchoose : n.choose 2 ≤ (n - 1) ^ 2 := by
    have hprod := congrArg (fun k : ℕ ↦ k * (n - 1)) hsub
    have hdd := Nat.mul_le_mul_left (n - 1) (show 1 ≤ n - 1 by omega)
    nlinarith
  have hid : (n - 1) * (n + 1) + (n + 1) * (n - 1) ^ 2 + n = n ^ 3 := by
    generalize hd : n - 1 = d at *
    have he : n = d + 1 := by omega
    rw [he]
    ring
  have hb : (n - 1) * (n + 1) + (n + 1) * n.choose 2 ≤ n ^ 3 := by
    have hm := Nat.mul_le_mul_left (n + 1) hchoose
    nlinarith
  have hF : 1 ≤ n.factorial ^ 2 := by
    have hf := Nat.factorial_pos n
    nlinarith
  calc
    (n - 1) * (n + 1) + (n + 1) * (n.choose 2 * n.factorial ^ 2) ≤
        ((n - 1) * (n + 1) + (n + 1) * n.choose 2) * n.factorial ^ 2 := by
      have hm := Nat.mul_le_mul_left ((n - 1) * (n + 1)) hF
      nlinarith
    _ ≤ n ^ 3 * n.factorial ^ 2 := Nat.mul_le_mul_right _ hb

theorem solution {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : 2 ≤ N.card) (c : ι) (hc : c ∈ N) (C : Piece) (hC : C.WF)
    (s : Rec ι) (hs : s.Valid V N) (hCs : s.Aligned C) (o : ChoiceOracle ι) :
    ∃ (Y : ι → Piece) (U : Piece) (s' : Rec ι) (tr : List (Event ι)),
      exec V o (core N c C) s = some ((Y, U), s', tr) ∧
      IsPartialAlloc N C.toSet (fun i ↦ (Y i).toSet) ∧
      U.toSet = residue N C.toSet (fun i ↦ (Y i).toSet) ∧
      EnvyFree V N (fun i ↦ (Y i).toSet) ∧
      (V c).value (Y c).toSet = (V c).value C.toSet / (N.card : ℝ) ∧
      queryCount tr ≤ N.card ^ 3 * (N.card.factorial) ^ 2 := by
  classical
  obtain ⟨P, s₁, o₁, hs₁, hP, hPs, hdisj, hcover, hequal, hcontinue⟩ :=
    core_equal_partition__p2m_285187a7_b6ea_4e38_bca1_5cfc5b97af68_a2 V N hN c hc C hC s hs hCs o
  obtain ⟨Y, U, s₂, tr₂, hrun₂, hEF, hres, hperm, hcuts⟩ :=
    lemma_6 V N ⟨c, hc⟩ P hP hdisj s₁ hs₁ hPs o₁
  obtain ⟨π, hπ, hsuffix, hwhole, _⟩ := hperm
  obtain ⟨istar, histar, hwhole⟩ := hwhole
  have hsub : ∀ i ∈ N, (Y i).toSet ⊆ (P (π i)).toSet := by
    intro i hi
    exact
      (ordered_suffix_calculus__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
        (P (π i)) (hP (π i) (hπ.1 hi))).2.1 _ (hsuffix i hi)
  have hPC : ∀ i ∈ N, (P i).toSet ⊆ C.toSet := by
    intro i hi x hx
    rw [← hcover]
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hx⟩⟩
  have halloc : IsPartialAlloc N C.toSet (fun i ↦ (Y i).toSet) := by
    constructor
    · intro i hi
      exact (hsub i hi).trans (hPC (π i) (hπ.1 hi))
    · intro i hi j hj hij
      have hpij : π i ≠ π j := fun e ↦ hij (hπ.2.1 hi hj e)
      exact (hdisj (π i) (hπ.1 hi) (π j) (hπ.1 hj) hpij).mono
        (hsub i hi) (hsub j hj)
  have hvalue : (V c).value (Y c).toSet = (V c).value C.toSet / (N.card : ℝ) := by
    apply le_antisymm
    · calc
        (V c).value (Y c).toSet ≤ (V c).value (P (π c)).toSet :=
          value_mono__p2m_285187a7_b6ea_4e38_bca1_5cfc5b97af68_a2 (V c) (hsub c hc)
        _ = _ := hequal (π c) (hπ.1 hc)
    · have he := hEF c hc istar histar
      change (V c).value (Y istar).toSet ≤ (V c).value (Y c).toSet at he
      rw [hwhole, hequal (π istar) (hπ.1 histar)] at he
      exact he
  obtain ⟨tr, hrun, htr⟩ := hcontinue Y U s₂ tr₂ hrun₂
  have hmeter := permute_query_meter__p2m_285187a7_b6ea_4e38_bca1_5cfc5b97af68_a2
    V N P s₁ o₁ Y U s₂ tr₂ hrun₂
  have hdelta : s₂.prefixCuts - s₁.prefixCuts ≤
      N.card.choose 2 * N.card.factorial ^ 2 := by omega
  have hqueries : queryCount tr ≤ N.card ^ 3 * N.card.factorial ^ 2 := by
    calc
      queryCount tr ≤ (N.card - 1) * (N.card + 1) + queryCount tr₂ := htr
      _ ≤ (N.card - 1) * (N.card + 1) +
          (N.card + 1) * (N.card.choose 2 * N.card.factorial ^ 2) := by
        exact Nat.add_le_add_left
          (hmeter.trans (Nat.mul_le_mul_left (N.card + 1) hdelta)) _
      _ ≤ _ := query_arithmetic__p2m_285187a7_b6ea_4e38_bca1_5cfc5b97af68_a2 N.card hN
  refine ⟨Y, U, s₂, tr, hrun, halloc, ?_, hEF, hvalue, hqueries⟩
  simpa only [residue, hcover] using hres

