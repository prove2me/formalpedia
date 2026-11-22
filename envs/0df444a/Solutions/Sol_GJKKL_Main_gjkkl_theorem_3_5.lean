-- Prove2me | solution 1 for GJKKL.Main.gjkkl_theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:31:11.481857+00:00
-- url     : https://prove2.me/submissions/920cd0cc-6690-4f67-84f2-06d1504b4b82

module
public import Definitions.Def_GJKKL_Main_TrackParams
public import Definitions.Def_GJKKL_Numerics_Final
public import Definitions.Def_GJKKL_Main_Theorem
public import Theorems.Thm_GJKKL_Main_aliveBefore_mono
public import Theorems.Thm_GJKKL_Main_le_rpow_of_root
public import Theorems.Thm_GJKKL_Main_empty_mem_matchingsOfSize
public import Theorems.Thm_GJKKL_Main_aPar_eq
public import Theorems.Thm_GJKKL_History_prob_mono
public import Theorems.Thm_GJKKL_History_prob_nonneg
public import Theorems.Thm_GJKKL_Main_Regime_a_mu_ge
public import Theorems.Thm_GJKKL_Main_Regime_card_ge
public import Theorems.Thm_GJKKL_Main_Regime_d_pos
public import Theorems.Thm_GJKKL_Main_Regime_delta_le_dhat
public import Theorems.Thm_GJKKL_Main_Regime_delta_le_half
public import Theorems.Thm_GJKKL_Main_Regime_dhat_pos
public import Theorems.Thm_GJKKL_Main_Regime_eta4_le_one
public import Theorems.Thm_GJKKL_Main_Regime_mu_le_eta4
public import Theorems.Thm_GJKKL_Main_Regime_mu_le_one
public import Theorems.Thm_GJKKL_Main_Regime_mu_lt_one
public import Theorems.Thm_GJKKL_Main_Regime_mu_pos
public import Theorems.Thm_GJKKL_Main_Regime_n_pos
public import Theorems.Thm_GJKKL_Main_Regime_trackHyp
public import Theorems.Thm_GJKKL_Main_Regime_union_small
public import Theorems.Thm_GJKKL_Main_Regime_x_ge
public import Theorems.Thm_GJKKL_Main_Regime_x_le_one
public import Theorems.Thm_GJKKL_Main_Regime_x_pos
public import Theorems.Thm_GJKKL_Numerics_final_bound
public import Theorems.Thm_GJKKL_TrackHyp_aliveBefore_good_manyAvail
public import Theorems.Thm_GJKKL_TrackHyp_prob_alive_good_ge
public import Theorems.Thm_GJKKL_card_matchingsOfSize_ge


set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory GJKKL.History GJKKL.Numerics
namespace GJKKL.Main
theorem _root_.solution : TargetStatement := by
  intro k hk
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have h64 : (0 : ℝ) < 64 * (k : ℝ) ^ 2 := mul_pos (by norm_num) (pow_pos hk0 2)
  refine ⟨1 / (64 * (k : ℝ) ^ 2), div_pos one_pos h64, fun ε hε0 hεlt => ?_⟩
  refine ⟨max (max 2 ((2 : ℝ) ^ (1 / (ε / 16)))) ((19200 * (k : ℝ) ^ 4) ^ (1 / (ε / 2))), ?_⟩
  intro d hd V _ _ H hunif hn hmin hmax hcod m hm
  have hd2 : 2 ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hd
  have R : Regime k ε d :=
    { two_le := hk
      ε_pos := hε0
      ε_small := by
        have h := (lt_div_iff₀ h64).mp hεlt
        linarith
      d_ge := hd2
      h16 := le_rpow_of_root (by norm_num) (by linarith)
        (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hd)
      h2 := le_rpow_of_root (by positivity) (by linarith) (le_trans (le_max_right _ _) hd) }
  -- the empty matching
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · subst hm0
    rw [pow_zero]
    exact Nat.one_le_cast.mpr (card_pos.mpr ⟨∅, empty_mem_matchingsOfSize H⟩)
  -- there is a vertex
  have hnpos : 0 < Fintype.card V := by
    by_contra h0
    have hc0 : Fintype.card V = 0 := by omega
    rw [hc0, Nat.cast_zero, mul_zero, zero_div] at hm
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp hnpos
  have hnge := R.card_ge hunif hmin hcod v
  have hm' : (m : ℝ) ≤ (1 - d ^ (-(ε ^ 3))) * ((Fintype.card V : ℝ) / k) := by
    rw [← mul_div_assoc]; exact hm
  have hyp := R.trackHyp hunif hmin hmax hcod hnge hm'
  have hamu := R.a_mu_ge hnge
  have hn0 : (Fintype.card V : ℝ) ≠ 0 := (R.n_pos hnge).ne'
  have haP := aPar_eq (V := V) hk0.ne' hn0
  have ha : 0 < (Fintype.card V : ℝ) / k := div_pos (R.n_pos hnge) hk0
  set a := (Fintype.card V : ℝ) / k with ha_def
  -- `m ≤ n`
  have hmn : m ≤ Fintype.card V := by
    have h1 : a ≤ Fintype.card V := div_le_self (Nat.cast_nonneg _) (by linarith)
    have h2 : (1 - d ^ (-(ε ^ 3))) * a ≤ a := by nlinarith [R.mu_pos]
    have : (m : ℝ) ≤ Fintype.card V := by linarith
    exact_mod_cast this
  -- the tracking event has probability at least `1/2`
  have hP := hyp.prob_alive_good_ge
  have hU := R.union_small hmn hn
  have hP2 : 1 / 2 ≤ prob (greedyKernel H) m (AliveBefore (GoodState H (dhat k d a)
      (delta k ε d a))) := by linarith
  -- the event `T*` for `g = gfun`
  have hg0 : ∀ i, 0 ≤ gfun V k ε d a m i := by
    intro i
    unfold gfun
    split_ifs with hi
    · rw [haP]
      have hx := R.x_pos ha hm' hi.le
      have hδ := R.delta_le_half (R.x_ge ha hm' hi.le) (R.x_le_one ha hm' i)
      have hdh := R.dhat_pos ha hm' hi.le
      exact mul_nonneg (mul_pos ha hx).le (by linarith)
    · exact le_rfl
  have hMany : ∀ h, AliveBefore (GoodState H (dhat k d a) (delta k ε d a)) h →
      ManyAvail H (gfun V k ε d a m) h := by
    intro h hal
    have := hyp.aliveBefore_good_manyAvail h hal
    unfold ManyAvail at this ⊢
    refine aliveBefore_mono (fun h' hh' => ?_) h this
    show gfun V k ε d a m h'.length ≤ ((avail H h').card : ℝ)
    unfold gfun
    split_ifs
    · exact hh'
    · exact Nat.cast_nonneg _
  have hPg : 1 / 2 ≤ prob (greedyKernel H) m (ManyAvail H (gfun V k ε d a m)) :=
    hP2.trans (prob_mono _ fun h _ hal => hMany h hal)
  have hne : ∀ e ∈ H, e.Nonempty := by
    intro e he
    rw [← card_pos, hunif e he]
    omega
  have hcount := card_matchingsOfSize_ge H hne (gfun V k ε d a m) hg0 m
  -- the product of the lower bounds
  have hμ0 := R.mu_pos
  have hμ1 := R.mu_le_one
  have hprod : ((1 - d ^ (-(ε ^ 3)) / 2) * d) ^ m * (a ^ m * (∏ i ∈ range m, (1 - (i : ℝ) / a)) ^ k) ≤
      ∏ i ∈ range m, gfun V k ε d a m i := by
    have e : ∏ i ∈ range m, ((1 - d ^ (-(ε ^ 3)) / 2) * d * (a * (1 - (i : ℝ) / a) ^ k)) =
        ((1 - d ^ (-(ε ^ 3)) / 2) * d) ^ m * (a ^ m * (∏ i ∈ range m, (1 - (i : ℝ) / a)) ^ k) := by
      rw [prod_mul_distrib, prod_const, card_range, prod_mul_distrib, prod_const, card_range,
        prod_pow]
    rw [← e]
    refine Finset.prod_le_prod (fun i hi => ?_) (fun i hi => ?_)
    · have hx := R.x_pos ha hm' (mem_range.mp hi).le
      have : 0 ≤ 1 - d ^ (-(ε ^ 3)) / 2 := by linarith
      exact mul_nonneg (mul_nonneg this R.d_pos.le) (mul_nonneg ha.le (pow_nonneg hx.le k))
    · have hi' := mem_range.mp hi
      unfold gfun
      rw [if_pos hi', haP]
      have hx := R.x_pos ha hm' hi'.le
      have hδ := R.delta_le_dhat (R.x_ge ha hm' hi'.le) (R.x_le_one ha hm' i)
      have hxk : pfrac a i * pfrac a i ^ (k - 1) = pfrac a i ^ k := by
        rw [← pow_succ']; congr 1; omega
      have hdh : dhat k d a i = d * pfrac a i ^ (k - 1) := rfl
      -- `dh - δ ≥ (1 - µ/2) dh`
      have h1 : (1 - d ^ (-(ε ^ 3)) / 2) * dhat k d a i ≤ dhat k d a i - delta k ε d a i := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (mul_pos ha hx).le
      have e2 : a * pfrac a i * ((1 - d ^ (-(ε ^ 3)) / 2) * dhat k d a i) =
          (1 - d ^ (-(ε ^ 3)) / 2) * d * (a * pfrac a i ^ k) := by
        rw [hdh, ← hxk]; ring
      show (1 - d ^ (-(ε ^ 3)) / 2) * d * (a * pfrac a i ^ k) ≤ a * pfrac a i * (dhat k d a i - delta k ε d a i)
      linarith
  -- the final arithmetic
  have hk1 : k - 1 + 1 = k := by omega
  have hfb := final_bound (a := a) (μ := d ^ (-(ε ^ 3))) (η := d ^ (-(ε ^ 3)) / 2) (η4 := d ^ (-(ε ^ 4))) (d := d)
    (P := prob (greedyKernel H) m (ManyAvail H (gfun V k ε d a m))) (k1 := k - 1) (m := m)
    ha hμ0 R.mu_lt_one (half_pos hμ0).le le_rfl
    ((show d ^ (-(ε ^ 3)) / 2 ≤ d ^ (-(ε ^ 3)) by linarith).trans R.mu_le_eta4) R.eta4_le_one R.d_pos.le hm1 hm'
    (by linarith) hPg
  rw [hk1] at hfb
  have hP0 : 0 ≤ prob (greedyKernel H) m (ManyAvail H (gfun V k ε d a m)) := prob_nonneg _ _ _
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  rw [hcast] at hfb
  calc ((1 - d ^ (-(ε ^ 4))) * d / Real.exp ((k : ℝ) - 1)) ^ m
      ≤ prob (greedyKernel H) m (ManyAvail H (gfun V k ε d a m)) * ((1 - d ^ (-(ε ^ 3)) / 2) * d) ^ m *
          (a ^ m * (∏ i ∈ range m, (1 - (i : ℝ) / a)) ^ k / m.factorial) := hfb
    _ = prob (greedyKernel H) m (ManyAvail H (gfun V k ε d a m)) *
          (((1 - d ^ (-(ε ^ 3)) / 2) * d) ^ m * (a ^ m * (∏ i ∈ range m, (1 - (i : ℝ) / a)) ^ k)) /
            m.factorial := by ring
    _ ≤ prob (greedyKernel H) m (ManyAvail H (gfun V k ε d a m)) *
          (∏ i ∈ range m, gfun V k ε d a m i) / m.factorial :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hP0) hfac.le
    _ ≤ (matchingsOfSize H m).card := hcount
end GJKKL.Main
