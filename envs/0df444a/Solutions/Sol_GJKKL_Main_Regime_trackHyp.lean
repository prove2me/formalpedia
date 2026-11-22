-- Prove2me | solution 1 for GJKKL.Main.Regime.trackHyp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:27:38.291013+00:00
-- url     : https://prove2.me/submissions/6a6b1ecf-3f30-4dcf-a147-f84f26159ba7

module
public import Definitions.Def_GJKKL_Main_Parameters
public import Definitions.Def_GJKKL_Main_TrackParams
public import Theorems.Thm_GJKKL_Main_cast_k_sub_two
public import Theorems.Thm_GJKKL_Main_Regime_x_ge
public import Theorems.Thm_GJKKL_Main_Regime_x_pos
public import Theorems.Thm_GJKKL_Main_Regime_x_le_one
public import Theorems.Thm_GJKKL_Main_Regime_dhat_pos
public import Theorems.Thm_GJKKL_Main_Regime_delta_nonneg
public import Theorems.Thm_GJKKL_Main_Regime_g_le_simple
public import Theorems.Thm_GJKKL_Main_Regime_r_le_simple
public import Theorems.Thm_GJKKL_Main_Regime_bnd_first_le
public import Theorems.Thm_GJKKL_Dv_nil
public import Theorems.Thm_GJKKL_History_aliveBefore_cons
public import Theorems.Thm_GJKKL_History_aliveBefore_nil
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_Main_Regime_E_le_delta
public import Theorems.Thm_GJKKL_Main_Regime_E_pos
public import Theorems.Thm_GJKKL_Main_Regime_a_mu_E_ge
public import Theorems.Thm_GJKKL_Main_Regime_a_mu_ge
public import Theorems.Thm_GJKKL_Main_Regime_d_div_a_le
public import Theorems.Thm_GJKKL_Main_Regime_d_pos
public import Theorems.Thm_GJKKL_Main_Regime_delta_le_half
public import Theorems.Thm_GJKKL_Main_Regime_delta_zero
public import Theorems.Thm_GJKKL_Main_Regime_dhat_le_d
public import Theorems.Thm_GJKKL_Main_Regime_dhat_zero
public import Theorems.Thm_GJKKL_Main_Regime_dneg_mul
public import Theorems.Thm_GJKKL_Main_Regime_init_bound
public import Theorems.Thm_GJKKL_Main_Regime_k_ge
public import Theorems.Thm_GJKKL_Main_Regime_k_le_sq
public import Theorems.Thm_GJKKL_Main_Regime_k_pos
public import Theorems.Thm_GJKKL_Main_Regime_mu_pos
public import Theorems.Thm_GJKKL_Main_Regime_n_pos
public import Theorems.Thm_GJKKL_Main_Regime_rp_pos
public import Theorems.Thm_GJKKL_Main_g_ge_aux
public import Theorems.Thm_GJKKL_Main_g_le_aux
public import Theorems.Thm_GJKKL_TrackHyp_k_pos
public import Theorems.Thm_GJKKL_Trajectory_inv_pow_sub_inv_pow_ge
public import Theorems.Thm_GJKKL_Trajectory_pfrac_sub_succ
public import Theorems.Thm_GJKKL_Trajectory_pfrac_succ_le
public import Theorems.Thm_GJKKL_bnd_def
public import Theorems.Thm_GJKKL_isGreedySeq_cons
public import Theorems.Thm_GJKKL_isGreedySeq_nil
public import Theorems.Thm_P2M_GJKKL_Main_Regime_d__le_E_f590cd77fc69
attribute [local simp] GJKKL.Dv_nil
attribute [local simp] GJKKL.History.aliveBefore_cons
attribute [local simp] GJKKL.History.aliveBefore_nil
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil
attribute [local simp] GJKKL.isGreedySeq_cons
attribute [local simp] GJKKL.isGreedySeq_nil



set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}
set_option maxHeartbeats 1600000
namespace GJKKL.Main.Regime
theorem _root_.solution (hunif : IsUniform H k)
    (hmin : ∀ v : V, (1 - d ^ (-ε)) * d ≤ (degree H v : ℝ))
    (hmax : ∀ v : V, (degree H v : ℝ) ≤ d)
    (hcod : ∀ u w : V, u ≠ w → (codegree H u w : ℝ) ≤ d ^ (1 - ε))
    (hn : ((k : ℝ) - 1) * d ^ ε / 2 ≤ Fintype.card V) {m : ℕ}
    (hm : (m : ℝ) ≤ (1 - d ^ (-(ε ^ 3))) * ((Fintype.card V : ℝ) / k)) :
    TrackHyp H k ⌊d ^ (1 - ε)⌋₊ (dhat k d ((Fintype.card V : ℝ) / k))
      (delta k ε d ((Fintype.card V : ℝ) / k)) m (Bn k : ℝ) (d ^ (1 - ε / 8) / 2)
      (100 * (k : ℝ) ^ 3 * d ^ (1 - ε)) (5 * k * d) := by
  have ha : 0 < (Fintype.card V : ℝ) / k := div_pos (R.n_pos hn) R.k_pos
  have hda := R.d_div_a_le hn
  have hamu := R.a_mu_ge hn
  have hamuE := R.a_mu_E_ge hn
  set a := (Fintype.card V : ℝ) / k with ha_def
  have haP : ∀ t, aPar V k t = a * pfrac a t := by
    intro t
    unfold aPar pfrac
    rw [ha_def]
    have hk0 : (k : ℝ) ≠ 0 := R.k_pos.ne'
    have hn0 : (Fintype.card V : ℝ) ≠ 0 := (R.n_pos hn).ne'
    first | (field_simp; ring) | field_simp
  have hk' : k - 1 = (k - 2) + 1 := by have := R.two_le; omega
  have hc : (k : ℝ) - 1 = ((k - 2 : ℕ) : ℝ) + 1 := by rw [cast_k_sub_two R.two_le]; ring
  have hK : 0 ≤ (k : ℝ) - 1 := by linarith [R.k_ge]
  have hcE : (⌊d ^ (1 - ε)⌋₊ : ℝ) ≤ d ^ (1 - ε / 8) :=
    (Nat.floor_le (R.rp_pos _).le).trans R.dε_le_E
  -- the variation bound summed
  have hsum : ∀ t < m, ∑ t' ∈ range (t + 1), bnd V k (dhat k d a) (delta k ε d a) t' ≤ 5 * k * d := by
    intro t ht
    have hterm : ∀ t' ∈ range (t + 1), bnd V k (dhat k d a) (delta k ε d a) t' ≤
        9 / 2 * ((k : ℝ) - 1) * (d / a) + ((dhat k d a t' - dhat k d a (t' + 1)) +
          (delta k ε d a (t' + 1) - delta k ε d a t')) := by
      intro t' ht'
      have ht'm : t' < m := by have := mem_range.mp ht'; omega
      rw [bnd_def, haP]
      have := R.bnd_first_le ha hm ht'm
      linarith
    refine (sum_le_sum hterm).trans ?_
    rw [sum_add_distrib, sum_add_distrib, sum_const, card_range, nsmul_eq_mul,
      sum_range_sub' (dhat k d a), sum_range_sub (delta k ε d a)]
    have htm : ((t + 1 : ℕ) : ℝ) ≤ a := by
      have : ((t + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.succ_le_of_lt ht
      have hμ := R.mu_pos
      nlinarith
    have h1 : ((t + 1 : ℕ) : ℝ) * (9 / 2 * ((k : ℝ) - 1) * (d / a)) ≤ 9 / 2 * ((k : ℝ) - 1) * d := by
      have : ((t + 1 : ℕ) : ℝ) * (d / a) ≤ d := by
        rw [mul_div_assoc', div_le_iff₀ ha]
        exact mul_le_mul_of_nonneg_right htm R.d_pos.le |>.trans_eq (mul_comm _ _)
      have := mul_le_mul_of_nonneg_left this (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 2) hK)
      nlinarith
    have hd0 : dhat k d a 0 = d := R.dhat_zero a
    have hdt := (R.dhat_pos ha hm (Nat.succ_le_of_lt ht)).le
    have hδt := R.delta_le_half (R.x_ge ha hm (Nat.succ_le_of_lt ht)) (R.x_le_one ha hm (t + 1))
    have hdtd := R.dhat_le_d (R.x_pos ha hm (Nat.succ_le_of_lt ht)).le (R.x_le_one ha hm (t + 1))
    have hδ0 := R.delta_nonneg ha hm (Nat.zero_le m)
    have hk := R.k_ge
    nlinarith [R.d_pos]
  refine
    { unif := hunif
      two_le := R.two_le
      codeg := fun u w h => Nat.le_floor (hcod u w h)
      dh_pos := fun t ht => R.dhat_pos ha hm ht.le
      δ_nonneg := fun t ht => R.delta_nonneg ha hm ht.le
      δ_le := fun t ht => R.delta_le_half (R.x_ge ha hm ht.le) (R.x_le_one ha hm t)
      aP_ge := ?_
      aP_ge_k := ?_
      g_nonneg := ?_
      g_le := ?_
      g_ge := ?_
      r_ge := ?_
      B_ge := ?_
      B_c := ?_
      B_n := ?_
      lam_pos := half_pos R.E_pos
      init := ?_
      C_pos := mul_pos (mul_pos (by norm_num) (pow_pos R.k_pos 3)) (R.rp_pos _)
      C_ge := ?_
      s_pos := mul_pos (mul_pos (by norm_num) R.k_pos) R.d_pos
      s_ge := hsum }
  · -- `16 ≤ aP`
    intro t ht
    rw [haP]
    have h1 : a * d ^ (-(ε ^ 3)) ≤ a * pfrac a t :=
      mul_le_mul_of_nonneg_left (R.x_ge ha hm ht.le) ha.le
    have := R.k_ge
    linarith
  · -- `k - 2 ≤ aP`
    intro t ht
    rw [haP]
    have h1 : a * d ^ (-(ε ^ 3)) ≤ a * pfrac a t :=
      mul_le_mul_of_nonneg_left (R.x_ge ha hm ht.le) ha.le
    have := R.k_ge
    linarith
  · -- `g ≥ 0`
    intro t ht
    unfold dhat
    have hy := R.x_pos ha hm (Nat.succ_le_of_lt ht)
    have := pow_le_pow_left₀ hy.le (pfrac_succ_le a ha.le t) (k - 1)
    have := mul_le_mul_of_nonneg_left this R.d_pos.le
    linarith
  · -- `g ≤ (k-1) dh / aP`
    intro t ht
    have hx := R.x_pos ha hm ht.le
    have hy := R.x_pos ha hm (Nat.succ_le_of_lt ht)
    have h := g_le_aux (k - 2) hy.le (pfrac_succ_le a ha.le t) hx ha R.d_pos.le
      (pfrac_sub_succ a t)
    rw [← hk', ← hc] at h
    rw [haP]
    unfold dhat
    exact h
  · -- `g ≥ (k-1) dh/aP - (k-1)(k-2) dh/aP²`
    intro t ht
    have hx := R.x_pos ha hm ht.le
    have hy := R.x_pos ha hm (Nat.succ_le_of_lt ht)
    have h := g_ge_aux (k - 2) hy.le (pfrac_succ_le a ha.le t) hx ha R.d_pos.le
      (pfrac_sub_succ a t)
    rw [← hk', ← hc, cast_k_sub_two R.two_le] at h
    rw [haP]
    unfold dhat
    exact h
  · -- `r ≥ B δ / aP`
    intro t ht
    have hx := R.x_pos ha hm ht.le
    have hy := R.x_pos ha hm (Nat.succ_le_of_lt ht)
    have h := inv_pow_sub_inv_pow_ge hy (pfrac_succ_le a ha.le t) (Bn k)
    rw [pfrac_sub_succ a t] at h
    have h2 := mul_le_mul_of_nonneg_left h R.E_pos.le
    rw [haP]
    unfold delta
    have hx0 : pfrac a t ≠ 0 := hx.ne'
    have ha0 : a ≠ 0 := ha.ne'
    have e1 : (Bn k : ℝ) * (d ^ (1 - ε / 8) / pfrac a t ^ Bn k) / (a * pfrac a t) =
        d ^ (1 - ε / 8) * ((Bn k : ℝ) * (1 / a) / pfrac a t ^ (Bn k + 1)) := by
      rw [pow_succ]
      first | (field_simp; ring) | field_simp
    have e2 : d ^ (1 - ε / 8) / pfrac a (t + 1) ^ Bn k - d ^ (1 - ε / 8) / pfrac a t ^ Bn k =
        d ^ (1 - ε / 8) * (1 / pfrac a (t + 1) ^ Bn k - 1 / pfrac a t ^ Bn k) := by ring
    rw [e1, e2]
    exact h2
  · -- `32(k-1) ≤ B`
    simp only [Bn]
    push_cast
    linarith [R.k_le_sq]
  · -- `8 κ c ≤ B δ`
    intro t ht
    have hκ : ((((k - 1) + (k - 1) * (k - 2) : ℕ)) : ℝ) ≤ (k : ℝ) ^ 2 := by
      have hk1 : 1 ≤ k := by have := R.two_le; omega
      push_cast [Nat.cast_sub hk1, Nat.cast_sub R.two_le]
      nlinarith [R.k_ge]
    have hδE := R.E_le_delta (R.x_pos ha hm ht.le) (R.x_le_one ha hm t)
    have hδ0 := R.delta_nonneg ha hm ht.le
    have hc0 : (0 : ℝ) ≤ ⌊d ^ (1 - ε)⌋₊ := Nat.cast_nonneg _
    have hcδ : (⌊d ^ (1 - ε)⌋₊ : ℝ) ≤ delta k ε d a t := hcE.trans hδE
    have hk2 : (0 : ℝ) ≤ (k : ℝ) ^ 2 := sq_nonneg _
    calc 8 * ((((k - 1) + (k - 1) * (k - 2) : ℕ)) : ℝ) * ⌊d ^ (1 - ε)⌋₊
        ≤ 8 * (k : ℝ) ^ 2 * ⌊d ^ (1 - ε)⌋₊ := by nlinarith
      _ ≤ 8 * (k : ℝ) ^ 2 * delta k ε d a t := mul_le_mul_of_nonneg_left hcδ (by nlinarith)
      _ ≤ (Bn k : ℝ) * delta k ε d a t := by
          simp only [Bn]; push_cast; nlinarith
  · -- `4(k-1)k dh ≤ B δ aP`
    intro t ht
    have hx := R.x_pos ha hm ht.le
    have hdh0 := (R.dhat_pos ha hm ht.le).le
    have hdhd := R.dhat_le_d hx.le (R.x_le_one ha hm t)
    have hδE := R.E_le_delta hx (R.x_le_one ha hm t)
    have hμx := R.x_ge ha hm ht.le
    rw [haP]
    have hk := R.k_ge
    -- `δ · aP ≥ E · aµ ≥ d`
    have h1 : a * d ^ (-(ε ^ 3)) * d ^ (1 - ε / 8) ≤ a * pfrac a t * delta k ε d a t := by
      have := mul_le_mul (mul_le_mul_of_nonneg_left hμx ha.le) hδE R.E_pos.le
        (mul_pos ha hx).le
      linarith
    have h2 : d ≤ a * pfrac a t * delta k ε d a t := hamuE.trans h1
    have h3 : 4 * ((k : ℝ) - 1) * (2 + ((k : ℝ) - 2)) * dhat k d a t ≤ 4 * (k : ℝ) ^ 2 * d := by
      have e : 4 * ((k : ℝ) - 1) * (2 + ((k : ℝ) - 2)) * dhat k d a t =
          4 * (((k : ℝ) - 1) * k) * dhat k d a t := by ring
      rw [e]
      have h4 : ((k : ℝ) - 1) * k ≤ (k : ℝ) ^ 2 := by nlinarith
      have h5 := mul_le_mul h4 hdhd hdh0 (sq_nonneg _)
      nlinarith
    have h6 : 4 * (k : ℝ) ^ 2 * d ≤ (Bn k : ℝ) * (delta k ε d a t * (a * pfrac a t)) := by
      simp only [Bn]
      push_cast
      have h7 : d ≤ delta k ε d a t * (a * pfrac a t) := by linarith
      have hk2 : (0 : ℝ) ≤ (k : ℝ) ^ 2 := sq_nonneg _
      nlinarith [R.d_pos]
    linarith
  · -- initial degrees
    intro v
    rw [R.dhat_zero, R.delta_zero]
    have h1 := hmin v
    have h2 := hmax v
    have h3 := R.dneg_mul
    have h4 := R.init_bound
    have hE := R.E_pos
    rw [abs_le]
    constructor <;> nlinarith
  · -- `kc + g + r ≤ C`
    intro t ht
    have hg := R.g_le_simple ha hm ht
    have hr := R.r_le_simple ha hm ht
    have hc1 : (⌊d ^ (1 - ε)⌋₊ : ℝ) ≤ d ^ (1 - ε) := Nat.floor_le (R.rp_pos _).le
    have hdε := (R.rp_pos (1 - ε)).le
    have hk := R.k_ge
    have hk3 : (k : ℝ) ≤ (k : ℝ) ^ 3 := by nlinarith [R.k_le_sq]
    have hk23 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by nlinarith [R.k_le_sq]
    have hda' : d / a ≤ 2 * k * d ^ (1 - ε) := hda
    have hBn : (Bn k : ℝ) = 32 * (k : ℝ) ^ 2 := by simp [Bn]
    rw [hBn] at hr
    have e1 : (k : ℝ) * ⌊d ^ (1 - ε)⌋₊ ≤ k * d ^ (1 - ε) :=
      mul_le_mul_of_nonneg_left hc1 (by linarith)
    have e2 : ((k : ℝ) - 1) * (d / a) ≤ ((k : ℝ) - 1) * (2 * k * d ^ (1 - ε)) :=
      mul_le_mul_of_nonneg_left hda' hK
    have e3 : 32 * (k : ℝ) ^ 2 * (d / a) / 2 ≤ 32 * (k : ℝ) ^ 2 * (2 * k * d ^ (1 - ε)) / 2 := by
      have := mul_le_mul_of_nonneg_left hda' (show (0 : ℝ) ≤ 32 * (k : ℝ) ^ 2 by nlinarith)
      linarith
    have e4 : (k : ℝ) * d ^ (1 - ε) + ((k : ℝ) - 1) * (2 * k * d ^ (1 - ε)) +
        32 * (k : ℝ) ^ 2 * (2 * k * d ^ (1 - ε)) / 2 ≤ 100 * (k : ℝ) ^ 3 * d ^ (1 - ε) := by
      have : (k : ℝ) + ((k : ℝ) - 1) * (2 * k) + 32 * (k : ℝ) ^ 2 * (2 * k) / 2 ≤
          100 * (k : ℝ) ^ 3 := by nlinarith
      nlinarith
    linarith
end GJKKL.Main.Regime
