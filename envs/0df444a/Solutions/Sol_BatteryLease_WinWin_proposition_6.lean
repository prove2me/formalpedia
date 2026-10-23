-- Prove2me | solution 1 for BatteryLease.WinWin.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T17:03:56.742694+00:00
-- url     : https://prove2.me/submissions/eda77ed9-1276-48a0-9875-de82df689103

import Mathlib
import Definitions.Def_BatteryLease_WinWin_Setting
import Theorems.Thm_BatteryLease_WinWin_lemma_2

set_option autoImplicit false
open MeasureTheory BatteryLease.WinWin

namespace BL6

lemma int_split {f : ℝ → ℝ} (hf : Continuous f) (x y z : ℝ) :
    ∫ D in x..z, f D = (∫ D in x..y, f D) + ∫ D in y..z, f D :=
  (intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
    (hf.intervalIntegrable _ _)).symm

lemma int_lin (x y m k : ℝ) : ∫ D in x..y, (m * D + k) = m * (y ^ 2 - x ^ 2) / 2 + k * (y - x) := by
  have h1 : ∫ D in x..y, (m * D + k) = (∫ D in x..y, m * D) + ∫ _ in x..y, k :=
    intervalIntegral.integral_add ((continuous_const.mul continuous_id).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)
  rw [h1, intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const,
    smul_eq_mul]
  ring

lemma int_congr_lin {f : ℝ → ℝ} (x y m k : ℝ) (hxy : x ≤ y)
    (h : ∀ D, x ≤ D → D ≤ y → f D = m * D + k) :
    ∫ D in x..y, f D = m * (y ^ 2 - x ^ 2) / 2 + k * (y - x) := by
  rw [← int_lin]
  apply intervalIntegral.integral_congr
  intro D hD
  rw [Set.uIcc_of_le hxy] at hD
  exact h D hD.1 hD.2

lemma custVol_le (P : ℝ → Prop) (X : ℝ) (h : ∀ d ∈ Set.Icc (0:ℝ) 1, P d ↔ d ≤ X) :
    custVol P = max 0 (min X 1) := by
  unfold custVol
  have hs : {d : ℝ | d ∈ Set.Icc (0:ℝ) 1 ∧ P d} = Set.Icc 0 (min X 1) := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨⟨h0, h1⟩, hP⟩
      exact ⟨h0, le_min ((h d ⟨h0, h1⟩).1 hP) h1⟩
    · rintro ⟨h0, hm⟩
      have h1 : d ≤ 1 := le_trans hm (min_le_right _ _)
      exact ⟨⟨h0, h1⟩, (h d ⟨h0, h1⟩).2 (le_trans hm (min_le_left _ _))⟩
  rw [hs, Real.volume_Icc, ENNReal.toReal_ofReal', sub_zero, max_comm]

lemma custVol_nonneg (P : ℝ → Prop) : 0 ≤ custVol P := ENNReal.toReal_nonneg

lemma custVol_le_one (P : ℝ → Prop) : custVol P ≤ 1 := by
  unfold custVol
  have h : volume {d : ℝ | d ∈ Set.Icc (0:ℝ) 1 ∧ P d} ≤ volume (Set.Icc (0:ℝ) 1) :=
    measure_mono (fun d hd => hd.1)
  rw [Real.volume_Icc] at h
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa using this

lemma int_pos (a rh : ℝ) (h0 : 0 ≤ rh) (h1 : rh ≤ a) :
    ∫ D in (0:ℝ)..a, pos (D - rh) = (a - rh) ^ 2 / 2 := by
  have hc : Continuous (fun D : ℝ => pos (D - rh)) := by unfold pos; fun_prop
  rw [int_split hc 0 rh a, int_congr_lin 0 rh 0 0 h0, int_congr_lin rh a 1 (-rh) h1]
  · ring
  · intro D hD _; simp only [pos]; rw [max_eq_left (by linarith)]; ring
  · intro D _ hD; simp only [pos]; rw [max_eq_right (by linarith)]; ring

lemma int_min (X : ℝ) (h0 : 0 ≤ X) (h1 : X ≤ 1) :
    ∫ d in (0:ℝ)..1, min d X = X - X ^ 2 / 2 := by
  have hc : Continuous (fun d : ℝ => min d X) := by fun_prop
  rw [int_split hc 0 X 1, int_congr_lin 0 X 1 0 h0, int_congr_lin X 1 0 X h1]
  · ring
  · intro D hD _; rw [min_eq_right hD]; ring
  · intro D _ hD; rw [min_eq_left hD]; ring

lemma EU_id (a : ℝ) (ha : 0 < a) : EU a (fun D => D) = a / 2 := by
  unfold EU; rw [integral_id]; field_simp; ring

lemma ECl_eq (a rh q : ℝ) (ha : 0 < a) (hq0 : 0 ≤ q) (hqr : q ≤ rh) (hra : rh ≤ a) :
    ECl a rh q = (a * q - q ^ 2 / 2 + (a - rh) ^ 2 / 2) / a := by
  unfold ECl EU
  congr 1
  have hc : Continuous (fun D : ℝ => min D (pos (D - rh) + q)) := by unfold pos; fun_prop
  rw [int_split hc 0 rh a, int_split hc 0 q rh, int_congr_lin 0 q 1 0 hq0,
    int_congr_lin q rh 0 q hqr, int_congr_lin rh a 1 (q - rh) hra]
  · ring
  · intro D hD _; simp only [pos]; rw [max_eq_left (by linarith), min_eq_right (by linarith)]; ring
  · intro D hD hD2; simp only [pos]; rw [max_eq_right (by linarith), min_eq_right (by linarith)]; ring
  · intro D hD hD2; simp only [pos]; rw [max_eq_right (by linarith), min_eq_left (by linarith)]; ring

lemma ECh_eq (a rh ph r : ℝ) (ha : 0 < a) (hs0 : 0 ≤ ph - r) (hsr : ph - r ≤ rh) (hra : rh ≤ a) :
    ECh a rh ph r = (a * ph - (ph - r) ^ 2 / 2 + (a - rh) ^ 2 / 2) / a := by
  unfold ECh EU
  congr 1
  have hc : Continuous (fun D : ℝ => min (pos (D - rh) + ph) (D + r)) := by unfold pos; fun_prop
  rw [int_split hc 0 rh a, int_split hc 0 (ph - r) rh, int_congr_lin 0 (ph - r) 1 r hs0,
    int_congr_lin (ph - r) rh 0 ph hsr, int_congr_lin rh a 1 (ph - rh) hra]
  · ring
  · intro D hD _; simp only [pos]; rw [max_eq_left (by linarith), min_eq_left (by linarith)]; ring
  · intro D hD hD2; simp only [pos]; rw [max_eq_right (by linarith), min_eq_left (by linarith)]; ring
  · intro D hD hD2; simp only [pos]; rw [max_eq_right (by linarith), min_eq_right (by linarith)]; ring

lemma ECl_le (a rh q : ℝ) (ha : 0 < a) : ECl a rh q ≤ a / 2 := by
  unfold ECl
  rw [← EU_id a ha]
  unfold EU
  apply div_le_div_of_nonneg_right _ ha.le
  apply intervalIntegral.integral_mono_on ha.le
  · exact (by unfold pos; fun_prop : Continuous (fun D : ℝ => min D (pos (D - rh) + q))).intervalIntegrable _ _
  · exact continuous_id.intervalIntegrable _ _
  · intro x _; exact min_le_left _ _


/-! ## Benchmark -/

noncomputable def Kb (a ρ rh : ℝ) : ℝ := (1 - ρ) * rh * (2 * a - rh) / (2 * a)
noncomputable def xb (a ρ rh ch : ℝ) : ℝ := (ρ - Kb a ρ rh + ch) / (2 * ρ)

lemma EU_pos (a rh : ℝ) (ha : 0 < a) (h0 : 0 ≤ rh) (h1 : rh ≤ a) :
    EU a (fun D => pos (D - rh)) = (a - rh) ^ 2 / (2 * a) := by
  unfold EU; rw [int_pos a rh h0 h1]; field_simp

lemma pos_small (d rh : ℝ) (hd : d ≤ 1) (hr : 1 ≤ rh) : pos (d - rh) = 0 := by
  unfold pos; exact max_eq_right (by linarith)

lemma benchLow_iff (a ρ rh ph d : ℝ) (ha : 0 < a) (hρ : 0 < ρ) (hr1 : 1 ≤ rh) (hra : rh ≤ a)
    (hd : d ∈ Set.Icc (0:ℝ) 1) : benchLow a ρ rh ph d ↔ d ≤ (ph - Kb a ρ rh) / ρ := by
  unfold benchLow
  rw [EU_id a ha, EU_pos a rh ha (by linarith) hra, pos_small d rh hd.2 hr1, le_div_iff₀ hρ]
  have : (1 - ρ) * (a / 2) = (1 - ρ) * ((a - rh) ^ 2 / (2 * a)) + Kb a ρ rh := by
    unfold Kb; field_simp; ring
  constructor <;> intro h <;> nlinarith

lemma tauB_eq (a ρ rh ph : ℝ) (ha : 0 < a) (hρ : 0 < ρ) (hr1 : 1 ≤ rh) (hra : rh ≤ a) :
    tauB a ρ rh ph = max 0 (min ((ph - Kb a ρ rh) / ρ) 1) :=
  custVol_le _ _ (fun d hd => benchLow_iff a ρ rh ph d ha hρ hr1 hra hd)

lemma benchCC_eq (a ρ rh ph : ℝ) (ha : 0 < a) (hρ : 0 < ρ) (hr1 : 1 ≤ rh) (hra : rh ≤ a)
    (hx0 : 0 ≤ (ph - Kb a ρ rh) / ρ) (hx1 : (ph - Kb a ρ rh) / ρ ≤ 1) :
    benchCC a ρ rh ph = (1 - ρ) * (a / 2) +
      ρ * ((ph - Kb a ρ rh) / ρ - ((ph - Kb a ρ rh) / ρ) ^ 2 / 2) := by
  set x := (ph - Kb a ρ rh) / ρ with hx
  have hK : (1 - ρ) * (a / 2) = (1 - ρ) * ((a - rh) ^ 2 / (2 * a)) + Kb a ρ rh := by
    unfold Kb; field_simp; ring
  have hph : ph = Kb a ρ rh + ρ * x := by rw [hx]; field_simp; ring
  unfold benchCC
  rw [EU_id a ha, EU_pos a rh ha (by linarith) hra]
  have e : ∫ d in (0:ℝ)..1, min (ρ * d + (1 - ρ) * (a / 2))
      (ph + ρ * pos (d - rh) + (1 - ρ) * ((a - rh) ^ 2 / (2 * a))) =
      ∫ d in (0:ℝ)..1, ((1 - ρ) * (a / 2) + ρ * min d x) := by
    apply intervalIntegral.integral_congr
    intro d hd
    rw [Set.uIcc_of_le zero_le_one] at hd
    simp only
    rw [pos_small d rh hd.2 hr1]
    rcases le_total d x with h | h
    · rw [min_eq_left (by nlinarith), min_eq_left h]; ring
    · rw [min_eq_right (by nlinarith), min_eq_right h]; linarith
  have e2 : ∫ d in (0:ℝ)..1, ((1 - ρ) * (a / 2) + ρ * min d x) =
      (∫ _ in (0:ℝ)..1, (1 - ρ) * (a / 2)) + ∫ d in (0:ℝ)..1, ρ * min d x :=
    intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
      ((continuous_const.mul (continuous_id.min continuous_const)).intervalIntegrable _ _)
  rw [e, e2, intervalIntegral.integral_const_mul ρ, int_min x hx0 hx1,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem bench (a ρ rh ch : ℝ) (ha : 0 < a) (hρ0 : 0 < ρ) (hr1 : 1 ≤ rh) (hra : rh ≤ a)
    (hx0 : 0 < xb a ρ rh ch) (hx1 : xb a ρ rh ch < 1) :
    IsBenchOpt a ρ rh ch (Kb a ρ rh + ρ * xb a ρ rh ch) ∧
    (∀ pb, IsBenchOpt a ρ rh ch pb → pb = Kb a ρ rh + ρ * xb a ρ rh ch) ∧
    benchProfit a ρ rh ch (Kb a ρ rh + ρ * xb a ρ rh ch) = ρ * (1 - xb a ρ rh ch) ^ 2 ∧
    benchCC a ρ rh (Kb a ρ rh + ρ * xb a ρ rh ch) =
      (1 - ρ) * (a / 2) + ρ * (xb a ρ rh ch - xb a ρ rh ch ^ 2 / 2) ∧
    benchCap a ρ rh (Kb a ρ rh + ρ * xb a ρ rh ch) = (1 - xb a ρ rh ch) * rh := by
  set xs := xb a ρ rh ch with hxs
  set K := Kb a ρ rh with hK
  have hKc : K - ch = ρ - 2 * ρ * xs := by rw [hxs]; unfold xb; rw [← hK]; field_simp; ring
  have hxx : (K + ρ * xs - K) / ρ = xs := by field_simp; ring
  -- profit as a function of p
  have hprof : ∀ p, benchProfit a ρ rh ch p =
      (1 - max 0 (min ((p - K) / ρ) 1)) * (p - ch) := by
    intro p; unfold benchProfit; rw [tauB_eq a ρ rh p ha hρ0 hr1 hra]
  have hstar : benchProfit a ρ rh ch (K + ρ * xs) = ρ * (1 - xs) ^ 2 := by
    rw [hprof, hxx, min_eq_left hx1.le, max_eq_right hx0.le]; nlinarith [hKc]
  -- key bound: every p gives ≤, with equality only at the optimum
  have hbound : ∀ p, benchProfit a ρ rh ch p ≤ ρ * (1 - xs) ^ 2 ∧
      (benchProfit a ρ rh ch p = ρ * (1 - xs) ^ 2 → p = K + ρ * xs) := by
    intro p
    rw [hprof]
    set x := (p - K) / ρ with hx
    have hp : p = K + ρ * x := by rw [hx]; field_simp; ring
    rcases le_total x 0 with h0 | h0
    · rw [min_eq_left (by linarith), max_eq_left h0]
      have : p - ch ≤ ρ - 2 * ρ * xs := by rw [hp]; nlinarith
      have hq : 0 < ρ * xs ^ 2 := by positivity
      constructor
      · nlinarith
      · intro h; nlinarith
    rcases le_total x 1 with h1 | h1
    · rw [min_eq_left h1, max_eq_right h0]
      have key : (1 - x) * (p - ch) = ρ * (1 - xs) ^ 2 - ρ * (x - xs) ^ 2 := by
        rw [hp]; linear_combination (1 - x) * hKc
      rw [key]
      constructor
      · nlinarith [sq_nonneg (x - xs)]
      · intro h
        have : (x - xs) ^ 2 = 0 := by
          have : ρ * (x - xs) ^ 2 = 0 := by linarith
          rcases mul_eq_zero.1 this with h' | h'
          · linarith
          · exact h'
        have : x = xs := by nlinarith [sq_nonneg (x - xs)]
        rw [hp, this]
    · rw [min_eq_right h1, max_eq_right zero_le_one]
      have hq : 0 < ρ * (1 - xs) ^ 2 := mul_pos hρ0 (pow_pos (by linarith) 2)
      constructor
      · nlinarith
      · intro h; nlinarith
  refine ⟨?_, ?_, hstar, ?_, ?_⟩
  · intro p; rw [hstar]; exact (hbound p).1
  · intro pb hpb
    apply (hbound pb).2
    apply le_antisymm (hbound pb).1
    rw [← hstar]; exact hpb _
  · rw [benchCC_eq a ρ rh _ ha hρ0 hr1 hra (by rw [← hK, hxx]; exact hx0.le)
      (by rw [← hK, hxx]; exact hx1.le), ← hK, hxx]
  · unfold benchCap; rw [tauB_eq a ρ rh _ ha hρ0 hr1 hra, ← hK, hxx, min_eq_left hx1.le,
      max_eq_right hx0.le]


/-! ## Flexible leasing -/

lemma flexLow_iff (a ρ rh ph pbh pbl d : ℝ) (hρ : 0 < ρ) (hr1 : 1 ≤ rh)
    (hd : d ∈ Set.Icc (0:ℝ) 1) : flexLow a ρ rh ph pbh pbl d ↔
      d ≤ (ρ * ph + (1 - ρ) * ECh a rh ph pbl - (1 - ρ) * ECl a rh pbh) / ρ := by
  unfold flexLow
  rw [pos_small d rh hd.2 hr1, le_div_iff₀ hρ]
  constructor <;> intro h <;> nlinarith

lemma tauF_eq (a ρ rh ph pbh pbl : ℝ) (hρ : 0 < ρ) (hr1 : 1 ≤ rh) :
    tauF a ρ rh ph pbh pbl = max 0 (min ((ρ * ph + (1 - ρ) * ECh a rh ph pbl -
      (1 - ρ) * ECl a rh pbh) / ρ) 1) :=
  custVol_le _ _ (fun d hd => flexLow_iff a ρ rh ph pbh pbl d hρ hr1 hd)

lemma flexCC_eq (a ρ rh ph pbh pbl : ℝ) (hρ : 0 < ρ) (hr1 : 1 ≤ rh)
    (hx0 : 0 ≤ (ρ * ph + (1 - ρ) * ECh a rh ph pbl - (1 - ρ) * ECl a rh pbh) / ρ)
    (hx1 : (ρ * ph + (1 - ρ) * ECh a rh ph pbl - (1 - ρ) * ECl a rh pbh) / ρ ≤ 1) :
    flexCC a ρ rh ph pbh pbl = (1 - ρ) * ECl a rh pbh +
      ρ * ((ρ * ph + (1 - ρ) * ECh a rh ph pbl - (1 - ρ) * ECl a rh pbh) / ρ -
        ((ρ * ph + (1 - ρ) * ECh a rh ph pbl - (1 - ρ) * ECl a rh pbh) / ρ) ^ 2 / 2) := by
  set x := (ρ * ph + (1 - ρ) * ECh a rh ph pbl - (1 - ρ) * ECl a rh pbh) / ρ with hx
  have hph : ρ * ph + (1 - ρ) * ECh a rh ph pbl = (1 - ρ) * ECl a rh pbh + ρ * x := by
    rw [hx]; field_simp; ring
  unfold flexCC
  have e : ∫ d in (0:ℝ)..1, min (ρ * d + (1 - ρ) * ECl a rh pbh)
      (ρ * (ph + pos (d - rh)) + (1 - ρ) * ECh a rh ph pbl) =
      ∫ d in (0:ℝ)..1, ((1 - ρ) * ECl a rh pbh + ρ * min d x) := by
    apply intervalIntegral.integral_congr
    intro d hd
    rw [Set.uIcc_of_le zero_le_one] at hd
    simp only
    rw [pos_small d rh hd.2 hr1]
    rcases le_total d x with h | h
    · rw [min_eq_left (by nlinarith), min_eq_left h]; ring
    · rw [min_eq_right (by nlinarith), min_eq_right h]; linarith
  have e2 : ∫ d in (0:ℝ)..1, ((1 - ρ) * ECl a rh pbh + ρ * min d x) =
      (∫ _ in (0:ℝ)..1, (1 - ρ) * ECl a rh pbh) + ∫ d in (0:ℝ)..1, ρ * min d x :=
    intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
      ((continuous_const.mul (continuous_id.min continuous_const)).intervalIntegrable _ _)
  rw [e, e2, intervalIntegral.integral_const_mul ρ, int_min x hx0 hx1,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- The bound `G(τ,λ)` on `a·(peak profit − (1−τ)p_h)`. -/
noncomputable def Gb (a τ lam : ℝ) : ℝ := (1 - τ) * lam ^ 2 / 4 + τ * (a - lam) ^ 2 / 4

lemma peak_expand (a ρ rh ch τ ph q r : ℝ) (hρ1 : ρ < 1) :
    peakObj a ρ rh ch τ ph q r - (1 - τ) * ph =
      downVol a rh τ ph r * (r - ph) + upVol a rh τ q * q -
        ch / (1 - ρ) * max (upVol a rh τ q - downVol a rh τ ph r) 0 := by
  unfold peakObj acq
  have : (1 - ρ) ≠ 0 := by linarith
  field_simp
  ring

/-- Upper bound on the peak profit and its equality case. -/
lemma peak_bound (a ρ rh ch τ ph q r lam : ℝ) (hS : Standing a ρ rh ch)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hRF : RateFeasible a ph q r)
    (hl0 : 0 ≤ lam) (hlc : lam ≤ ch / (1 - ρ)) (hlr : lam < rh) :
    a * (peakObj a ρ rh ch τ ph q r - (1 - τ) * ph) ≤ Gb a τ lam ∧
    (a * (peakObj a ρ rh ch τ ph q r - (1 - τ) * ph) = Gb a τ lam →
      q = (a + lam) / 2 ∧ r = ph - lam / 2) := by
  obtain ⟨ha1, ⟨hρ0', hρ1⟩, ⟨hr0, hra⟩, hch⟩ := hS
  have ha : 0 < a := by linarith
  obtain ⟨hqa, hrlo, hrhi⟩ := hRF
  obtain ⟨u1, u2, u3, -, d1, d2, -, -⟩ := lemma_2 a ρ rh ch τ ph q r
    ⟨ha1, ⟨hρ0', hρ1⟩, ⟨hr0, hra⟩, hch⟩ hτ0.le hτ1.le
  rw [peak_expand a ρ rh ch τ ph q r hρ1]
  set c := ch / (1 - ρ) with hc
  set U := upVol a rh τ q with hU
  set W := downVol a rh τ ph r with hW
  set m := max (U - W) 0 with hm
  have hm1 : U - W ≤ m := le_max_left _ _
  have hm0 : 0 ≤ m := le_max_right _ _
  have hcm : lam * (U - W) ≤ c * m := by nlinarith
  have hG : 0 < Gb a τ lam := by
    unfold Gb
    have : 0 < τ * (a - lam) ^ 2 := mul_pos hτ0 (pow_pos (by linarith) 2)
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - τ) (sq_nonneg lam)]
  set s := ph - r with hs
  have hs0 : 0 ≤ s := by linarith
  have hsa : s ≤ a := by linarith
  rcases lt_or_ge r (ph - rh) with hr | hr
  · -- deep downgrade: W = 1 - τ
    have hWv : W = 1 - τ := d1 hr
    have hsr : rh < s := by linarith
    have hWpart : a * (W * (r - ph)) + a * lam * W < 0 := by
      rw [hWv]; nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - τ) (by linarith : (0:ℝ) < s - lam)]
    have hUpart : a * (U * q) - a * lam * U ≤ τ * (a - lam) ^ 2 / 4 := by
      rcases lt_or_ge q 0 with hq | hq
      · rw [u1 hq]; nlinarith [mul_pos hτ0 ha]
      rcases le_or_gt q rh with hq2 | hq2
      · rw [u2 hq hq2]; field_simp
        nlinarith [mul_nonneg hτ0.le (sq_nonneg (q - (a + lam) / 2))]
      · rw [u3 hq2]; nlinarith [mul_nonneg hτ0.le (sq_nonneg (a - lam))]
    have : a * (W * (r - ph) + U * q - c * m) < Gb a τ lam := by
      have f1 : a * (lam * (U - W)) ≤ a * (c * m) := mul_le_mul_of_nonneg_left hcm ha.le
      have e1 : a * (W * (r - ph) + U * q - c * m) = a * (W * (r - ph)) + a * (U * q) - a * (c * m) := by ring
      have e2 : a * (lam * (U - W)) = a * lam * U - a * lam * W := by ring
      have f2 : 0 ≤ (1 - τ) * lam ^ 2 / 4 := by
        have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - τ) (sq_nonneg lam); linarith
      unfold Gb
      linarith
    exact ⟨this.le, fun h => absurd h this.ne⟩
  · have hWv : W = (1 - τ) * (ph - r) / a := d2 hr hrhi
    rcases lt_or_ge q 0 with hq | hq
    · have hUv : U = τ := u1 hq
      have : a * (W * (r - ph) + U * q - c * m) < Gb a τ lam := by
        have e1 : a * (W * (r - ph) + U * q - c * m) = -(1 - τ) * s ^ 2 + a * τ * q - a * (c * m) := by
          rw [hWv, hUv, hs]; field_simp; ring
        have e2 : a * (lam * (U - W)) = a * lam * τ - lam * (1 - τ) * s := by
          rw [hWv, hUv, hs]; field_simp
        have e3 : -(1 - τ) * s ^ 2 + lam * (1 - τ) * s = (1 - τ) * lam ^ 2 / 4 - (1 - τ) * (s - lam / 2) ^ 2 := by ring
        have f1 : a * (lam * (U - W)) ≤ a * (c * m) := mul_le_mul_of_nonneg_left hcm ha.le
        have f2 : 0 ≤ (1 - τ) * (s - lam / 2) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
        have f3 : a * τ * q < 0 := mul_neg_of_pos_of_neg (mul_pos ha hτ0) hq
        have f4 : 0 ≤ a * lam * τ := by positivity
        have f5 : 0 ≤ τ * (a - lam) ^ 2 / 4 := by positivity
        unfold Gb
        linarith
      exact ⟨this.le, fun h => absurd h this.ne⟩
    rcases le_or_gt q rh with hq2 | hq2
    · have hUv : U = τ * (a - q) / a := u2 hq hq2
      have E : a * (W * (r - ph) + U * q - c * m) = Gb a τ lam - (1 - τ) * (s - lam / 2) ^ 2 -
          τ * (q - (a + lam) / 2) ^ 2 - a * (c * m - lam * (U - W)) := by
        rw [hUv, hWv, hs]; unfold Gb; field_simp; ring
      have h1 : 0 ≤ (1 - τ) * (s - lam / 2) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      have h2 : 0 ≤ τ * (q - (a + lam) / 2) ^ 2 := mul_nonneg hτ0.le (sq_nonneg _)
      have h3 : 0 ≤ a * (c * m - lam * (U - W)) := mul_nonneg ha.le (by linarith)
      refine ⟨by rw [E]; linarith, fun h => ?_⟩
      rw [E] at h
      have h1' : (1 - τ) * (s - lam / 2) ^ 2 = 0 := by linarith
      have h2' : τ * (q - (a + lam) / 2) ^ 2 = 0 := by linarith
      rcases mul_eq_zero.1 h1' with h | h
      · linarith
      rcases mul_eq_zero.1 h2' with h' | h'
      · linarith
      constructor
      · have := pow_eq_zero_iff (n := 2) (a := q - (a + lam) / 2) two_ne_zero |>.1 h'
        linarith
      · have := pow_eq_zero_iff (n := 2) (a := s - lam / 2) two_ne_zero |>.1 h
        rw [hs] at this; linarith
    · have hUv : U = 0 := u3 hq2
      have hW0 : 0 ≤ W := by rw [hWv]; apply div_nonneg _ ha.le; nlinarith
      have hm' : m = 0 := by rw [hm, hUv]; simp; linarith
      have : a * (W * (r - ph) + U * q - c * m) < Gb a τ lam := by
        rw [hUv, hm']; nlinarith [mul_nonneg hW0 hs0]
      exact ⟨this.le, fun h => absurd h this.ne⟩


noncomputable def Psi (a ρ ch τ lam : ℝ) : ℝ :=
  (1 - τ) * (ρ * τ + (1 - ρ) * (3 * a + 2 * lam) / 8 - ch) +
    (1 - ρ) * ((1 - τ) * lam ^ 2 + τ * (a - lam) ^ 2) / (4 * a)

lemma clamp_eq (t X : ℝ) (h0 : 0 < t) (h1 : t < 1) (h : t = max 0 (min X 1)) : X = t := by
  rcases le_total X 1 with hX | hX
  · rw [min_eq_left hX] at h
    rcases le_total X 0 with hX0 | hX0
    · rw [max_eq_left hX0] at h; linarith
    · rw [max_eq_right hX0] at h; exact h.symm
  · rw [min_eq_right hX, max_eq_right zero_le_one] at h; linarith

lemma peak_star (a ρ rh ch τ ph lam : ℝ) (hS : Standing a ρ rh ch)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hl0 : 0 ≤ lam) (hlc : lam ≤ ch / (1 - ρ)) (hlt : lam ≤ a * τ)
    (hlor : lam = ch / (1 - ρ) ∨ lam = a * τ) (hq : (a + lam) / 2 ≤ rh) :
    a * (peakObj a ρ rh ch τ ph ((a + lam) / 2) (ph - lam / 2) - (1 - τ) * ph) = Gb a τ lam := by
  obtain ⟨ha1, ⟨hρ0', hρ1⟩, ⟨hr0, hra⟩, hch⟩ := hS
  have ha : 0 < a := by linarith
  obtain ⟨-, u2, -, -, -, d2, -, -⟩ := lemma_2 a ρ rh ch τ ph ((a + lam) / 2) (ph - lam / 2)
    ⟨ha1, ⟨hρ0', hρ1⟩, ⟨hr0, hra⟩, hch⟩ hτ0.le hτ1.le
  rw [peak_expand a ρ rh ch τ ph _ _ hρ1, u2 (by linarith) hq, d2 (by linarith) (by linarith)]
  have hUW : τ * (a - (a + lam) / 2) / a - (1 - τ) * (ph - (ph - lam / 2)) / a =
      (a * τ - lam) / (2 * a) := by field_simp; ring
  rw [hUW]
  have hm : ch / (1 - ρ) * max ((a * τ - lam) / (2 * a)) 0 = lam * ((a * τ - lam) / (2 * a)) := by
    rw [max_eq_left (div_nonneg (by linarith) (by linarith))]
    rcases hlor with h | h
    · rw [h]
    · rw [h]; ring
  rw [hm]
  unfold Gb
  field_simp
  ring

lemma rf_star (a ph lam : ℝ) (hl0 : 0 ≤ lam) (hla : lam ≤ a) :
    RateFeasible a ph ((a + lam) / 2) (ph - lam / 2) :=
  ⟨by linarith, by linarith, by linarith⟩

lemma tauF_star (a ρ rh ph lam : ℝ) (ha : 0 < a) (hρ : 0 < ρ) (hr1 : 1 ≤ rh) (hra : rh ≤ a)
    (hl0 : 0 ≤ lam) (hq : (a + lam) / 2 ≤ rh) :
    (ρ * ph + (1 - ρ) * ECh a rh ph (ph - lam / 2) - (1 - ρ) * ECl a rh ((a + lam) / 2)) / ρ =
      (ph - (1 - ρ) * (3 * a + 2 * lam) / 8) / ρ := by
  rw [ECh_eq a rh ph _ ha (by linarith) (by linarith) hra, ECl_eq a rh _ ha (by linarith) hq hra]
  congr 1
  field_simp
  ring

lemma cont_mid (a ρ rh ch ph τ q r lam : ℝ) (hS : Standing a ρ rh ch) (hr1 : 1 ≤ rh)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hC : IsContinuation a ρ rh ch ph τ q r)
    (hl0 : 0 ≤ lam) (hlc : lam ≤ ch / (1 - ρ)) (hlt : lam ≤ a * τ)
    (hlor : lam = ch / (1 - ρ) ∨ lam = a * τ) (hq : (a + lam) / 2 ≤ rh) (hlr : lam < rh) :
    q = (a + lam) / 2 ∧ r = ph - lam / 2 ∧ ph = ρ * τ + (1 - ρ) * (3 * a + 2 * lam) / 8 ∧
      flexProfit a ρ rh ch ph τ q r = Psi a ρ ch τ lam := by
  have hS' := hS
  obtain ⟨ha1, ⟨hρ0', hρ1⟩, ⟨hr0, hra⟩, hch⟩ := hS'
  have ha : 0 < a := by linarith
  have hρ : 0 < ρ := lt_trans (by positivity) hρ0'
  obtain ⟨hRF, hopt, hτF⟩ := hC
  have h1 := hopt _ _ (rf_star a ph lam hl0 (by linarith))
  have hstar := peak_star a ρ rh ch τ ph lam hS hτ0 hτ1 hl0 hlc hlt hlor hq
  obtain ⟨hb, heq⟩ := peak_bound a ρ rh ch τ ph q r lam hS hτ0 hτ1 hRF hl0 hlc hlr
  have hE : a * (peakObj a ρ rh ch τ ph q r - (1 - τ) * ph) = Gb a τ lam := by
    apply le_antisymm hb
    rw [← hstar]
    exact mul_le_mul_of_nonneg_left (by linarith) ha.le
  obtain ⟨hqq, hrr⟩ := heq hE
  subst hqq hrr
  rw [tauF_eq a ρ rh _ _ _ hρ hr1, tauF_star a ρ rh ph lam ha hρ hr1 hra hl0 hq] at hτF
  have hX := clamp_eq τ _ hτ0 hτ1 hτF
  have hph : ph = ρ * τ + (1 - ρ) * (3 * a + 2 * lam) / 8 := by
    field_simp at hX; linarith
  refine ⟨rfl, rfl, hph, ?_⟩
  have hpk : peakObj a ρ rh ch τ ph ((a + lam) / 2) (ph - lam / 2) = (1 - τ) * ph + Gb a τ lam / a := by
    rw [← hstar]; field_simp; ring
  unfold flexProfit Psi
  rw [hpk]
  unfold Gb
  rw [hph]
  field_simp
  ring

lemma cont_zero (a ρ rh ch ph q r : ℝ) (hS : Standing a ρ rh ch) (hr1 : 1 ≤ rh)
    (hC : IsContinuation a ρ rh ch ph 0 q r) :
    flexProfit a ρ rh ch ph 0 q r ≤ Kb a ρ rh - ch := by
  have hS' := hS
  obtain ⟨ha1, ⟨hρ0', hρ1⟩, ⟨hr0, hra⟩, hch⟩ := hS'
  have ha : 0 < a := by linarith
  have hρ : 0 < ρ := lt_trans (by positivity) hρ0'
  obtain ⟨⟨hqa, hrlo, hrhi⟩, hopt, hτF⟩ := hC
  have hup : ∀ x, upVol a rh 0 x = 0 := by intro x; unfold upVol; simp
  have hpk : ∀ x y, peakObj a ρ rh ch 0 ph x y = ph + downVol a rh 0 ph y * (y - ph) -
      ch / (1 - ρ) * max (-downVol a rh 0 ph y) 0 := by
    intro x y
    have := peak_expand a ρ rh ch 0 ph x y hρ1
    rw [hup] at this; simp only [zero_sub, zero_mul, add_zero, sub_zero, one_mul] at this ⊢
    linarith
  obtain ⟨-, -, -, -, d1, d2, -, -⟩ := lemma_2 a ρ rh ch 0 ph q r hS le_rfl zero_le_one
  obtain ⟨-, -, -, -, -, d2', -, -⟩ := lemma_2 a ρ rh ch 0 ph q ph hS le_rfl zero_le_one
  have hph0 : downVol a rh 0 ph ph = 0 := by rw [d2' (by linarith) le_rfl]; simp
  have h1 := hopt q ph ⟨hqa, by linarith, le_rfl⟩
  rw [hpk, hpk, hph0] at h1
  simp only [sub_self, mul_zero, add_zero, neg_zero, max_self] at h1
  -- r = ph
  have hr : r = ph := by
    rcases lt_or_ge r (ph - rh) with h | h
    · rw [d1 h] at h1
      have : max (-(1 - 0 : ℝ)) 0 = 0 := by norm_num
      rw [this] at h1; nlinarith
    · rw [d2 h hrhi] at h1
      have hW : 0 ≤ (1 - 0) * (ph - r) / a := div_nonneg (by linarith) ha.le
      have : max (-((1 - 0) * (ph - r) / a)) 0 = 0 := max_eq_right (by linarith)
      rw [this] at h1
      have : (1 - 0) * (ph - r) / a * (r - ph) = -((ph - r) ^ 2 / a) := by field_simp; ring
      have hsq : 0 ≤ (ph - r) ^ 2 / a := div_nonneg (sq_nonneg _) ha.le
      have : (ph - r) ^ 2 / a = 0 := by linarith
      have : (ph - r) ^ 2 = 0 := by
        rcases div_eq_zero_iff.1 this with h | h
        · exact h
        · linarith
      have := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 this
      linarith
  subst hr
  rw [tauF_eq a ρ rh _ _ _ hρ hr1, ECh_eq a rh r r ha (by simp) (by simp; linarith) hra] at hτF
  have hcl := ECl_le a rh q ha
  set X := (ρ * r + (1 - ρ) * ((a * r - (r - r) ^ 2 / 2 + (a - rh) ^ 2 / 2) / a) -
    (1 - ρ) * ECl a rh q) / ρ with hX
  have hX0 : X ≤ 0 := by
    by_contra hc
    push_neg at hc
    have : 0 < max 0 (min X 1) := lt_of_lt_of_le (lt_min hc one_pos) (le_max_right _ _)
    linarith
  have hnum : ρ * r + (1 - ρ) * ((a * r - (r - r) ^ 2 / 2 + (a - rh) ^ 2 / 2) / a) -
      (1 - ρ) * ECl a rh q ≤ 0 := by
    have := (div_nonpos_iff.1 hX0)
    rcases this with h | h
    · linarith [h.2]
    · exact h.1
  have hpk' : peakObj a ρ rh ch 0 r q r = r := by
    rw [hpk, hph0]; simp
  unfold flexProfit
  rw [hpk']
  unfold Kb
  have e : (a * r - (r - r) ^ 2 / 2 + (a - rh) ^ 2 / 2) / a = r + (a - rh) ^ 2 / (2 * a) := by
    field_simp; ring
  rw [e] at hnum
  have : (1 - ρ) * ECl a rh q ≤ (1 - ρ) * (a / 2) := mul_le_mul_of_nonneg_left hcl (by linarith)
  have e2 : (1 - ρ) * (a / 2) - (1 - ρ) * ((a - rh) ^ 2 / (2 * a)) = (1 - ρ) * rh * (2 * a - rh) / (2 * a) := by
    field_simp; ring
  nlinarith

lemma cont_one (a ρ rh ch ph q r : ℝ) (hS : Standing a ρ rh ch)
    (hC : IsContinuation a ρ rh ch ph 1 q r) :
    flexProfit a ρ rh ch ph 1 q r ≤ Psi a ρ ch 1 (ch / (1 - ρ)) := by
  have hS' := hS
  obtain ⟨ha1, ⟨hρ0', hρ1⟩, ⟨hr0, hra⟩, hch0, hch1⟩ := hS'
  have ha : 0 < a := by linarith
  have hρ : 0 < ρ := lt_trans (by positivity) hρ0'
  obtain ⟨⟨hqa, hrlo, hrhi⟩, -, -⟩ := hC
  have hdown : downVol a rh 1 ph r = 0 := by unfold downVol; simp
  have hpk := peak_expand a ρ rh ch 1 ph q r hρ1
  rw [hdown] at hpk
  obtain ⟨u1, u2, u3, -, -, -, -, -⟩ := lemma_2 a ρ rh ch 1 ph q r hS zero_le_one le_rfl
  set c := ch / (1 - ρ) with hc
  have hc0 : 0 ≤ c := div_nonneg hch0 (by linarith)
  have hca : c ≤ a := by rw [hc, div_le_iff₀ (by linarith)]; linarith
  have hbound : peakObj a ρ rh ch 1 ph q r ≤ (a - c) ^ 2 / (4 * a) := by
    have hpk' : peakObj a ρ rh ch 1 ph q r = upVol a rh 1 q * q - c * max (upVol a rh 1 q) 0 := by
      simp only [sub_self, zero_mul, zero_add, sub_zero] at hpk; linarith
    rw [hpk']
    have hq4 : 0 ≤ (a - c) ^ 2 / (4 * a) := by positivity
    rcases lt_or_ge q 0 with h | h
    · rw [u1 h, max_eq_left zero_le_one]; nlinarith
    rcases le_or_gt q rh with h2 | h2
    · rw [u2 h h2, max_eq_left (div_nonneg (by linarith) ha.le)]
      rw [show (1 * (a - q) / a * q - c * (1 * (a - q) / a)) = (a - q) * (q - c) / a by field_simp]
      rw [div_le_div_iff₀ ha (by positivity)]
      nlinarith [sq_nonneg (a + c - 2 * q)]
    · rw [u3 h2]; simp; exact hq4
  unfold flexProfit Psi
  simp only [sub_self, zero_mul, mul_zero, zero_add, sub_zero, one_mul]
  have : (1 - ρ) * peakObj a ρ rh ch 1 ph q r ≤ (1 - ρ) * ((a - c) ^ 2 / (4 * a)) :=
    mul_le_mul_of_nonneg_left hbound (by linarith)
  calc _ ≤ (1 - ρ) * ((a - c) ^ 2 / (4 * a)) := by linarith
    _ = _ := by field_simp


lemma tauF_mem (a ρ rh ph pbh pbl : ℝ) :
    0 ≤ tauF a ρ rh ph pbh pbl ∧ tauF a ρ rh ph pbh pbl ≤ 1 :=
  ⟨custVol_nonneg _, custVol_le_one _⟩

theorem flex_main (a ρ rh ch ts : ℝ) (hS : Standing a ρ rh ch) (hr1 : 1 ≤ rh)
    (hcq : (a + ch / (1 - ρ)) / 2 ≤ rh) (hcr : ch / (1 - ρ) < rh)
    (hts0 : 0 < ts) (hts1 : ts < 1) (hcts : ch / (1 - ρ) ≤ a * ts)
    (hP1 : ∀ τ, 0 < τ → τ ≤ 1 → ch / (1 - ρ) ≤ a * τ → τ ≠ ts →
      Psi a ρ ch τ (ch / (1 - ρ)) < Psi a ρ ch ts (ch / (1 - ρ)))
    (hP2 : ∀ τ, 0 < τ → a * τ < ch / (1 - ρ) →
      Psi a ρ ch τ (a * τ) < Psi a ρ ch ts (ch / (1 - ρ)))
    (h0 : Kb a ρ rh - ch < Psi a ρ ch ts (ch / (1 - ρ))) :
    IsFlexEq a ρ rh ch (ρ * ts + (1 - ρ) * (3 * a + 2 * (ch / (1 - ρ))) / 8) ts
      ((a + ch / (1 - ρ)) / 2) (ρ * ts + (1 - ρ) * (3 * a + 2 * (ch / (1 - ρ))) / 8 - ch / (1 - ρ) / 2) ∧
    (∀ ph τ q r, IsFlexEq a ρ rh ch ph τ q r →
      ph = ρ * ts + (1 - ρ) * (3 * a + 2 * (ch / (1 - ρ))) / 8 ∧ τ = ts ∧
      q = (a + ch / (1 - ρ)) / 2 ∧
      r = ρ * ts + (1 - ρ) * (3 * a + 2 * (ch / (1 - ρ))) / 8 - ch / (1 - ρ) / 2) ∧
    flexProfit a ρ rh ch (ρ * ts + (1 - ρ) * (3 * a + 2 * (ch / (1 - ρ))) / 8) ts
      ((a + ch / (1 - ρ)) / 2) (ρ * ts + (1 - ρ) * (3 * a + 2 * (ch / (1 - ρ))) / 8 - ch / (1 - ρ) / 2) =
      Psi a ρ ch ts (ch / (1 - ρ)) := by
  have hS' := hS
  obtain ⟨ha1, ⟨hρ0', hρ1⟩, ⟨hr0, hra⟩, hch0, hch1⟩ := hS'
  have ha : 0 < a := by linarith
  have hρ : 0 < ρ := lt_trans (by positivity) hρ0'
  set c := ch / (1 - ρ) with hc
  have hc0 : 0 ≤ c := div_nonneg hch0 (by linarith)
  set phs := ρ * ts + (1 - ρ) * (3 * a + 2 * c) / 8 with hphs
  -- the candidate is a continuation
  have hcont : IsContinuation a ρ rh ch phs ts ((a + c) / 2) (phs - c / 2) := by
    refine ⟨rf_star a phs c hc0 (by linarith), ?_, ?_⟩
    · intro q r hqr
      have hb := (peak_bound a ρ rh ch ts phs q r c hS hts0 hts1 hqr hc0 le_rfl hcr).1
      have hs := peak_star a ρ rh ch ts phs c hS hts0 hts1 hc0 le_rfl hcts (Or.inl rfl) hcq
      have : a * peakObj a ρ rh ch ts phs q r ≤ a * peakObj a ρ rh ch ts phs ((a + c) / 2) (phs - c / 2) := by
        linarith
      exact le_of_mul_le_mul_left this ha
    · rw [tauF_eq a ρ rh _ _ _ hρ hr1, tauF_star a ρ rh phs c ha hρ hr1 hra hc0 hcq]
      have : (phs - (1 - ρ) * (3 * a + 2 * c) / 8) / ρ = ts := by rw [hphs]; field_simp; ring
      rw [this, min_eq_left hts1.le, max_eq_right hts0.le]
  have hprof : flexProfit a ρ rh ch phs ts ((a + c) / 2) (phs - c / 2) = Psi a ρ ch ts c :=
    (cont_mid a ρ rh ch phs ts _ _ c hS hr1 hts0 hts1 hcont hc0 le_rfl hcts (Or.inl rfl) hcq hcr).2.2.2
  -- every continuation is weakly worse, strictly unless it is the candidate
  have key : ∀ ph τ q r, IsContinuation a ρ rh ch ph τ q r →
      flexProfit a ρ rh ch ph τ q r ≤ Psi a ρ ch ts c ∧
      (flexProfit a ρ rh ch ph τ q r = Psi a ρ ch ts c →
        ph = phs ∧ τ = ts ∧ q = (a + c) / 2 ∧ r = phs - c / 2) := by
    intro ph τ q r hC
    have hτm : 0 ≤ τ ∧ τ ≤ 1 := by rw [hC.2.2]; exact tauF_mem _ _ _ _ _ _
    rcases eq_or_lt_of_le hτm.1 with h | hτ0
    · subst h
      have := cont_zero a ρ rh ch ph q r hS hr1 hC
      exact ⟨by linarith, fun h => by linarith⟩
    rcases eq_or_lt_of_le hτm.2 with h | hτ1
    · subst h
      have h1 := cont_one a ρ rh ch ph q r hS hC
      have h2 := hP1 1 one_pos le_rfl (by linarith) (by intro h; linarith)
      exact ⟨by linarith, fun h => by linarith⟩
    rcases le_or_gt c (a * τ) with hca | hca
    · obtain ⟨hq, hr, hph, hpr⟩ := cont_mid a ρ rh ch ph τ q r c hS hr1 hτ0 hτ1 hC hc0 le_rfl hca
        (Or.inl rfl) hcq hcr
      rw [hpr]
      by_cases hτt : τ = ts
      · subst hτt
        exact ⟨le_rfl, fun _ => ⟨hph, rfl, hq, by rw [hr, hph]⟩⟩
      · have := hP1 τ hτ0 hτ1.le hca hτt
        exact ⟨this.le, fun h => absurd h this.ne⟩
    · have hl0 : 0 ≤ a * τ := by positivity
      obtain ⟨-, -, -, hpr⟩ := cont_mid a ρ rh ch ph τ q r (a * τ) hS hr1 hτ0 hτ1 hC hl0 hca.le le_rfl
        (Or.inr rfl) (by linarith) (by linarith)
      rw [hpr]
      have := hP2 τ hτ0 hca
      exact ⟨this.le, fun h => absurd h this.ne⟩
  have hEq : IsFlexEq a ρ rh ch phs ts ((a + c) / 2) (phs - c / 2) := by
    refine ⟨hcont, fun ph' τ' q r hC => ?_⟩
    rw [hprof]; exact (key ph' τ' q r hC).1
  refine ⟨hEq, fun ph τ q r hE => ?_, hprof⟩
  have h1 := hE.2 _ _ _ _ hcont
  rw [hprof] at h1
  exact (key ph τ q r hE.1).2 (le_antisymm (key ph τ q r hE.1).1 h1)

theorem flex_values (a ρ rh ch ts : ℝ) (hS : Standing a ρ rh ch) (hr1 : 1 ≤ rh)
    (hcq : (a + ch / (1 - ρ)) / 2 ≤ rh)
    (hts0 : 0 < ts) (hts1 : ts < 1) (hcts : ch / (1 - ρ) ≤ a * ts) :
    acq a rh ts (ρ * ts + (1 - ρ) * (3 * a + 2 * (ch / (1 - ρ))) / 8) ((a + ch / (1 - ρ)) / 2)
      (ρ * ts + (1 - ρ) * (3 * a + 2 * (ch / (1 - ρ))) / 8 - ch / (1 - ρ) / 2) =
      (a * ts - ch / (1 - ρ)) / (2 * a) ∧
    flexCC a ρ rh (ρ * ts + (1 - ρ) * (3 * a + 2 * (ch / (1 - ρ))) / 8) ((a + ch / (1 - ρ)) / 2)
      (ρ * ts + (1 - ρ) * (3 * a + 2 * (ch / (1 - ρ))) / 8 - ch / (1 - ρ) / 2) =
      (1 - ρ) * ((a * ((a + ch / (1 - ρ)) / 2) - ((a + ch / (1 - ρ)) / 2) ^ 2 / 2 +
        (a - rh) ^ 2 / 2) / a) + ρ * (ts - ts ^ 2 / 2) := by
  have hS' := hS
  obtain ⟨ha1, ⟨hρ0', hρ1⟩, ⟨hr0, hra⟩, hch0, hch1⟩ := hS'
  have ha : 0 < a := by linarith
  have hρ : 0 < ρ := lt_trans (by positivity) hρ0'
  set c := ch / (1 - ρ) with hc
  have hc0 : 0 ≤ c := div_nonneg hch0 (by linarith)
  set phs := ρ * ts + (1 - ρ) * (3 * a + 2 * c) / 8 with hphs
  constructor
  · obtain ⟨-, u2, -, -, -, d2, -, -⟩ := lemma_2 a ρ rh ch ts phs ((a + c) / 2) (phs - c / 2)
      hS hts0.le hts1.le
    unfold acq
    rw [u2 (by linarith) hcq, d2 (by linarith) (by linarith)]
    have : ts * (a - (a + c) / 2) / a - (1 - ts) * (phs - (phs - c / 2)) / a =
        (a * ts - c) / (2 * a) := by field_simp; ring
    rw [this, max_eq_left (div_nonneg (by linarith) (by linarith))]
  · have hX : (ρ * phs + (1 - ρ) * ECh a rh phs (phs - c / 2) - (1 - ρ) * ECl a rh ((a + c) / 2)) / ρ = ts := by
      rw [tauF_star a ρ rh phs c ha hρ hr1 hra hc0 hcq, hphs]; field_simp; ring
    rw [flexCC_eq a ρ rh _ _ _ hρ hr1 (by rw [hX]; exact hts0.le) (by rw [hX]; exact hts1.le), hX,
      ECl_eq a rh _ ha (by linarith) hcq hra]


theorem inner (a ρ rh ch ts : ℝ) (hS : Standing a ρ rh ch) (hr1 : 1 ≤ rh)
    (hcq : (a + ch / (1 - ρ)) / 2 ≤ rh) (hcr : ch / (1 - ρ) < rh)
    (hx0 : 0 < xb a ρ rh ch) (hx1 : xb a ρ rh ch < 1)
    (hts0 : 0 < ts) (hts1 : ts < 1) (hcts : ch / (1 - ρ) ≤ a * ts)
    (hP1 : ∀ τ, 0 < τ → τ ≤ 1 → ch / (1 - ρ) ≤ a * τ → τ ≠ ts →
      Psi a ρ ch τ (ch / (1 - ρ)) < Psi a ρ ch ts (ch / (1 - ρ)))
    (hP2 : ∀ τ, 0 < τ → a * τ < ch / (1 - ρ) →
      Psi a ρ ch τ (a * τ) < Psi a ρ ch ts (ch / (1 - ρ)))
    (h0 : Kb a ρ rh - ch < Psi a ρ ch ts (ch / (1 - ρ)))
    (hpi : ρ * (1 - xb a ρ rh ch) ^ 2 < Psi a ρ ch ts (ch / (1 - ρ)))
    (hcc : (1 - ρ) * ((a * ((a + ch / (1 - ρ)) / 2) - ((a + ch / (1 - ρ)) / 2) ^ 2 / 2 +
        (a - rh) ^ 2 / 2) / a) + ρ * (ts - ts ^ 2 / 2) <
      (1 - ρ) * (a / 2) + ρ * (xb a ρ rh ch - xb a ρ rh ch ^ 2 / 2))
    (hcap : (1 - ts + (a * ts - ch / (1 - ρ)) / (2 * a)) * rh < (1 - xb a ρ rh ch) * rh) :
    (∃ pb, IsBenchOpt a ρ rh ch pb) ∧
    (∃ ph τ pbh pbl, IsFlexEq a ρ rh ch ph τ pbh pbl) ∧
    ∀ pb, IsBenchOpt a ρ rh ch pb → ∀ ph τ pbh pbl, IsFlexEq a ρ rh ch ph τ pbh pbl →
      acq a rh τ ph pbh pbl = (a * ts - ch / (1 - ρ)) / (2 * a) ∧
      benchProfit a ρ rh ch pb < flexProfit a ρ rh ch ph τ pbh pbl ∧
      flexCC a ρ rh ph pbh pbl < benchCC a ρ rh pb ∧
      flexCap a rh τ ph pbh pbl < benchCap a ρ rh pb := by
  have hS' := hS
  obtain ⟨ha1, ⟨hρ0', hρ1⟩, ⟨hr0, hra⟩, hch0, hch1⟩ := hS'
  have ha : 0 < a := by linarith
  have hρ : 0 < ρ := lt_trans (by positivity) hρ0'
  obtain ⟨bOpt, bUniq, bProf, bCC, bCap⟩ := bench a ρ rh ch ha hρ hr1 hra hx0 hx1
  obtain ⟨fEq, fUniq, fProf⟩ := flex_main a ρ rh ch ts hS hr1 hcq hcr hts0 hts1 hcts hP1 hP2 h0
  obtain ⟨fAcq, fCC⟩ := flex_values a ρ rh ch ts hS hr1 hcq hts0 hts1 hcts
  refine ⟨⟨_, bOpt⟩, ⟨_, _, _, _, fEq⟩, fun pb hpb ph τ pbh pbl hE => ?_⟩
  have hpb := bUniq pb hpb
  obtain ⟨e1, e2, e3, e4⟩ := fUniq ph τ pbh pbl hE
  subst hpb e1 e2 e3 e4
  refine ⟨fAcq, by rw [bProf, fProf]; exact hpi, by rw [bCC, fCC]; exact hcc, ?_⟩
  unfold flexCap
  rw [bCap, fAcq]
  exact hcap


noncomputable def tA (a ρ ch : ℝ) : ℝ := (2 * ch + ρ * (8 + a) - a) / (16 * ρ)
noncomputable def tB (a ρ ch : ℝ) : ℝ :=
  (ρ + (1 - ρ) * a / 2 - ((1 - ρ) * (3 * a / 8) - ch)) / (2 * (ρ + (1 - ρ) * a / 2))

lemma psiA_id (a ρ ch τ : ℝ) (ha : 0 < a) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    Psi a ρ ch τ (ch / (1 - ρ)) = Psi a ρ ch (tA a ρ ch) (ch / (1 - ρ)) - ρ * (τ - tA a ρ ch) ^ 2 := by
  have : (1 - ρ) ≠ 0 := by linarith
  unfold Psi tA; field_simp; ring

lemma psiB_id (a ρ ch τ t : ℝ) (ha : 0 < a) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    Psi a ρ ch τ (a * τ) = Psi a ρ ch t (a * t) -
      (ρ + (1 - ρ) * a / 2) * (τ - t) * (τ + t - 2 * tB a ρ ch) := by
  have hβ : (ρ + (1 - ρ) * a / 2) ≠ 0 := by nlinarith
  have hT : 2 * (ρ + (1 - ρ) * a / 2) * tB a ρ ch =
      ρ + (1 - ρ) * a / 2 - ((1 - ρ) * (3 * a / 8) - ch) := by
    have hβ' : 2 * ρ + (1 - ρ) * a ≠ 0 := by nlinarith
    unfold tB; field_simp
  have hf : ∀ x, Psi a ρ ch x (a * x) =
      (1 - x) * ((ρ + (1 - ρ) * a / 2) * x + ((1 - ρ) * (3 * a / 8) - ch)) := by
    intro x; unfold Psi; field_simp; ring
  rw [hf, hf]
  linear_combination (t - τ) * hT

lemma P2_gen (a ρ ch τ : ℝ) (ha : 0 < a) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hB : ch / (1 - ρ) / a ≤ tB a ρ ch) (hτ : a * τ < ch / (1 - ρ)) :
    Psi a ρ ch τ (a * τ) < Psi a ρ ch (ch / (1 - ρ) / a) (ch / (1 - ρ)) := by
  have e := psiB_id a ρ ch τ (ch / (1 - ρ) / a) ha hρ hρ1
  have e2 : a * (ch / (1 - ρ) / a) = ch / (1 - ρ) := by field_simp
  rw [e2] at e
  rw [e]
  have h1 : τ < ch / (1 - ρ) / a := by rw [lt_div_iff₀ ha]; linarith
  have hβ : 0 < ρ + (1 - ρ) * a / 2 := by nlinarith
  have : 0 < (ρ + (1 - ρ) * a / 2) * (τ - ch / (1 - ρ) / a) * (τ + ch / (1 - ρ) / a - 2 * tB a ρ ch) := by
    apply mul_pos_of_neg_of_neg
    · exact mul_neg_of_pos_of_neg hβ (by linarith)
    · linarith
  linarith

lemma branch1_P (a ρ ch : ℝ) (ha : 0 < a) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hB : ch / (1 - ρ) / a ≤ tB a ρ ch) :
    (∀ τ, 0 < τ → τ ≤ 1 → ch / (1 - ρ) ≤ a * τ → τ ≠ tA a ρ ch →
      Psi a ρ ch τ (ch / (1 - ρ)) < Psi a ρ ch (tA a ρ ch) (ch / (1 - ρ))) ∧
    (∀ τ, 0 < τ → a * τ < ch / (1 - ρ) →
      Psi a ρ ch τ (a * τ) < Psi a ρ ch (tA a ρ ch) (ch / (1 - ρ))) := by
  constructor
  · intro τ _ _ _ hne
    rw [psiA_id a ρ ch τ ha hρ hρ1]
    have : 0 < (τ - tA a ρ ch) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hne)))
    nlinarith
  · intro τ _ hτ
    have h1 := P2_gen a ρ ch τ ha hρ hρ1 hB hτ
    have h2 := psiA_id a ρ ch (ch / (1 - ρ) / a) ha hρ hρ1
    nlinarith [sq_nonneg (ch / (1 - ρ) / a - tA a ρ ch)]

lemma branch2_P (a ρ ch : ℝ) (ha : 0 < a) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hB : ch / (1 - ρ) / a ≤ tB a ρ ch) (hA : tA a ρ ch ≤ ch / (1 - ρ) / a) :
    (∀ τ, 0 < τ → τ ≤ 1 → ch / (1 - ρ) ≤ a * τ → τ ≠ ch / (1 - ρ) / a →
      Psi a ρ ch τ (ch / (1 - ρ)) < Psi a ρ ch (ch / (1 - ρ) / a) (ch / (1 - ρ))) ∧
    (∀ τ, 0 < τ → a * τ < ch / (1 - ρ) →
      Psi a ρ ch τ (a * τ) < Psi a ρ ch (ch / (1 - ρ) / a) (ch / (1 - ρ))) := by
  constructor
  · intro τ _ _ hc hne
    have hgt : ch / (1 - ρ) / a < τ := by
      rcases lt_or_eq_of_le (show ch / (1 - ρ) / a ≤ τ by rw [div_le_iff₀ ha]; linarith) with h | h
      · exact h
      · exact absurd h.symm hne
    rw [psiA_id a ρ ch τ ha hρ hρ1, psiA_id a ρ ch (ch / (1 - ρ) / a) ha hρ hρ1]
    have : (ch / (1 - ρ) / a - tA a ρ ch) ^ 2 < (τ - tA a ρ ch) ^ 2 := by
      apply pow_lt_pow_left₀ (by linarith) (by linarith) two_ne_zero
    nlinarith
  · intro τ _ hτ
    exact P2_gen a ρ ch τ ha hρ hρ1 hB hτ


lemma ev_R {P : ℝ → Prop} {a : ℝ} (h : ∀ᶠ x in nhds a, P x) :
    ∃ R < a, ∀ x, R < x → x ≤ a → P x := by
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨a - ε, by linarith, fun x h1 h2 => hP ?_⟩
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith

lemma ev_δ {P : ℝ → Prop} {c0 : ℝ} (h : ∀ᶠ x in nhds c0, P x) :
    ∃ δ > 0, ∀ x, c0 - δ < x → x < c0 + δ → P x := by
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨ε, hε, fun x h1 h2 => hP ?_⟩
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith

theorem stage2 (a ρ ch ts : ℝ) (ha1 : 1 < a) (hρ0 : a / (2 + a) < ρ) (hρ1 : ρ < 1)
    (hch0 : 0 ≤ ch) (hch1 : ch ≤ (1 - ρ) * a)
    (hts0 : 0 < ts) (hts1 : ts < 1) (hcts : ch / (1 - ρ) ≤ a * ts)
    (hP1 : ∀ τ, 0 < τ → τ ≤ 1 → ch / (1 - ρ) ≤ a * τ → τ ≠ ts →
      Psi a ρ ch τ (ch / (1 - ρ)) < Psi a ρ ch ts (ch / (1 - ρ)))
    (hP2 : ∀ τ, 0 < τ → a * τ < ch / (1 - ρ) →
      Psi a ρ ch τ (a * τ) < Psi a ρ ch ts (ch / (1 - ρ)))
    (F3 : (a + ch / (1 - ρ)) / 2 < a)
    (F4 : 0 < xb a ρ a ch) (F5 : xb a ρ a ch < 1)
    (F6 : Kb a ρ a - ch < Psi a ρ ch ts (ch / (1 - ρ)))
    (F7 : ρ * (1 - xb a ρ a ch) ^ 2 < Psi a ρ ch ts (ch / (1 - ρ)))
    (F8 : (1 - ρ) * ((a * ((a + ch / (1 - ρ)) / 2) - ((a + ch / (1 - ρ)) / 2) ^ 2 / 2 +
        (a - a) ^ 2 / 2) / a) + ρ * (ts - ts ^ 2 / 2) <
      (1 - ρ) * (a / 2) + ρ * (xb a ρ a ch - xb a ρ a ch ^ 2 / 2))
    (F9 : (1 - ts + (a * ts - ch / (1 - ρ)) / (2 * a)) * a < (1 - xb a ρ a ch) * a) :
    ∃ R < a, ∀ rh, R < rh → rh ≤ a →
    (∃ pb, IsBenchOpt a ρ rh ch pb) ∧
    (∃ ph τ pbh pbl, IsFlexEq a ρ rh ch ph τ pbh pbl) ∧
    ∀ pb, IsBenchOpt a ρ rh ch pb → ∀ ph τ pbh pbl, IsFlexEq a ρ rh ch ph τ pbh pbl →
      acq a rh τ ph pbh pbl = (a * ts - ch / (1 - ρ)) / (2 * a) ∧
      benchProfit a ρ rh ch pb < flexProfit a ρ rh ch ph τ pbh pbl ∧
      flexCC a ρ rh ph pbh pbl < benchCC a ρ rh pb ∧
      flexCap a rh τ ph pbh pbl < benchCap a ρ rh pb := by
  have hxc : ContinuousAt (fun rh => xb a ρ rh ch) a := by unfold xb Kb; fun_prop
  have hKc : ContinuousAt (fun rh => Kb a ρ rh) a := by unfold Kb; fun_prop
  have e1 : ∀ᶠ rh in nhds a, (1:ℝ) < rh :=
    ContinuousAt.eventually_lt continuousAt_const continuousAt_id ha1
  have e3 : ∀ᶠ rh in nhds a, (a + ch / (1 - ρ)) / 2 < rh :=
    ContinuousAt.eventually_lt continuousAt_const continuousAt_id F3
  have e4 : ∀ᶠ rh in nhds a, 0 < xb a ρ rh ch :=
    ContinuousAt.eventually_lt continuousAt_const hxc F4
  have e5 : ∀ᶠ rh in nhds a, xb a ρ rh ch < 1 :=
    ContinuousAt.eventually_lt hxc continuousAt_const F5
  have e6 : ∀ᶠ rh in nhds a, Kb a ρ rh - ch < Psi a ρ ch ts (ch / (1 - ρ)) :=
    ContinuousAt.eventually_lt (hKc.sub continuousAt_const) continuousAt_const F6
  have e7 : ∀ᶠ rh in nhds a, ρ * (1 - xb a ρ rh ch) ^ 2 < Psi a ρ ch ts (ch / (1 - ρ)) :=
    ContinuousAt.eventually_lt (by fun_prop) continuousAt_const F7
  have e8 : ∀ᶠ rh in nhds a, (1 - ρ) * ((a * ((a + ch / (1 - ρ)) / 2) - ((a + ch / (1 - ρ)) / 2) ^ 2 / 2 +
        (a - rh) ^ 2 / 2) / a) + ρ * (ts - ts ^ 2 / 2) <
      (1 - ρ) * (a / 2) + ρ * (xb a ρ rh ch - xb a ρ rh ch ^ 2 / 2) :=
    ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) F8
  have e9 : ∀ᶠ rh in nhds a, (1 - ts + (a * ts - ch / (1 - ρ)) / (2 * a)) * rh <
      (1 - xb a ρ rh ch) * rh :=
    ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) F9
  obtain ⟨R, hR, hRP⟩ := ev_R (e1.and (e3.and (e4.and (e5.and (e6.and (e7.and (e8.and e9)))))))
  refine ⟨R, hR, fun rh h1 h2 => ?_⟩
  obtain ⟨g1, g3, g4, g5, g6, g7, g8, g9⟩ := hRP rh h1 h2
  have hS : Standing a ρ rh ch := ⟨ha1, ⟨hρ0, hρ1⟩, ⟨by linarith, h2⟩, ⟨hch0, hch1⟩⟩
  have hca : ch / (1 - ρ) < a := by linarith
  exact inner a ρ rh ch ts hS g1.le g3.le (by linarith) g4 g5 hts0 hts1 hcts hP1 hP2 g6 g7 g8 g9


lemma vals (a ρ : ℝ) (ha : 0 < a) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    a * (1 - ρ) / 2 / (1 - ρ) = a / 2 ∧ tA a ρ (a * (1 - ρ) / 2) = 1 / 2 ∧
    Kb a ρ a = a * (1 - ρ) / 2 ∧ xb a ρ a (a * (1 - ρ) / 2) = 1 / 2 ∧
    Psi a ρ (a * (1 - ρ) / 2) (1 / 2) (a / 2) = ρ / 4 + (1 - ρ) * a / 16 ∧
    tB a ρ (a * (1 - ρ) / 2) = (ρ + 5 * (1 - ρ) * a / 8) / (2 * ρ + (1 - ρ) * a) ∧
    (a * ((a + a / 2) / 2) - ((a + a / 2) / 2) ^ 2 / 2 + (a - a) ^ 2 / 2) / a = 15 * a / 32 := by
  have h1 : (1 - ρ) ≠ 0 := by linarith
  have h2 : 2 * ρ + (1 - ρ) * a ≠ 0 := by nlinarith
  have hK : Kb a ρ a = a * (1 - ρ) / 2 := by unfold Kb; field_simp; ring
  refine ⟨by field_simp, by unfold tA; field_simp; ring, hK, ?_, by unfold Psi; field_simp; ring,
    ?_, by field_simp; ring⟩
  · unfold xb; rw [hK]; field_simp; ring
  · unfold tB; field_simp; ring

theorem branch1 (a ρ : ℝ) (ha1 : 1 < a) (hρ0 : a / (2 + a) < ρ) (hρ1 : ρ < 1)
    (h7 : ρ < 7 * a / (8 + 7 * a)) :
    ∃ δ > 0, ∀ ch : ℝ, a * (1 - ρ) / 2 - δ < ch → ch < a * (1 - ρ) / 2 →
        ∃ R < a, ∀ rh : ℝ, R < rh → rh ≤ a →
          (∃ pb, IsBenchOpt a ρ rh ch pb) ∧
          (∃ ph τ pbh pbl, IsFlexEq a ρ rh ch ph τ pbh pbl) ∧
          ∀ pb, IsBenchOpt a ρ rh ch pb → ∀ ph τ pbh pbl, IsFlexEq a ρ rh ch ph τ pbh pbl →
            0 < acq a rh τ ph pbh pbl ∧
            benchProfit a ρ rh ch pb < flexProfit a ρ rh ch ph τ pbh pbl ∧
            flexCC a ρ rh ph pbh pbl < benchCC a ρ rh pb ∧
            flexCap a rh τ ph pbh pbl < benchCap a ρ rh pb := by
  have ha : 0 < a := by linarith
  have hρ : 0 < ρ := lt_trans (by positivity) hρ0
  have hαa : (1 - ρ) * a < 2 * ρ := by
    rw [div_lt_iff₀ (by linarith)] at hρ0; nlinarith
  have h7' : 8 * ρ < 7 * (1 - ρ) * a := by
    rw [lt_div_iff₀ (by linarith)] at h7; nlinarith
  obtain ⟨v1, v2, v3, v4, v5, v6, v7⟩ := vals a ρ ha hρ hρ1
  set c0 := a * (1 - ρ) / 2 with hc0
  have hc0pos : 0 < c0 := by rw [hc0]; nlinarith
  have hcont : ∀ f : ℝ → ℝ, Continuous f → ContinuousAt f c0 := fun f hf => hf.continuousAt
  have E1 : ∀ᶠ ch in nhds c0, (0:ℝ) < ch :=
    ContinuousAt.eventually_lt continuousAt_const continuousAt_id hc0pos
  have E2 : ∀ᶠ ch in nhds c0, ch < (1 - ρ) * a :=
    ContinuousAt.eventually_lt continuousAt_id continuousAt_const (by rw [hc0]; nlinarith)
  have E3 : ∀ᶠ ch in nhds c0, tA a ρ ch < 1 :=
    ContinuousAt.eventually_lt (by unfold tA; fun_prop) continuousAt_const (by rw [v2]; norm_num)
  have E4 : ∀ᶠ ch in nhds c0, ch / (1 - ρ) / a < tB a ρ ch :=
    ContinuousAt.eventually_lt (by fun_prop) (by unfold tB; fun_prop)
      (by rw [v1, v6, lt_div_iff₀ (by nlinarith)]; field_simp; nlinarith)
  have E5 : ∀ᶠ ch in nhds c0, (a + ch / (1 - ρ)) / 2 < a :=
    ContinuousAt.eventually_lt (by fun_prop) continuousAt_const (by rw [v1]; linarith)
  have E6 : ∀ᶠ ch in nhds c0, 0 < xb a ρ a ch :=
    ContinuousAt.eventually_lt continuousAt_const (by unfold xb; fun_prop) (by rw [v4]; norm_num)
  have E7 : ∀ᶠ ch in nhds c0, xb a ρ a ch < 1 :=
    ContinuousAt.eventually_lt (by unfold xb; fun_prop) continuousAt_const (by rw [v4]; norm_num)
  have E8 : ∀ᶠ ch in nhds c0, Kb a ρ a - ch < Psi a ρ ch (tA a ρ ch) (ch / (1 - ρ)) :=
    ContinuousAt.eventually_lt (by fun_prop) (by unfold Psi tA; fun_prop)
      (by rw [v1, v2, v3, v5]; nlinarith)
  have E9 : ∀ᶠ ch in nhds c0, ρ * (1 - xb a ρ a ch) ^ 2 < Psi a ρ ch (tA a ρ ch) (ch / (1 - ρ)) :=
    ContinuousAt.eventually_lt (by unfold xb; fun_prop) (by unfold Psi tA; fun_prop)
      (by rw [v1, v2, v4, v5]; nlinarith)
  have E10 : ∀ᶠ ch in nhds c0, (1 - ρ) * ((a * ((a + ch / (1 - ρ)) / 2) - ((a + ch / (1 - ρ)) / 2) ^ 2 / 2 +
        (a - a) ^ 2 / 2) / a) + ρ * (tA a ρ ch - tA a ρ ch ^ 2 / 2) <
      (1 - ρ) * (a / 2) + ρ * (xb a ρ a ch - xb a ρ a ch ^ 2 / 2) :=
    ContinuousAt.eventually_lt (by unfold tA; fun_prop) (by unfold xb; fun_prop)
      (by rw [v1, v2, v4, v7]; nlinarith)
  obtain ⟨δ, hδ, hP⟩ := ev_δ (E1.and (E2.and (E3.and (E4.and (E5.and (E6.and (E7.and (E8.and (E9.and E10)))))))))
  refine ⟨δ, hδ, fun ch h1 h2 => ?_⟩
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := hP ch h1 (by linarith)
  have hD1 : a * tA a ρ ch - ch / (1 - ρ) =
      ((1 - ρ) * a - 2 * ch) * (8 * ρ - (1 - ρ) * a) / (16 * ρ * (1 - ρ)) := by
    have : (1 - ρ) ≠ 0 := by linarith
    unfold tA; field_simp; ring
  have hα : 0 < 1 - ρ := sub_pos.2 hρ1
  have f1 : 0 < (1 - ρ) * a - 2 * ch := by rw [hc0] at h2; linarith
  have f2 : 0 < 8 * ρ - (1 - ρ) * a := by linarith
  have f3 : 2 * ch - (1 - ρ) * a < 0 := by linarith
  have f4 : 8 * ρ - 7 * (1 - ρ) * a < 0 := by linarith
  have hD1pos : 0 < a * tA a ρ ch - ch / (1 - ρ) := by
    rw [hD1]; exact div_pos (mul_pos f1 f2) (by positivity)
  have hD2 : (1 - xb a ρ a ch) * a - (1 - tA a ρ ch + (a * tA a ρ ch - ch / (1 - ρ)) / (2 * a)) * a =
      (2 * ch - (1 - ρ) * a) * (8 * ρ - 7 * (1 - ρ) * a) / (32 * ρ * (1 - ρ)) := by
    have : (1 - ρ) ≠ 0 := by linarith
    unfold xb Kb tA; field_simp; ring
  have hD2pos : 0 < (1 - xb a ρ a ch) * a - (1 - tA a ρ ch + (a * tA a ρ ch - ch / (1 - ρ)) / (2 * a)) * a := by
    rw [hD2]; exact div_pos (mul_pos_of_neg_of_neg f3 f4) (by positivity)
  have hc0' : 0 ≤ ch / (1 - ρ) := div_nonneg g1.le (by linarith)
  have hts0 : 0 < tA a ρ ch := by
    by_contra hcon; push_neg at hcon
    have : a * tA a ρ ch ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le hcon
    linarith
  obtain ⟨hP1, hP2⟩ := branch1_P a ρ ch ha hρ hρ1 g4.le
  obtain ⟨R, hR, hRP⟩ := stage2 a ρ ch (tA a ρ ch) ha1 hρ0 hρ1 g1.le g2.le hts0 g3 (by linarith) hP1 hP2
    g5 g6 g7 g8 g9 g10 (by linarith)
  refine ⟨R, hR, fun rh r1 r2 => ?_⟩
  obtain ⟨b1, b2, b3⟩ := hRP rh r1 r2
  refine ⟨b1, b2, fun pb hpb ph τ pbh pbl hE => ?_⟩
  obtain ⟨q1, q2, q3, q4⟩ := b3 pb hpb ph τ pbh pbl hE
  refine ⟨?_, q2, q3, q4⟩
  rw [q1]; exact div_pos hD1pos (by linarith)


theorem branch2 (a ρ : ℝ) (ha1 : 1 < a) (hρ0 : a / (2 + a) < ρ) (hρ1 : ρ < 1) :
    ∃ δ > 0, ∀ ch : ℝ, a * (1 - ρ) / 2 < ch → ch < a * (1 - ρ) / 2 + δ →
        ∃ R < a, ∀ rh : ℝ, R < rh → rh ≤ a →
          (∃ pb, IsBenchOpt a ρ rh ch pb) ∧
          (∃ ph τ pbh pbl, IsFlexEq a ρ rh ch ph τ pbh pbl) ∧
          ∀ pb, IsBenchOpt a ρ rh ch pb → ∀ ph τ pbh pbl, IsFlexEq a ρ rh ch ph τ pbh pbl →
            acq a rh τ ph pbh pbl = 0 ∧
            benchProfit a ρ rh ch pb < flexProfit a ρ rh ch ph τ pbh pbl ∧
            flexCC a ρ rh ph pbh pbl < benchCC a ρ rh pb ∧
            flexCap a rh τ ph pbh pbl < benchCap a ρ rh pb := by
  have ha : 0 < a := by linarith
  have hρ : 0 < ρ := lt_trans (by positivity) hρ0
  have hαa : (1 - ρ) * a < 2 * ρ := by
    rw [div_lt_iff₀ (by linarith)] at hρ0; nlinarith
  obtain ⟨v1, v2, v3, v4, v5, v6, v7⟩ := vals a ρ ha hρ hρ1
  have v8 : a / 2 / a = 1 / 2 := by field_simp
  set c0 := a * (1 - ρ) / 2 with hc0
  have hc0pos : 0 < c0 := by rw [hc0]; nlinarith
  have E1 : ∀ᶠ ch in nhds c0, (0:ℝ) < ch :=
    ContinuousAt.eventually_lt continuousAt_const continuousAt_id hc0pos
  have E2 : ∀ᶠ ch in nhds c0, ch < (1 - ρ) * a :=
    ContinuousAt.eventually_lt continuousAt_id continuousAt_const (by rw [hc0]; nlinarith)
  have E3 : ∀ᶠ ch in nhds c0, ch / (1 - ρ) / a < 1 :=
    ContinuousAt.eventually_lt (by fun_prop) continuousAt_const (by rw [v1, v8]; norm_num)
  have E4 : ∀ᶠ ch in nhds c0, ch / (1 - ρ) / a < tB a ρ ch :=
    ContinuousAt.eventually_lt (by fun_prop) (by unfold tB; fun_prop)
      (by rw [v1, v6, lt_div_iff₀ (by nlinarith)]; field_simp; nlinarith)
  have E5 : ∀ᶠ ch in nhds c0, (a + ch / (1 - ρ)) / 2 < a :=
    ContinuousAt.eventually_lt (by fun_prop) continuousAt_const (by rw [v1]; linarith)
  have E6 : ∀ᶠ ch in nhds c0, 0 < xb a ρ a ch :=
    ContinuousAt.eventually_lt continuousAt_const (by unfold xb; fun_prop) (by rw [v4]; norm_num)
  have E7 : ∀ᶠ ch in nhds c0, xb a ρ a ch < 1 :=
    ContinuousAt.eventually_lt (by unfold xb; fun_prop) continuousAt_const (by rw [v4]; norm_num)
  have E8 : ∀ᶠ ch in nhds c0, Kb a ρ a - ch < Psi a ρ ch (ch / (1 - ρ) / a) (ch / (1 - ρ)) :=
    ContinuousAt.eventually_lt (by fun_prop) (by unfold Psi; fun_prop)
      (by rw [v1, v8, v3, v5]; nlinarith)
  have E9 : ∀ᶠ ch in nhds c0, ρ * (1 - xb a ρ a ch) ^ 2 < Psi a ρ ch (ch / (1 - ρ) / a) (ch / (1 - ρ)) :=
    ContinuousAt.eventually_lt (by unfold xb; fun_prop) (by unfold Psi; fun_prop)
      (by rw [v1, v8, v4, v5]; nlinarith)
  have E10 : ∀ᶠ ch in nhds c0, (1 - ρ) * ((a * ((a + ch / (1 - ρ)) / 2) - ((a + ch / (1 - ρ)) / 2) ^ 2 / 2 +
        (a - a) ^ 2 / 2) / a) + ρ * (ch / (1 - ρ) / a - (ch / (1 - ρ) / a) ^ 2 / 2) <
      (1 - ρ) * (a / 2) + ρ * (xb a ρ a ch - xb a ρ a ch ^ 2 / 2) :=
    ContinuousAt.eventually_lt (by fun_prop) (by unfold xb; fun_prop)
      (by rw [v1, v8, v4, v7]; nlinarith)
  obtain ⟨δ, hδ, hP⟩ := ev_δ (E1.and (E2.and (E3.and (E4.and (E5.and (E6.and (E7.and (E8.and (E9.and E10)))))))))
  refine ⟨δ, hδ, fun ch h1 h2 => ?_⟩
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := hP ch (by linarith) h2
  have hα : 0 < 1 - ρ := sub_pos.2 hρ1
  have f1 : (1 - ρ) * a - 2 * ch < 0 := by rw [hc0] at h1; linarith
  have f2 : 0 < 8 * ρ - (1 - ρ) * a := by linarith
  have f3 : 0 < 2 * ch - (1 - ρ) * a := by linarith
  have f4 : 0 < 2 * ρ - (1 - ρ) * a := by linarith
  have hD1 : a * tA a ρ ch - ch / (1 - ρ) =
      ((1 - ρ) * a - 2 * ch) * (8 * ρ - (1 - ρ) * a) / (16 * ρ * (1 - ρ)) := by
    have : (1 - ρ) ≠ 0 := by linarith
    unfold tA; field_simp; ring
  have hD1neg : a * tA a ρ ch - ch / (1 - ρ) < 0 := by
    rw [hD1]; exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos f1 f2) (by positivity)
  have hA : tA a ρ ch ≤ ch / (1 - ρ) / a := by rw [le_div_iff₀ ha]; linarith
  have hat : a * (ch / (1 - ρ) / a) = ch / (1 - ρ) := by field_simp
  have hD2 : (1 - xb a ρ a ch) * a - (1 - ch / (1 - ρ) / a +
      (a * (ch / (1 - ρ) / a) - ch / (1 - ρ)) / (2 * a)) * a =
      (2 * ch - (1 - ρ) * a) * (2 * ρ - (1 - ρ) * a) / (4 * ρ * (1 - ρ)) := by
    have : (1 - ρ) ≠ 0 := by linarith
    unfold xb Kb; field_simp; ring
  have hD2pos : 0 < (1 - xb a ρ a ch) * a - (1 - ch / (1 - ρ) / a +
      (a * (ch / (1 - ρ) / a) - ch / (1 - ρ)) / (2 * a)) * a := by
    rw [hD2]; exact div_pos (mul_pos f3 f4) (by positivity)
  have hts0 : 0 < ch / (1 - ρ) / a := div_pos (div_pos g1 hα) ha
  obtain ⟨hP1, hP2⟩ := branch2_P a ρ ch ha hρ hρ1 g4.le hA
  obtain ⟨R, hR, hRP⟩ := stage2 a ρ ch (ch / (1 - ρ) / a) ha1 hρ0 hρ1 g1.le g2.le hts0 g3 hat.ge hP1 hP2
    g5 g6 g7 g8 g9 g10 (by linarith)
  refine ⟨R, hR, fun rh r1 r2 => ?_⟩
  obtain ⟨b1, b2, b3⟩ := hRP rh r1 r2
  refine ⟨b1, b2, fun pb hpb ph τ pbh pbl hE => ?_⟩
  obtain ⟨q1, q2, q3, q4⟩ := b3 pb hpb ph τ pbh pbl hE
  refine ⟨?_, q2, q3, q4⟩
  rw [q1, hat]; simp

end BL6

open BL6 in
theorem solution (a ρ : ℝ) (ha : 1 < a) (hρ0 : a / (2 + a) < ρ) (hρ1 : ρ < 1) :
    (ρ < 7 * a / (8 + 7 * a) →
      ∃ δ > 0, ∀ ch : ℝ, a * (1 - ρ) / 2 - δ < ch → ch < a * (1 - ρ) / 2 →
        ∃ R < a, ∀ rh : ℝ, R < rh → rh ≤ a →
          (∃ pb, IsBenchOpt a ρ rh ch pb) ∧
          (∃ ph τ pbh pbl, IsFlexEq a ρ rh ch ph τ pbh pbl) ∧
          ∀ pb, IsBenchOpt a ρ rh ch pb → ∀ ph τ pbh pbl, IsFlexEq a ρ rh ch ph τ pbh pbl →
            0 < acq a rh τ ph pbh pbl ∧
            benchProfit a ρ rh ch pb < flexProfit a ρ rh ch ph τ pbh pbl ∧
            flexCC a ρ rh ph pbh pbl < benchCC a ρ rh pb ∧
            flexCap a rh τ ph pbh pbl < benchCap a ρ rh pb) ∧
    (∃ δ > 0, ∀ ch : ℝ, a * (1 - ρ) / 2 < ch → ch < a * (1 - ρ) / 2 + δ →
        ∃ R < a, ∀ rh : ℝ, R < rh → rh ≤ a →
          (∃ pb, IsBenchOpt a ρ rh ch pb) ∧
          (∃ ph τ pbh pbl, IsFlexEq a ρ rh ch ph τ pbh pbl) ∧
          ∀ pb, IsBenchOpt a ρ rh ch pb → ∀ ph τ pbh pbl, IsFlexEq a ρ rh ch ph τ pbh pbl →
            acq a rh τ ph pbh pbl = 0 ∧
            benchProfit a ρ rh ch pb < flexProfit a ρ rh ch ph τ pbh pbl ∧
            flexCC a ρ rh ph pbh pbl < benchCC a ρ rh pb ∧
            flexCap a rh τ ph pbh pbl < benchCap a ρ rh pb) :=
  ⟨branch1 a ρ ha hρ0 hρ1, branch2 a ρ ha hρ0 hρ1⟩
