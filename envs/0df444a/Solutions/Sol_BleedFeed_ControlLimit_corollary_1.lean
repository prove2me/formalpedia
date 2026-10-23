-- Prove2me | solution 1 for BleedFeed.ControlLimit.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T17:31:05.942198+00:00
-- url     : https://prove2.me/submissions/17180d49-f7f6-4263-bd8f-7bab6d3a81a0

import Mathlib
import Definitions.Def_BleedFeed_ControlLimit_Model

set_option autoImplicit false

namespace BleedFeed.ControlLimit

theorem cl_W_eq (P : Params) (b μ : ℝ) (i : ℕ) :
    W P b μ i = if P.I ≤ i then 0 else max (Ck P b i μ) b := by
  rw [W]; rfl

theorem cl_W_of_ge (P : Params) {b μ : ℝ} {i : ℕ} (h : P.I ≤ i) : W P b μ i = 0 := by
  rw [cl_W_eq, if_pos h]

theorem cl_W_of_lt (P : Params) {b μ : ℝ} {i : ℕ} (h : i < P.I) :
    W P b μ i = max (Ck P b i μ) b := by
  rw [cl_W_eq, if_neg (by omega)]

theorem cl_Ck_eq (P : Params) (b μ : ℝ) (i : ℕ) :
    Ck P b i μ = r P i μ + p P i μ * W P b μ (i + 1) := rfl

theorem cl_r_eq (P : Params) (i : ℕ) (μ : ℝ) :
    r P i μ = P.m0 * (1 + μ * P.tau) ^ i * (μ * P.tau) := by
  unfold r mass; ring

theorem cl_r_succ (P : Params) (i : ℕ) (μ : ℝ) :
    r P (i + 1) μ = (1 + μ * P.tau) * r P i μ := by
  rw [cl_r_eq, cl_r_eq]; ring

theorem cl_mass_succ (P : Params) (i : ℕ) (μ : ℝ) :
    mass P (i + 1) μ = (1 + μ * P.tau) * mass P i μ := by
  unfold mass; ring

theorem cl_r_pos (P : Params) (hS : P.Standing) {μ : ℝ} (hμ : 0 < μ) (i : ℕ) :
    0 < r P i μ := by
  obtain ⟨hm0, hτ, -⟩ := id hS
  have h1 : 0 < 1 + μ * P.tau := by have := mul_pos hμ hτ; linarith
  rw [cl_r_eq]
  exact mul_pos (mul_pos hm0 (pow_pos h1 _)) (mul_pos hμ hτ)

theorem cl_mass_pos (P : Params) (hS : P.Standing) {μ : ℝ} (hμ : 0 < μ) (i : ℕ) :
    0 < mass P i μ := by
  obtain ⟨hm0, hτ, -⟩ := id hS
  have h1 : 0 < 1 + μ * P.tau := by have := mul_pos hμ hτ; linarith
  unfold mass
  exact mul_pos hm0 (pow_pos h1 _)

theorem cl_r_mono (P : Params) (hS : P.Standing) {μ : ℝ} (hμ : 0 < μ) {i j : ℕ} (hij : i ≤ j) :
    r P i μ ≤ r P j μ := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih =>
    rw [cl_r_succ]
    have h1 := cl_r_pos P hS hμ k
    have h2 : 0 < μ * P.tau := mul_pos hμ hS.2.1
    nlinarith

theorem cl_mass_le_succ (P : Params) (hS : P.Standing) {μ : ℝ} (hμ : 0 < μ) (i : ℕ) :
    mass P i μ ≤ mass P (i + 1) μ := by
  rw [cl_mass_succ]
  have h1 := cl_mass_pos P hS hμ i
  have h2 : 0 < μ * P.tau := mul_pos hμ hS.2.1
  nlinarith

theorem cl_mass_mono_rate (P : Params) (hS : P.Standing) {μ μ' : ℝ} (hμ : 0 < μ) (hle : μ ≤ μ')
    (i : ℕ) : mass P i μ ≤ mass P i μ' := by
  obtain ⟨hm0, hτ, -⟩ := id hS
  unfold mass
  have h0 : 0 ≤ 1 + μ * P.tau := by nlinarith [mul_pos hμ hτ]
  have h1 : 1 + μ * P.tau ≤ 1 + μ' * P.tau := by nlinarith [mul_le_mul_of_nonneg_right hle hτ.le]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 i) hm0.le

theorem cl_nu_nonneg (P : Params) (hS : P.Standing) (m : ℝ) : 0 ≤ P.nu m := by
  obtain ⟨-, -, -, -, -, -, hν0, hνm, -⟩ := id hS
  rcases le_or_gt m P.mtil with h | h
  · rw [hν0 m h]
  · have := hνm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h.le) h
    rw [hν0 _ le_rfl] at this; linarith

theorem cl_nu_mono (P : Params) (hS : P.Standing) {a c : ℝ} (h : a ≤ c) : P.nu a ≤ P.nu c := by
  have hn := cl_nu_nonneg P hS c
  obtain ⟨-, -, -, -, -, -, hν0, hνm, -⟩ := id hS
  rcases le_or_gt a P.mtil with ha | ha
  · rw [hν0 a ha]; exact hn
  · exact hνm.monotoneOn (Set.mem_Ici.mpr ha.le) (Set.mem_Ici.mpr (ha.le.trans h)) h

theorem cl_p_nonneg (P : Params) (hS : P.Standing) (i : ℕ) (μ : ℝ) : 0 ≤ p P i μ := by
  obtain ⟨-, -, -, -, -, -, -, -, hντ, -⟩ := id hS
  have := hντ (mass P i μ)
  unfold p; linarith

theorem cl_p_le_one (P : Params) (hS : P.Standing) (i : ℕ) (μ : ℝ) : p P i μ ≤ 1 := by
  have h1 := cl_nu_nonneg P hS (mass P i μ)
  have h2 := hS.2.1
  have := mul_nonneg h1 h2.le
  unfold p; linarith

theorem cl_W_ge (P : Params) (b μ : ℝ) {i : ℕ} (hi : i < P.I) : b ≤ W P b μ i := by
  rw [cl_W_of_lt P hi]; exact le_max_right _ _

theorem cl_W_nonneg (P : Params) (b μ : ℝ) (hb : 0 ≤ b) (i : ℕ) : 0 ≤ W P b μ i := by
  rw [cl_W_eq]; split_ifs
  · exact le_rfl
  · exact hb.trans (le_max_right _ _)

theorem cl_Ck_last (P : Params) (b μ : ℝ) (hI : 1 ≤ P.I) :
    Ck P b (P.I - 1) μ = r P (P.I - 1) μ := by
  rw [cl_Ck_eq, cl_W_of_ge P (show P.I ≤ P.I - 1 + 1 by omega)]; ring

/-- One-step-lookahead stopping set (with the last age always included). -/
def cl_good (P : Params) (b μ : ℝ) (i : ℕ) : Prop :=
  P.I ≤ i + 1 ∨ r P i μ ≤ (1 - p P i μ) * b

theorem cl_good_succ (P : Params) (hS : P.Standing) (h4 : Condition4 P) {μ b : ℝ}
    (hμ : μ ∈ P.rates) (hb : r P (P.I - 1) μ ≤ b) {j : ℕ} (hj : cl_good P b μ j) :
    cl_good P b μ (j + 1) := by
  rcases hj with hj | hj
  · left; omega
  by_cases hjI : P.I ≤ j + 1 + 1
  · left; exact hjI
  right
  obtain ⟨-, hτ, hμL, -, -, -, hν0, -⟩ := id hS
  have hμ0 : 0 < μ := lt_of_lt_of_le hμL hμ.1
  have hr0 := cl_r_pos P hS hμ0 j
  have hr1 := cl_r_pos P hS hμ0 (j + 1)
  have hr1b : r P (j + 1) μ ≤ b := (cl_r_mono P hS hμ0 (by omega : j + 1 ≤ P.I - 1)).trans hb
  have hbpos : 0 < b := lt_of_lt_of_le hr1 hr1b
  have hq : 0 < 1 - p P j μ := by
    by_contra hc
    push Not at hc
    nlinarith
  have hmass : P.mtil < mass P j μ := by
    by_contra hc
    push Not at hc
    unfold p at hq; rw [hν0 _ hc] at hq; simp at hq
  have hcrit : critAge P μ ≤ j + 1 :=
    (Nat.sInf_le (show j ∈ {i : ℕ | P.mtil < mass P i μ} from hmass)).trans (Nat.le_succ j)
  have h := h4 μ hμ (j + 1) hcrit (by omega)
  simp only [Nat.add_sub_cancel] at h
  rw [div_le_iff₀ hr1] at h
  have hx : 0 ≤ p P j μ - p P (j + 1) μ := by
    have := cl_nu_mono P hS (cl_mass_le_succ P hS hμ0 j)
    unfold p; nlinarith [mul_le_mul_of_nonneg_right this hτ.le]
  nlinarith [mul_le_mul_of_nonneg_left hr1b hx]

theorem cl_good_mono (P : Params) (hS : P.Standing) (h4 : Condition4 P) {μ b : ℝ}
    (hμ : μ ∈ P.rates) (hb : r P (P.I - 1) μ ≤ b) {i j : ℕ} (hi : cl_good P b μ i) (hij : i ≤ j) :
    cl_good P b μ j := by
  induction j, hij using Nat.le_induction with
  | base => exact hi
  | succ k _ ih => exact cl_good_succ P hS h4 hμ hb ih

theorem cl_Ck_le_of_good (P : Params) (hS : P.Standing) (h4 : Condition4 P) {μ b : ℝ}
    (hμ : μ ∈ P.rates) (hb : r P (P.I - 1) μ ≤ b) :
    ∀ d i, i + d + 1 = P.I → cl_good P b μ i → Ck P b i μ ≤ b := by
  intro d
  induction d with
  | zero =>
    intro i hi _
    rw [cl_Ck_eq, cl_W_of_ge P (show P.I ≤ i + 1 by omega), mul_zero, add_zero,
      show i = P.I - 1 by omega]
    exact hb
  | succ d ih =>
    intro i hi hg
    have hg1 := cl_good_succ P hS h4 hμ hb hg
    have h1 := ih (i + 1) (by omega) hg1
    have hW : W P b μ (i + 1) = b := by
      rw [cl_W_of_lt P (show i + 1 < P.I by omega)]; exact max_eq_right h1
    rw [cl_Ck_eq, hW]
    rcases hg with hg | hg
    · exfalso; omega
    · nlinarith

theorem cl_lt_Ck_of_not_good (P : Params) (hS : P.Standing) {μ b : ℝ} {i : ℕ}
    (hg : ¬ cl_good P b μ i) : b < Ck P b i μ := by
  unfold cl_good at hg
  push Not at hg
  obtain ⟨h1, h2⟩ := hg
  have hW := cl_W_ge P b μ (i := i + 1) h1
  have hp := cl_p_nonneg P hS i μ
  rw [cl_Ck_eq]
  nlinarith [mul_le_mul_of_nonneg_left hW hp]

theorem cl_hb (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) {μ : ℝ} (hμ : μ ∈ P.rates)
    {n : ℕ} (hn : n < P.N) : r P (P.I - 1) μ ≤ B P n := by
  have := (hA1 μ hμ n hn).2
  unfold C at this
  rwa [cl_Ck_last P _ _ hS.2.2.2.2.1] at this

theorem cl_bleed_iff (P : Params) (hS : P.Standing) (h4 : Condition4 P) (hA1 : Assumption1 P)
    {μ : ℝ} (hμ : μ ∈ P.rates) {n : ℕ} (hn : n < P.N) {i : ℕ} (hi : i < P.I) :
    BleedOpt P i μ n ↔ cl_good P (B P n) μ i := by
  constructor
  · intro h
    by_contra hg
    have := cl_lt_Ck_of_not_good P hS hg
    exact absurd h.2 (not_le.mpr this)
  · intro hg
    exact ⟨hn, cl_Ck_le_of_good P hS h4 hμ (cl_hb P hS hA1 hμ hn) (P.I - i - 1) i (by omega) hg⟩

theorem cl_Ck_zero_nonneg (P : Params) (hS : P.Standing) {μ : ℝ} (hμ : μ ∈ P.rates) (i : ℕ) :
    0 ≤ Ck P 0 i μ := by
  have hμ0 : 0 < μ := lt_of_lt_of_le hS.2.2.1 hμ.1
  have h1 := cl_r_pos P hS hμ0 i
  have h2 := cl_W_nonneg P 0 μ le_rfl (i + 1)
  have h3 := cl_p_nonneg P hS i μ
  rw [cl_Ck_eq]
  nlinarith [mul_nonneg h3 h2]

theorem cl_cont_N (P : Params) (hS : P.Standing) {μ : ℝ} (hμ : μ ∈ P.rates) (i : ℕ) :
    ContOpt P i μ P.N := by
  have hB : B P P.N = 0 := by simp [B, Bk]
  unfold ContOpt C
  rw [hB]
  exact cl_Ck_zero_nonneg P hS hμ i

theorem cl_good_rate (P : Params) (hS : P.Standing) (h5 : Condition5 P) (hA1 : Assumption1 P)
    {n : ℕ} (hn : n < P.N) {i : ℕ} {μ μ' : ℝ} (hμ : μ ∈ P.rates) (hμ' : μ' ∈ P.rates)
    (hle : μ ≤ μ') (hg : cl_good P (B P n) μ i) : cl_good P (B P n) μ' i := by
  rcases hg with hg | hg
  · exact Or.inl hg
  by_cases hiI : P.I ≤ i + 1
  · exact Or.inl hiI
  right
  obtain ⟨-, hτ, hμL, -, -, -, hν0, -⟩ := id hS
  have hμ0 : 0 < μ := lt_of_lt_of_le hμL hμ.1
  have hμ0' : 0 < μ' := lt_of_lt_of_le hμL hμ'.1
  have hb' := cl_hb P hS hA1 hμ' hn
  have hr := cl_r_pos P hS hμ0 i
  have hr1' : r P (i + 1) μ' ≤ B P n :=
    (cl_r_mono P hS hμ0' (by omega : i + 1 ≤ P.I - 1)).trans hb'
  have hbpos : 0 < B P n := lt_of_lt_of_le (cl_r_pos P hS hμ0' _) hr1'
  have hq : 0 < 1 - p P i μ := by
    by_contra hc
    push Not at hc
    nlinarith
  have hmass : P.mtil < mass P i μ := by
    by_contra hc
    push Not at hc
    unfold p at hq; rw [hν0 _ hc] at hq; simp at hq
  have hmm : mass P i μ ≤ mass P i μ' := cl_mass_mono_rate P hS hμ0 hle i
  have hcrit : critAge P μ' < i + 1 :=
    Nat.lt_succ_of_le (Nat.sInf_le (show i ∈ {k : ℕ | P.mtil < mass P k μ'} from
      lt_of_lt_of_le hmass hmm))
  have h := h5 μ hμ μ' hμ' hle (i + 1) hcrit (by omega)
  simp only [Nat.add_sub_cancel] at h
  rw [div_le_iff₀ (cl_r_pos P hS hμ0' _)] at h
  have hx : 0 ≤ p P i μ - p P i μ' := by
    have := cl_nu_mono P hS hmm
    unfold p; nlinarith [mul_le_mul_of_nonneg_right this hτ.le]
  nlinarith [mul_le_mul_of_nonneg_left hr1' hx]

/-! Monotonicity of the bleed–feed value in the number of remaining bleed–feeds. -/

theorem cl_W_mono (P : Params) (hS : P.Standing) (μ : ℝ) {b b' : ℝ} (hbb : b ≤ b') :
    ∀ d i, P.I ≤ i + d → W P b μ i ≤ W P b' μ i := by
  intro d
  induction d with
  | zero =>
    intro i hi
    rw [cl_W_of_ge P (show P.I ≤ i by omega), cl_W_of_ge P (show P.I ≤ i by omega)]
  | succ d ih =>
    intro i hi
    by_cases h : P.I ≤ i
    · rw [cl_W_of_ge P h, cl_W_of_ge P h]
    · rw [cl_W_of_lt P (show i < P.I by omega), cl_W_of_lt P (show i < P.I by omega),
        cl_Ck_eq, cl_Ck_eq]
      exact max_le_max (add_le_add le_rfl (mul_le_mul_of_nonneg_left (ih (i + 1) (by omega))
        (cl_p_nonneg P hS i μ))) hbb

theorem cl_Ck_mono (P : Params) (hS : P.Standing) (μ : ℝ) {b b' : ℝ} (h : b ≤ b') (i : ℕ) :
    Ck P b i μ ≤ Ck P b' i μ := by
  rw [cl_Ck_eq, cl_Ck_eq]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (cl_W_mono P hS μ h P.I (i + 1) (by omega)) (cl_p_nonneg P hS i μ))

theorem cl_meas_r (P : Params) (i : ℕ) : Measurable (fun μ => r P i μ) := by
  unfold r mass; fun_prop

theorem cl_meas_p (P : Params) (hS : P.Standing) (i : ℕ) : Measurable (fun μ => p P i μ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hνm, -⟩ := id hS
  have hm : Measurable (fun μ => mass P i μ) := by unfold mass; fun_prop
  unfold p
  exact measurable_const.sub ((hνm.comp hm).mul measurable_const)

theorem cl_meas_W (P : Params) (hS : P.Standing) (b : ℝ) :
    ∀ d i, P.I ≤ i + d → Measurable (fun μ => W P b μ i) := by
  intro d
  induction d with
  | zero =>
    intro i hi
    simp only [cl_W_of_ge P (show P.I ≤ i by omega)]
    exact measurable_const
  | succ d ih =>
    intro i hi
    by_cases h : P.I ≤ i
    · simp only [cl_W_of_ge P h]
      exact measurable_const
    · simp only [cl_W_of_lt P (show i < P.I by omega), cl_Ck_eq]
      exact ((cl_meas_r P i).add ((cl_meas_p P hS i).mul (ih (i + 1) (by omega)))).max
        measurable_const

noncomputable def cl_K (P : Params) : ℝ := P.m0 * (1 + P.muU * P.tau) ^ P.I * (P.muU * P.tau)

theorem cl_r_le (P : Params) (hS : P.Standing) {μ : ℝ} (hμ : μ ∈ P.rates) {j : ℕ}
    (hj : j ≤ P.I) : |r P j μ| ≤ cl_K P := by
  obtain ⟨hm0, hτ, hμL, -⟩ := id hS
  have hμ0 : 0 < μ := lt_of_lt_of_le hμL hμ.1
  rw [abs_of_pos (cl_r_pos P hS hμ0 j), cl_r_eq, cl_K]
  have h1 : 1 ≤ 1 + μ * P.tau := by nlinarith [mul_pos hμ0 hτ]
  have h2 : 1 + μ * P.tau ≤ 1 + P.muU * P.tau := by
    nlinarith [mul_le_mul_of_nonneg_right hμ.2 hτ.le]
  have h3 : (1 + μ * P.tau) ^ j ≤ (1 + P.muU * P.tau) ^ P.I :=
    (pow_le_pow_left₀ (by linarith) h2 j).trans (pow_le_pow_right₀ (by linarith) hj)
  have h4 : μ * P.tau ≤ P.muU * P.tau := mul_le_mul_of_nonneg_right hμ.2 hτ.le
  exact mul_le_mul (mul_le_mul_of_nonneg_left h3 hm0.le) h4 (mul_pos hμ0 hτ).le
    (mul_nonneg hm0.le (pow_nonneg (by linarith) _))

theorem cl_K_nonneg (P : Params) (hS : P.Standing) {μ : ℝ} (hμ : μ ∈ P.rates) : 0 ≤ cl_K P :=
  (abs_nonneg _).trans (cl_r_le P hS hμ (Nat.zero_le _))

theorem cl_abs_Ck (P : Params) (hS : P.Standing) {μ : ℝ} (hμ : μ ∈ P.rates) (b : ℝ) {i : ℕ}
    (hi : i ≤ P.I) : |Ck P b i μ| ≤ cl_K P + |W P b μ (i + 1)| := by
  rw [cl_Ck_eq]
  have h1 := cl_r_le P hS hμ hi
  have hp0 := cl_p_nonneg P hS i μ
  have hp1 := cl_p_le_one P hS i μ
  have h2 : |p P i μ * W P b μ (i + 1)| ≤ |W P b μ (i + 1)| := by
    rw [abs_mul, abs_of_nonneg hp0]
    exact mul_le_of_le_one_left (abs_nonneg _) hp1
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem cl_W_bound (P : Params) (hS : P.Standing) {μ : ℝ} (hμ : μ ∈ P.rates) (b : ℝ) :
    ∀ d i, P.I ≤ i + d → |W P b μ i| ≤ (d : ℝ) * cl_K P + |b| := by
  have hK := cl_K_nonneg P hS hμ
  intro d
  induction d with
  | zero =>
    intro i hi
    rw [cl_W_of_ge P (show P.I ≤ i by omega)]
    simp
  | succ d ih =>
    intro i hi
    by_cases h : P.I ≤ i
    · rw [cl_W_of_ge P h]
      simp only [abs_zero]
      positivity
    · rw [cl_W_of_lt P (show i < P.I by omega)]
      have hC := (cl_abs_Ck P hS hμ b (show i ≤ P.I by omega)).trans
        (add_le_add le_rfl (ih (i + 1) (by omega)))
      have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      push_cast
      have hb0 := abs_nonneg b
      rw [abs_le] at hC ⊢
      have hnb := neg_abs_le b
      have hlb := le_abs_self b
      have hdK := mul_nonneg hd hK
      constructor
      · exact le_trans (by nlinarith) (le_max_right _ _)
      · exact max_le (by nlinarith) (by nlinarith)

theorem cl_integrable (P : Params) (hS : P.Standing) (b : ℝ) :
    MeasureTheory.Integrable (fun μ' => Ck P b 0 μ') P.G := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGp, hG0⟩ := id hS
  have := hGp
  have hmeas : Measurable (fun μ' => Ck P b 0 μ') := by
    simp only [cl_Ck_eq]
    exact (cl_meas_r P 0).add ((cl_meas_p P hS 0).mul (cl_meas_W P hS b P.I 1 (by omega)))
  have hae : ∀ᵐ μ ∂P.G, μ ∈ P.rates := MeasureTheory.ae_iff.2 hG0
  refine MeasureTheory.Integrable.mono'
    (MeasureTheory.integrable_const (cl_K P + ((P.I : ℝ) * cl_K P + |b|)))
    hmeas.aestronglyMeasurable ?_
  filter_upwards [hae] with μ hμ
  rw [Real.norm_eq_abs]
  exact (cl_abs_Ck P hS hμ b (Nat.zero_le _)).trans
    (add_le_add le_rfl (cl_W_bound P hS hμ b P.I 1 (by omega)))

theorem cl_Bk_succ (P : Params) (k : ℕ) : Bk P (k + 1) = ∫ μ', Ck P (Bk P k) 0 μ' ∂P.G := rfl

theorem cl_Bk_mono_succ (P : Params) (hS : P.Standing) : ∀ k, Bk P k ≤ Bk P (k + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hG0⟩ := id hS
  have hae : ∀ᵐ μ ∂P.G, μ ∈ P.rates := MeasureTheory.ae_iff.2 hG0
  intro k
  induction k with
  | zero =>
    rw [cl_Bk_succ, show Bk P 0 = 0 from rfl]
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [hae] with μ hμ
    exact cl_Ck_zero_nonneg P hS hμ 0
  | succ k ih =>
    rw [cl_Bk_succ P (k + 1), cl_Bk_succ P k]
    exact MeasureTheory.integral_mono (cl_integrable P hS _) (cl_integrable P hS _)
      (fun μ => cl_Ck_mono P hS μ ih 0)

theorem cl_B_anti (P : Params) (hS : P.Standing) {k n : ℕ} (hkn : k ≤ n) : B P n ≤ B P k := by
  unfold B
  exact monotone_nat_of_le_succ (cl_Bk_mono_succ P hS) (by omega : P.N - n ≤ P.N - k)

theorem cl_good_count (P : Params) (hS : P.Standing) {k n i : ℕ} {μ : ℝ} (hkn : k ≤ n)
    (hg : cl_good P (B P n) μ i) : cl_good P (B P k) μ i := by
  rcases hg with hg | hg
  · exact Or.inl hg
  · right
    have hB : B P n ≤ B P k := cl_B_anti P hS hkn
    have hq : 0 ≤ 1 - p P i μ := by have := cl_p_le_one P hS i μ; linarith
    exact hg.trans (mul_le_mul_of_nonneg_left hB hq)

end BleedFeed.ControlLimit

open BleedFeed.ControlLimit in
theorem solution (P : Params) (hS : P.Standing)
    (h4 : Condition4 P) (h5 : Condition5 P) (hA1 : Assumption1 P) :
    (∀ μ ∈ P.rates, ∀ n ≤ P.N, ∃ iStar : ℤ, ∀ i < P.I,
        ((i : ℤ) ≤ iStar → ContOpt P i μ n) ∧ (iStar < i → BleedOpt P i μ n)) ∧
    (∀ i < P.I, ∀ n ≤ P.N, ∃ μStar : ℝ, ∀ μ ∈ P.rates,
        (μ < μStar → ContOpt P i μ n) ∧ (μStar < μ → BleedOpt P i μ n)) ∧
    (∀ i < P.I, ∀ μ ∈ P.rates, ∃ nStar : ℤ, ∀ n ≤ P.N,
        ((n : ℤ) ≤ nStar → BleedOpt P i μ n) ∧ (nStar < n → ContOpt P i μ n)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro μ hμ n hn
    rcases lt_or_eq_of_le hn with hn | hn
    · have hb := cl_hb P hS hA1 hμ hn
      have hex : ∃ k, cl_good P (B P n) μ k := ⟨P.I - 1, Or.inl (by omega)⟩
      refine ⟨(Nat.find hex : ℤ) - 1, fun i hi => ⟨fun hle => ?_, fun hlt => ?_⟩⟩
      · have hlt : i < Nat.find hex := by omega
        exact (cl_lt_Ck_of_not_good P hS (Nat.find_min hex hlt)).le
      · have hle : Nat.find hex ≤ i := by omega
        exact (cl_bleed_iff P hS h4 hA1 hμ hn hi).2
          (cl_good_mono P hS h4 hμ hb (Nat.find_spec hex) hle)
    · subst hn
      exact ⟨P.I, fun i hi => ⟨fun _ => cl_cont_N P hS hμ i, fun h => absurd h (by omega)⟩⟩
  · intro i hi n hn
    rcases lt_or_eq_of_le hn with hn | hn
    · by_cases hne : ({μ | μ ∈ P.rates ∧ cl_good P (B P n) μ i} : Set ℝ).Nonempty
      · have hbdd : BddBelow ({μ | μ ∈ P.rates ∧ cl_good P (B P n) μ i} : Set ℝ) :=
          ⟨P.muL, fun x hx => hx.1.1⟩
        refine ⟨sInf {μ | μ ∈ P.rates ∧ cl_good P (B P n) μ i}, fun μ hμ =>
          ⟨fun hlt => ?_, fun hlt => ?_⟩⟩
        · have hg : ¬ cl_good P (B P n) μ i := fun hg =>
            absurd (csInf_le hbdd ⟨hμ, hg⟩) (not_le.mpr hlt)
          exact (cl_lt_Ck_of_not_good P hS hg).le
        · obtain ⟨u, hu, hult⟩ := exists_lt_of_csInf_lt hne hlt
          exact (cl_bleed_iff P hS h4 hA1 hμ hn hi).2
            (cl_good_rate P hS h5 hA1 hn hu.1 hμ hult.le hu.2)
      · refine ⟨P.muU + 1, fun μ hμ =>
          ⟨fun _ => ?_, fun hlt => absurd hμ.2 (not_le.mpr (by linarith))⟩⟩
        have hg : ¬ cl_good P (B P n) μ i := fun hg => hne ⟨μ, hμ, hg⟩
        exact (cl_lt_Ck_of_not_good P hS hg).le
    · subst hn
      exact ⟨P.muU + 1, fun μ hμ => ⟨fun _ => cl_cont_N P hS hμ i,
        fun hlt => absurd hμ.2 (not_le.mpr (by linarith))⟩⟩
  · intro i hi μ hμ
    have hex : ∃ k, ¬ (k < P.N ∧ cl_good P (B P k) μ i) := ⟨P.N, fun h => lt_irrefl _ h.1⟩
    refine ⟨(Nat.find hex : ℤ) - 1, fun n hn => ⟨fun hle => ?_, fun hlt => ?_⟩⟩
    · have hlt : n < Nat.find hex := by omega
      have h := not_not.mp (Nat.find_min hex hlt)
      exact (cl_bleed_iff P hS h4 hA1 hμ h.1 hi).2 h.2
    · have hle : Nat.find hex ≤ n := by omega
      rcases lt_or_eq_of_le hn with hn' | hn'
      · have hg : ¬ cl_good P (B P n) μ i := by
          intro hg
          exact Nat.find_spec hex ⟨by omega, cl_good_count P hS hle hg⟩
        exact (cl_lt_Ck_of_not_good P hS hg).le
      · rw [hn']; exact cl_cont_N P hS hμ i
