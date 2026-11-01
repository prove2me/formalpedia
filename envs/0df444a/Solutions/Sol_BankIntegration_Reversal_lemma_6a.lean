-- Prove2me | solution 1 for BankIntegration.Reversal.lemma_6a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:16:32.181208+00:00
-- url     : https://prove2.me/submissions/483ede80-4328-42c6-8251-369a483813f9

import Mathlib
import Definitions.Def_BankIntegration_Reversal_Model

namespace BankL6aAux

open BankIntegration.Reversal

/-- reduced profit `(O + x)(μ − s(O + x))x`. -/
noncomputable def φ (μ s O x : ℝ) : ℝ := (O + x) * (μ - s * (O + x)) * x

lemma sum_update {m : ℕ} (L : Fin m → ℝ) (i : Fin m) (x : ℝ) :
    ∑ k, Function.update L i x k = (∑ k, L k) - L i + x := by
  have h1 := Finset.sum_update_of_mem (Finset.mem_univ i) L x
  have h2 := Finset.sum_sdiff (f := L) (Finset.subset_univ {i})
  rw [h1]; simp only [Finset.sum_singleton] at h2; linarith

lemma profit_eq (lam c a b y z : ℝ) (ha : 0 < a) (hb : 0 < b) (hl : 0 < lam) :
    bankProfit lam c a b y z = (y * (lam - c - (1/a + 1/b) * y) * z) / (2 * lam * b) := by
  unfold bankProfit; field_simp; ring

lemma dev_pos (μ s O : ℝ) (hs : 0 < s) (hO : 0 ≤ O) (h : 0 < μ - s * O) :
    0 < φ μ s O ((μ - s * O) / (2 * s)) := by
  unfold φ
  have hx : 0 < (μ - s * O) / (2 * s) := by positivity
  have e : μ - s * (O + (μ - s * O) / (2 * s)) = (μ - s * O) / 2 := by field_simp; ring
  rw [e]
  have : 0 < O + (μ - s * O) / (2 * s) := by linarith
  positivity

lemma foc (μ s O x0 : ℝ) (hx0 : 0 < x0) (hmax : ∀ x, 0 ≤ x → φ μ s O x ≤ φ μ s O x0) :
    (μ - 2 * s * (O + x0)) * x0 + (O + x0) * (μ - s * (O + x0)) = 0 := by
  have hloc : IsLocalMax (φ μ s O) x0 := by
    have : IsMaxOn (φ μ s O) (Set.Ici 0) x0 := fun x hx => hmax x hx
    exact this.isLocalMax (Ici_mem_nhds hx0)
  have hd : HasDerivAt (φ μ s O)
      ((μ - 2 * s * (O + x0)) * x0 + (O + x0) * (μ - s * (O + x0))) x0 := by
    have h1 : HasDerivAt (fun x : ℝ => O + x) 1 x0 := (hasDerivAt_id' x0).const_add O
    have h2 : HasDerivAt (fun x : ℝ => μ - s * (O + x)) (-(s * 1)) x0 :=
      (h1.const_mul s).const_sub μ
    have h3 := (h1.mul h2).mul (hasDerivAt_id' x0)
    unfold φ
    exact h3.congr_deriv (by simp only [Pi.mul_apply]; ring)
  exact hloc.hasDerivAt_eq_zero hd

lemma taylor (μ s O x0 x : ℝ) :
    φ μ s O x - φ μ s O x0 =
      ((μ - 2 * s * (O + x0)) * x0 + (O + x0) * (μ - s * (O + x0))) * (x - x0) +
        (x - x0) ^ 2 * (μ - 2 * s * (O + x0) - s * x) := by
  unfold φ; ring


/-- Nash condition rewritten in terms of the reduced profit. -/
lemma key {lam c a b : ℝ} {m : ℕ} (ha : 0 < a) (hb : 0 < b) (hl : 0 < lam)
    {L : Fin m → ℝ} (h : IsCournotEq lam c a b m L) (i : Fin m) (x : ℝ) (hx : 0 ≤ x) :
    φ (lam - c) (1 / a + 1 / b) ((∑ k, L k) - L i) x ≤
      φ (lam - c) (1 / a + 1 / b) ((∑ k, L k) - L i) (L i) := by
  have h1 := h.2 i x hx
  simp only [sum_update, Function.update_self] at h1
  rw [profit_eq _ _ _ _ _ _ ha hb hl, profit_eq _ _ _ _ _ _ ha hb hl] at h1
  have hp : 0 < 2 * lam * b := by positivity
  have h2 := (div_le_div_iff_of_pos_right hp).mp h1
  unfold φ
  have e : (∑ k, L k) - L i + L i = ∑ k, L k := by ring
  rw [e]; linarith

lemma char {lam c a b : ℝ} {m : ℕ} (ha : 0 < a) (hb : 0 < b) (hl : 0 < lam) (hμ : 0 < lam - c)
    (hm : 1 ≤ m) {L : Fin m → ℝ} (h : IsCournotEq lam c a b m L) :
    (∑ k, L k) * (((m : ℝ) + 2) * (1 / a + 1 / b)) = ((m : ℝ) + 1) * (lam - c) ∧
      ∀ i, ∑ k, L k = (m : ℝ) * L i := by
  have hK := key ha hb hl h
  set μ := lam - c with hμdef
  set s := 1 / a + 1 / b with hsdef
  have hs : 0 < s := by positivity
  set T := ∑ k, L k with hTdef
  have hnn : ∀ i, 0 ≤ L i := fun i => h.1 i
  have hle : ∀ i, L i ≤ T := fun i =>
    Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun j _ => hnn j)
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  -- Step 1: T > 0
  have hTpos : 0 < T := by
    by_contra hc
    have hT : T = 0 := by linarith
    let i0 : Fin m := ⟨0, by omega⟩
    have hz : L i0 = 0 := le_antisymm (hT ▸ hle i0) (hnn i0)
    have hd := dev_pos μ s 0 hs le_rfl (by simpa using hμ)
    have hx : 0 ≤ (μ - s * 0) / (2 * s) := div_nonneg (by linarith) (by linarith)
    have := hK i0 _ hx
    rw [hT, hz] at this
    simp [φ] at this hd
    linarith
  -- Step 2: μ - s T > 0
  have hgT : 0 < μ - s * T := by
    by_contra hc
    push Not at hc
    have : ∃ j, 0 < L j := by
      by_contra hn
      push Not at hn
      have : T ≤ 0 := Finset.sum_nonpos (fun j _ => hn j)
      linarith
    obtain ⟨j, hj⟩ := this
    have hO : 0 ≤ T - L j := by
      have : T - L j = ∑ k ∈ Finset.univ \ {j}, L k := by
        have h2 := Finset.sum_sdiff (f := L) (Finset.subset_univ {j})
        simp only [Finset.sum_singleton] at h2; linarith
      rw [this]; exact Finset.sum_nonneg (fun k _ => hnn k)
    have hcur : φ μ s (T - L j) (L j) ≤ 0 := by
      unfold φ
      have e : T - L j + L j = T := by ring
      rw [e]
      have : 0 ≤ T * (-(μ - s * T)) * L j := by
        apply mul_nonneg (mul_nonneg hT0 (by linarith)) hj.le
      nlinarith
    by_cases hg : 0 < μ - s * (T - L j)
    · have hd := dev_pos μ s (T - L j) hs hO hg
      have := hK j _ (div_nonneg (by linarith) (by linarith) : 0 ≤ (μ - s * (T - L j)) / (2 * s))
      linarith
    · push Not at hg
      have := hK j 0 le_rfl
      have hlt : φ μ s (T - L j) (L j) < 0 := by
        unfold φ
        have e : T - L j + L j = T := by ring
        rw [e]
        have h3 : μ - s * T < 0 := by nlinarith
        have : 0 < T * (-(μ - s * T)) * L j := by
          apply mul_pos (mul_pos hTpos (by linarith)) hj
        nlinarith
      have h0 : φ μ s (T - L j) 0 = 0 := by simp [φ]
      linarith
  -- Step 3: every L i > 0
  have hpos : ∀ i, 0 < L i := by
    intro i
    rcases (hnn i).lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have hz : L i = 0 := h'.symm
      have hd := dev_pos μ s T hs hT0 hgT
      have := hK i _ (div_nonneg (by linarith) (by linarith) : 0 ≤ (μ - s * T) / (2 * s))
      rw [hz, sub_zero] at this
      have h0 : φ μ s T 0 = 0 := by simp [φ]
      linarith
  -- Step 4: first-order conditions
  have hfoc : ∀ i, L i * (μ - 2 * s * T) = -(T * (μ - s * T)) := by
    intro i
    have := foc μ s (T - L i) (L i) (hpos i) (hK i)
    have e : T - L i + L i = T := by ring
    rw [e] at this
    linarith
  have hsum : T * (μ - 2 * s * T) = (m : ℝ) * (-(T * (μ - s * T))) := by
    have : ∑ i, L i * (μ - 2 * s * T) = ∑ _i : Fin m, (-(T * (μ - s * T))) :=
      Finset.sum_congr rfl (fun i _ => hfoc i)
    rw [← Finset.sum_mul] at this
    rw [this]; simp
  have hrel : μ - 2 * s * T = -((m : ℝ) * (μ - s * T)) := by
    have h3 : T * (μ - 2 * s * T + (m : ℝ) * (μ - s * T)) = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · linarith
    · linarith
  refine ⟨by linarith, fun i => ?_⟩
  have hne : μ - 2 * s * T ≠ 0 := by
    rw [hrel]; have : 0 < (m : ℝ) * (μ - s * T) := by positivity
    linarith
  have h5 : ((m : ℝ) * L i) * (μ - 2 * s * T) = T * (μ - 2 * s * T) := by
    rw [hsum, mul_assoc, hfoc i]
  exact (mul_right_cancel₀ hne h5).symm

lemma risk (lam r θ : ℝ) (hl : 0 < lam) (hr0 : -lam ≤ r) (hr1 : r ≤ lam) :
    IsOptimalRisk lam r θ ↔ θ = (lam + r) / 2 := by
  have key : ∀ x : ℝ, (1 - x / lam) * (x - r) =
      (1 - (lam + r) / 2 / lam) * ((lam + r) / 2 - r) - (x - (lam + r) / 2) ^ 2 / lam := by
    intro x; field_simp; ring
  have hmem : (lam + r) / 2 ∈ Set.Icc 0 lam := ⟨by linarith, by linarith⟩
  constructor
  · rintro ⟨_, hopt⟩
    have h := hopt _ hmem
    rw [key θ, key ((lam + r) / 2)] at h
    have h2 : (θ - (lam + r) / 2) ^ 2 / lam ≤ 0 := by
      have : ((lam + r) / 2 - (lam + r) / 2) ^ 2 / lam = 0 := by ring
      linarith
    have h3 : (θ - (lam + r) / 2) ^ 2 ≤ 0 := by
      have := (div_le_iff₀ hl).mp h2; linarith
    have h4 : θ - (lam + r) / 2 = 0 := by nlinarith [sq_nonneg (θ - (lam + r) / 2)]
    linarith
  · rintro rfl
    refine ⟨hmem, fun θ' _ => ?_⟩
    rw [key θ', key ((lam + r) / 2)]
    have : 0 ≤ (θ' - (lam + r) / 2) ^ 2 / lam := by positivity
    have e : ((lam + r) / 2 - (lam + r) / 2) ^ 2 / lam = 0 := by ring
    linarith

end BankL6aAux

open BankIntegration.Reversal BankL6aAux in
theorem solution (lam c a b : ℝ) (m : ℕ) (hlam : 1 < lam) (hc0 : 0 ≤ c) (hc1 : c < lam)
    (ha : 0 < a) (hb : 0 < b) (hm : 1 ≤ m) :
    (∃! L : Fin m → ℝ, IsCournotEq lam c a b m L) ∧
    ∀ L : Fin m → ℝ, IsCournotEq lam c a b m L →
      (∀ i, ∑ k, L k = (m : ℝ) * L i) ∧
      depositRate a (∑ k, L k) =
        (lam - c) * (((m : ℝ) + 1) / ((m : ℝ) + 2)) * (xi a b / (1 + xi a b)) ∧
      loanRate lam b (∑ k, L k) =
        lam - (lam - c) * (((m : ℝ) + 1) / ((m : ℝ) + 2)) * (1 / (1 + xi a b)) ∧
      ∀ θ : ℝ, IsOptimalRisk lam (loanRate lam b (∑ k, L k)) θ ↔
        θ = lam - (lam - c) / 2 * (((m : ℝ) + 1) / ((m : ℝ) + 2)) * (1 / (1 + xi a b)) := by
  have hl : 0 < lam := by linarith
  have hμ : 0 < lam - c := by linarith
  set μ := lam - c with hμdef
  set s := 1 / a + 1 / b with hsdef
  have hs : 0 < s := by positivity
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  set Ts := ((m : ℝ) + 1) * μ / (((m : ℝ) + 2) * s) with hTs
  have hTs_pos : 0 < Ts := by positivity
  -- characterization of the total
  have hT : ∀ L : Fin m → ℝ, IsCournotEq lam c a b m L → ∑ k, L k = Ts := by
    intro L hL
    have := (char ha hb hl hμ hm hL).1
    rw [hTs, eq_div_iff (by positivity)]; linarith
  -- the symmetric profile is an equilibrium
  let L0 : Fin m → ℝ := fun _ => Ts / m
  have hL0sum : ∑ k, L0 k = Ts := by
    simp [L0]; field_simp
  have hL0 : IsCournotEq lam c a b m L0 := by
    refine ⟨fun i => ?_, fun i x hx => ?_⟩
    · show (0 : ℝ) ≤ Ts / m; positivity
    · have h1 : φ μ s (Ts - Ts / m) x ≤ φ μ s (Ts - Ts / m) (Ts / m) := by
        have ht := taylor μ s (Ts - Ts / m) (Ts / m) x
        have hf : (μ - 2 * s * (Ts - Ts / m + Ts / m)) * (Ts / m) +
            (Ts - Ts / m + Ts / m) * (μ - s * (Ts - Ts / m + Ts / m)) = 0 := by
          rw [hTs]; field_simp; ring
        have hneg : μ - 2 * s * (Ts - Ts / m + Ts / m) - s * x < 0 := by
          have e : μ - 2 * s * (Ts - Ts / m + Ts / m) = -((m : ℝ) * μ / ((m : ℝ) + 2)) := by
            rw [hTs]; field_simp; ring
          rw [e]
          have : 0 < (m : ℝ) * μ / ((m : ℝ) + 2) := by positivity
          have hx' : (0 : ℝ) ≤ x := hx
          nlinarith [mul_nonneg hs.le hx']
        rw [hf, zero_mul, zero_add] at ht
        have : (x - Ts / m) ^ 2 * (μ - 2 * s * (Ts - Ts / m + Ts / m) - s * x) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hneg.le
        linarith
      simp only [sum_update, Function.update_self]
      rw [profit_eq _ _ _ _ _ _ ha hb hl, profit_eq _ _ _ _ _ _ ha hb hl, hL0sum]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have e1 : Ts - L0 i + x = (Ts - Ts / m) + x := rfl
      have e2 : L0 i = Ts / m := rfl
      rw [e1, e2]
      unfold φ at h1
      have e3 : Ts - Ts / m + Ts / m = Ts := by ring
      rw [e3] at h1
      exact h1
  have hxi : xi a b = b / a := rfl
  refine ⟨⟨L0, hL0, fun L hL => ?_⟩, fun L hL => ?_⟩
  · funext i
    have h1 := (char ha hb hl hμ hm hL).2 i
    rw [hT L hL] at h1
    show L i = Ts / m
    rw [eq_div_iff hm0]; linarith
  · have hsum := hT L hL
    refine ⟨(char ha hb hl hμ hm hL).2, ?_, ?_, ?_⟩
    · unfold depositRate; rw [hsum, hTs, hxi, hsdef]; field_simp; ring
    · unfold loanRate; rw [hsum, hTs, hxi, hsdef]; field_simp; ring
    · intro θ
      have hr : loanRate lam b (∑ k, L k) =
          lam - μ * (((m : ℝ) + 1) / ((m : ℝ) + 2)) * (1 / (1 + xi a b)) := by
        unfold loanRate; rw [hsum, hTs, hxi, hsdef]; field_simp; ring
      have hxi0 : 0 < xi a b := by rw [hxi]; positivity
      have hq0 : 0 ≤ μ * (((m : ℝ) + 1) / ((m : ℝ) + 2)) * (1 / (1 + xi a b)) := by positivity
      have hq1 : μ * (((m : ℝ) + 1) / ((m : ℝ) + 2)) * (1 / (1 + xi a b)) ≤ μ := by
        have h1 : ((m : ℝ) + 1) / ((m : ℝ) + 2) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith
        have h2 : 1 / (1 + xi a b) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith
        have h3 : ((m : ℝ) + 1) / ((m : ℝ) + 2) * (1 / (1 + xi a b)) ≤ 1 := by
          have : 0 ≤ 1 / (1 + xi a b) := by positivity
          nlinarith
        have : μ * (((m : ℝ) + 1) / ((m : ℝ) + 2) * (1 / (1 + xi a b))) ≤ μ * 1 :=
          mul_le_mul_of_nonneg_left h3 hμ.le
        linarith [mul_assoc μ (((m : ℝ) + 1) / ((m : ℝ) + 2)) (1 / (1 + xi a b))]
      rw [hr, risk lam _ θ hl (by linarith) (by linarith)]
      constructor <;> intro h <;> linarith
