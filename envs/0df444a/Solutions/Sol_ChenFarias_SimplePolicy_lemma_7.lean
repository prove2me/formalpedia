-- Prove2me | solution 1 for ChenFarias.SimplePolicy.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T18:52:36.402502+00:00
-- url     : https://prove2.me/submissions/de9ef4b6-c7bb-4d51-9855-d48261848c27

import Mathlib
import Definitions.Def_ChenFarias_SimplePolicy_Model
import Theorems.Thm_ChenFarias_SimplePolicy_price_antitone
import Theorems.Thm_ChenFarias_SimplePolicy_value_monotone
open MeasureTheory Set
open scoped ENNReal
open ChenFarias.SimplePolicy

lemma cf_Fbar_split (f : ℝ → ℝ) (hf : Assumption1 f) {a p : ℝ} (hap : a ≤ p) :
    Fbar f p = Fbar f a - ∫ v in a..p, f v := by
  have hint := hf.integrable
  unfold Fbar
  rw [← Ioc_union_Ioi_eq_Ioi hap,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint.integrableOn
      hint.integrableOn, intervalIntegral.integral_of_le hap]
  ring

lemma cf_Fbar_antitone (f : ℝ → ℝ) (hf : Assumption1 f) : Antitone (Fbar f) := by
  intro a b hab
  rw [cf_Fbar_split f hf hab]
  have : 0 ≤ ∫ v in a..b, f v :=
    intervalIntegral.integral_nonneg hab (fun u _ => hf.nonnegative u)
  linarith

lemma cf_Fbar_nonneg (f : ℝ → ℝ) (hf : Assumption1 f) (p : ℝ) : 0 ≤ Fbar f p :=
  setIntegral_nonneg measurableSet_Ioi (fun v _ => hf.nonnegative v)

/-- `(p - Δ) F̄(p)` is absolutely continuous with a.e. derivative `F̄ - (p - Δ) f`. -/
lemma cf_gain_identity (f : ℝ → ℝ) (hf : Assumption1 f) (Δ : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (b - Δ) * Fbar f b - (a - Δ) * Fbar f a =
      ∫ v in a..b, (Fbar f v - (v - Δ) * f v) := by
  set H : ℝ → ℝ := fun p => (p - Δ) * (Fbar f a - ∫ v in a..p, f v) with hH
  have hII : IntervalIntegrable f volume a b := hf.integrable.intervalIntegrable
  have hAC1 : AbsolutelyContinuousOnInterval (fun p : ℝ => p - Δ) a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    exact (contDiff_id.sub contDiff_const).contDiffOn
  have hAC2 : AbsolutelyContinuousOnInterval
      (fun p : ℝ => Fbar f a - ∫ v in a..p, f v) a b := by
    have h1 := hII.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
    have h0 : AbsolutelyContinuousOnInterval (fun _ : ℝ => Fbar f a) a b := by
      apply LipschitzOnWith.absolutelyContinuousOnInterval (K := 0)
      exact (LipschitzWith.const (Fbar f a)).lipschitzOnWith
    exact h0.sub h1
  have hAC : AbsolutelyContinuousOnInterval H a b := hAC1.fun_mul hAC2
  have hFTC := hAC.integral_deriv_eq_sub
  have hHb : H b = (b - Δ) * Fbar f b := by simp only [hH, ← cf_Fbar_split f hf hab]
  have hHa : H a = (a - Δ) * Fbar f a := by simp [hH]
  rw [← hHb, ← hHa, ← hFTC]
  apply intervalIntegral.integral_congr_ae
  have hLI : LocallyIntegrable f volume := hf.integrable.locallyIntegrable
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hLI] with x hx hxab
  have hx' : a ≤ x := by
    rw [uIoc_of_le hab] at hxab; exact hxab.1.le
  have hd : HasDerivAt H (1 * (Fbar f a - ∫ v in a..x, f v) + (x - Δ) * (0 - f x)) x := by
    have h1 : HasDerivAt (fun p : ℝ => p - Δ) 1 x := (hasDerivAt_id x).sub_const Δ
    have h2 : HasDerivAt (fun p : ℝ => Fbar f a - ∫ v in a..p, f v) (0 - f x) x :=
      (hasDerivAt_const x (Fbar f a)).sub (hx a)
    exact h1.mul h2
  rw [hd.deriv, ← cf_Fbar_split f hf hx']
  ring

/-- The root of `ψ(p) = Δ` maximizes `(p - Δ) F̄(p)` over `p ≥ 0`. -/
lemma cf_root_optimal (f : ℝ → ℝ) (hf : Assumption1 f) {Δ q p : ℝ} (hq : 0 ≤ q)
    (hψ : psi f q = Δ) (hp : 0 ≤ p) :
    (p - Δ) * Fbar f p ≤ (q - Δ) * Fbar f q := by
  have hkey : ∀ v, 0 ≤ v → Fbar f v - (v - Δ) * f v = f v * (Δ - psi f v) := by
    intro v hv
    have hfv : 0 < f v := hf.positive_of_nonnegative v hv
    unfold psi
    field_simp
    ring
  rcases le_total p q with hpq | hpq
  · have := cf_gain_identity f hf Δ hpq
    have hnn : 0 ≤ ∫ v in p..q, (Fbar f v - (v - Δ) * f v) := by
      apply intervalIntegral.integral_nonneg hpq
      intro u hu
      have hu0 : 0 ≤ u := hp.trans hu.1
      rw [hkey u hu0]
      have : psi f u ≤ psi f q :=
        hf.virtual_monotone (show u ∈ Ici (0:ℝ) from hu0) (show q ∈ Ici (0:ℝ) from hq) hu.2
      exact mul_nonneg (hf.nonnegative u) (by linarith)
    linarith
  · have := cf_gain_identity f hf Δ hpq
    have hnp : ∫ v in q..p, (Fbar f v - (v - Δ) * f v) ≤ 0 := by
      rw [← neg_nonneg, ← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_nonneg hpq
      intro u hu
      rw [neg_nonneg]
      have hu0 : 0 ≤ u := hq.trans hu.1
      rw [hkey u hu0]
      have : psi f q ≤ psi f u :=
        hf.virtual_monotone (show q ∈ Ici (0:ℝ) from hq) (show u ∈ Ici (0:ℝ) from hu0) hu.1
      exact mul_nonpos_of_nonneg_of_nonpos (hf.nonnegative u) (by linarith)
    linarith

/-- The Bellman value is attained at the root price. -/
lemma cf_bellman_eq (lam β : ℝ) (f : ℝ → ℝ) (V π : ℕ → ℝ) (hlam : 0 < lam)
    (hf : Assumption1 f) (hV : IsValueFn lam β f V) (hπ : IsRootPolicy f V π)
    (x : ℕ) (hx : 1 ≤ x) :
    β * V x = lam * Fbar f (π x) * (π x + V (x - 1) - V x) := by
  obtain ⟨hπ0, hψ, -⟩ := hπ x hx
  have hlub := hV.2 x hx
  apply le_antisymm
  · apply hlub.2
    rintro y ⟨p, hp, rfl⟩
    have := cf_root_optimal f hf hπ0 hψ hp
    have h2 : (p + V (x - 1) - V x) * Fbar f p ≤ (π x + V (x - 1) - V x) * Fbar f (π x) := by
      have e1 : p + V (x - 1) - V x = p - (V x - V (x - 1)) := by ring
      have e2 : π x + V (x - 1) - V x = π x - (V x - V (x - 1)) := by ring
      rw [e1, e2]; exact this
    nlinarith [mul_le_mul_of_nonneg_left h2 hlam.le]
  · exact hlub.1 ⟨π x, hπ0, rfl⟩

lemma cf_Xminus_antitone (lam : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ) (x0 : ℕ) (e : Fin x0 → ℝ) :
    Antitone (Xminus lam f π x0 e) := by
  intro s t hst
  unfold Xminus
  apply Nat.sub_le_sub_left
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, lt_of_lt_of_le hk.2 hst⟩

lemma cf_rate_mono (lam β : ℝ) (f : ℝ → ℝ) (V π : ℕ → ℝ) (hlam : 0 < lam) (hβ : 0 < β)
    (hf : Assumption1 f) (hV : IsValueFn lam β f V) (hπ : IsRootPolicy f V π)
    {x y : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    π x * Fbar f (π x) ≤ π y * Fbar f (π y) := by
  have hy : 1 ≤ y := hx.trans hxy
  obtain ⟨hπy0, hψy, -⟩ := hπ y hy
  have hπx0 := (hπ x hx).1
  have hopt := cf_root_optimal f hf hπy0 hψy hπx0
  have hanti := price_antitone lam β f V π hlam hβ hf hV hπ
    (show x ∈ Ici 1 from hx) (show y ∈ Ici 1 from hy) hxy
  have hF : Fbar f (π x) ≤ Fbar f (π y) := cf_Fbar_antitone f hf hanti
  have hΔ : 0 ≤ V y - V (y - 1) := by
    have := value_monotone lam β f V hlam hβ hf hV y hy; linarith
  nlinarith [mul_le_mul_of_nonneg_left hF hΔ]

theorem solution (lam β : ℝ) (f : ℝ → ℝ) (V : ℕ → ℝ) (π : ℕ → ℝ)
    (x0 : ℕ) (hlam : 0 < lam) (hβ : 0 < β) (hf : Assumption1 f)
    (hV : IsValueFn lam β f V) (hπ : IsRootPolicy f V π) :
    ∀ (e : Fin x0 → ℝ) (s t : ℝ), s ≤ t →
      priceAt lam f π x0 e s ≤ priceAt lam f π x0 e t ∧
      rateRev f π (Xminus lam f π x0 e t) ≤
        rateRev f π (Xminus lam f π x0 e s) := by
  intro e s t hst
  have hle : Xminus lam f π x0 e t ≤ Xminus lam f π x0 e s :=
    cf_Xminus_antitone lam f π x0 e hst
  constructor
  · unfold priceAt
    split_ifs with h1 h2 h2
    · exact le_rfl
    · omega
    · exact le_top
    · have := price_antitone lam β f V π hlam hβ hf hV hπ
        (show Xminus lam f π x0 e t ∈ Ici 1 by simp; omega)
        (show Xminus lam f π x0 e s ∈ Ici 1 by simp; omega) hle
      exact WithTop.coe_le_coe.2 this
  · unfold rateRev
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact mul_nonneg ((hπ _ (by omega)).1) (cf_Fbar_nonneg f hf _)
    · omega
    · exact cf_rate_mono lam β f V π hlam hβ hf hV hπ (by omega) hle
