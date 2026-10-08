-- Prove2me | solution 1 for ErschlerZheng.hasFiniteEntropy_convPow_and_tendsto_entropy_convPow_div
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-05T22:12:59.875219+00:00
-- url     : https://prove2.me/submissions/427c6277-c44c-4726-82e1-ddb44f10625c

import Mathlib
import Definitions.Def_ErschlerZheng_Walks

section
/-!
# C1: Avez's asymptotic entropy exists (Erschler–Zheng p. 10)

`H(μ^{(n)})/n → h_μ`: entropy is subadditive under convolution, `H(μ ⋆ ν) ≤ H(μ) + H(ν)`,
so `n ↦ H(μ^{(n)})` is subadditive and Fekete's lemma applies.

All bookkeeping is done in `ℝ≥0∞`, where the series need no summability side conditions.
-/

namespace ErschlerZheng

namespace EntropyDev

open scoped ENNReal

set_option linter.unusedSectionVars false

variable {Γ : Type*} [Group Γ]

/-- The entropy series in `[0, ∞]`. -/
noncomputable def entE (μ : Γ → ℝ) : ℝ≥0∞ := ∑' g, ENNReal.ofReal (Real.negMulLog (μ g))

/-- Convolution of `[0, ∞]`-valued functions. -/
noncomputable def convE (a b : Γ → ℝ≥0∞) : Γ → ℝ≥0∞ := fun g => ∑' h, a h * b (h⁻¹ * g)

lemma le_one_of_isProb {μ : Γ → ℝ} (hμ : IsProbability μ) (g : Γ) : μ g ≤ 1 :=
  le_hasSum hμ.2 g (fun j _ => hμ.1 j)

lemma tsum_ofReal_of_isProb {μ : Γ → ℝ} (hμ : IsProbability μ) :
    ∑' g, ENNReal.ofReal (μ g) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg hμ.1 hμ.2.summable, hμ.2.tsum_eq, ENNReal.ofReal_one]

lemma isProb_of_tsum_ofReal {f : Γ → ℝ} (h0 : ∀ g, 0 ≤ f g)
    (h : ∑' g, ENNReal.ofReal (f g) = 1) : IsProbability f := by
  have hs : Summable f := by
    have := ENNReal.summable_toReal (f := fun g => ENNReal.ofReal (f g))
      (by rw [h]; exact ENNReal.one_ne_top)
    simpa [ENNReal.toReal_ofReal (h0 _)] using this
  refine ⟨h0, hs.hasSum_iff.mpr ?_⟩
  have := ENNReal.ofReal_tsum_of_nonneg h0 hs
  rw [h] at this
  exact ENNReal.ofReal_eq_one.mp this

lemma tsum_mulLeft_eq (F : Γ → ℝ≥0∞) (k : Γ) : ∑' m, F (k * m) = ∑' h, F h :=
  (Equiv.mulLeft k).tsum_eq F

lemma conv_summand_summable {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν) (g : Γ) :
    Summable fun h => μ h * ν (h⁻¹ * g) := by
  refine Summable.of_nonneg_of_le (fun h => mul_nonneg (hμ.1 h) (hν.1 _)) (fun h => ?_)
    hμ.2.summable
  calc μ h * ν (h⁻¹ * g) ≤ μ h * 1 :=
        mul_le_mul_of_nonneg_left (le_one_of_isProb hν _) (hμ.1 h)
    _ = μ h := mul_one _

lemma conv_nonneg {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν) (g : Γ) :
    0 ≤ conv μ ν g :=
  tsum_nonneg fun h => mul_nonneg (hμ.1 h) (hν.1 _)

lemma ofReal_conv {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν) (g : Γ) :
    ENNReal.ofReal (conv μ ν g) =
      convE (fun x => ENNReal.ofReal (μ x)) (fun x => ENNReal.ofReal (ν x)) g := by
  unfold conv convE
  rw [ENNReal.ofReal_tsum_of_nonneg (fun h => mul_nonneg (hμ.1 h) (hν.1 _))
    (conv_summand_summable hμ hν g)]
  congr 1
  ext h
  rw [ENNReal.ofReal_mul (hμ.1 h)]

lemma isProb_conv {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν) :
    IsProbability (conv μ ν) := by
  refine isProb_of_tsum_ofReal (conv_nonneg hμ hν) ?_
  simp_rw [ofReal_conv hμ hν]
  unfold convE
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  have : ∀ h : Γ, ∑' g, ENNReal.ofReal (ν (h⁻¹ * g)) = 1 := fun h => by
    rw [tsum_mulLeft_eq (fun x => ENNReal.ofReal (ν x)) h⁻¹]
    exact tsum_ofReal_of_isProb hν
  simp_rw [this, mul_one]
  exact tsum_ofReal_of_isProb hμ

lemma convE_assoc (a b c : Γ → ℝ≥0∞) : convE (convE a b) c = convE a (convE b c) := by
  ext g
  unfold convE
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  congr 1
  ext k
  rw [← ENNReal.tsum_mul_left]
  rw [← tsum_mulLeft_eq _ k]
  congr 1
  ext m
  simp only [mul_inv_rev, inv_mul_cancel_left, mul_assoc]

lemma conv_assoc {a b c : Γ → ℝ} (ha : IsProbability a) (hb : IsProbability b)
    (hc : IsProbability c) : conv (conv a b) c = conv a (conv b c) := by
  ext g
  have h1 := ofReal_conv (isProb_conv ha hb) hc g
  have h2 := ofReal_conv ha (isProb_conv hb hc) g
  have e1 : (fun x => ENNReal.ofReal (conv a b x)) =
      convE (fun x => ENNReal.ofReal (a x)) (fun x => ENNReal.ofReal (b x)) :=
    funext (ofReal_conv ha hb)
  have e2 : (fun x => ENNReal.ofReal (conv b c x)) =
      convE (fun x => ENNReal.ofReal (b x)) (fun x => ENNReal.ofReal (c x)) :=
    funext (ofReal_conv hb hc)
  rw [e1] at h1
  rw [e2, ← convE_assoc, ← h1] at h2
  exact (ENNReal.ofReal_eq_ofReal_iff (conv_nonneg (isProb_conv ha hb) hc g)
    (conv_nonneg ha (isProb_conv hb hc) g)).mp h2.symm

open scoped Classical in
lemma conv_delta (a : Γ → ℝ) : conv a (fun g => if g = 1 then 1 else 0) = a := by
  ext g
  unfold conv
  rw [tsum_eq_single g]
  · simp
  · intro h hh
    have : h⁻¹ * g ≠ 1 := by
      intro e
      apply hh
      rw [inv_mul_eq_one] at e
      exact e
    simp [this]

lemma isProb_convPow {μ : Γ → ℝ} (hμ : IsProbability μ) (n : ℕ) :
    IsProbability (convPow μ n) := by
  induction n with
  | zero =>
    classical
    refine ⟨fun g => ?_, ?_⟩
    · simp only [convPow]; split_ifs <;> norm_num
    · have : convPow μ 0 = fun g => if g = 1 then (1 : ℝ) else 0 := by
        ext g; simp only [convPow]
      rw [this]
      convert hasSum_ite_eq (1 : Γ) (1 : ℝ) using 1
  | succ n ih => exact isProb_conv ih hμ

lemma convPow_add {μ : Γ → ℝ} (hμ : IsProbability μ) (m n : ℕ) :
    convPow μ (m + n) = conv (convPow μ m) (convPow μ n) := by
  induction n with
  | zero =>
    classical
    have : convPow μ 0 = fun g => if g = 1 then (1 : ℝ) else 0 := by
      ext g; simp only [convPow]
    rw [this, conv_delta]
    rfl
  | succ n ih =>
    rw [← add_assoc]
    show conv (convPow μ (m + n)) μ = conv (convPow μ m) (conv (convPow μ n) μ)
    rw [ih, conv_assoc (isProb_convPow hμ m) (isProb_convPow hμ n) hμ]

/-- The pointwise step: `-q log q ≤ Σ_h -t_h log t_h` where `q = Σ_h t_h`. -/
lemma ofReal_negMulLog_conv_le {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν)
    (g : Γ) :
    ENNReal.ofReal (Real.negMulLog (conv μ ν g)) ≤
      ∑' h, ENNReal.ofReal (Real.negMulLog (μ h * ν (h⁻¹ * g))) := by
  set q := conv μ ν g with hq
  have hq0 : 0 ≤ q := conv_nonneg hμ hν g
  have hq1 : q ≤ 1 := le_one_of_isProb (isProb_conv hμ hν) g
  have hlog : 0 ≤ -Real.log q := by
    have := Real.log_nonpos hq0 hq1
    linarith
  have hs := conv_summand_summable hμ hν g
  have ht0 : ∀ h, 0 ≤ μ h * ν (h⁻¹ * g) := fun h => mul_nonneg (hμ.1 h) (hν.1 _)
  have key : Real.negMulLog q = ∑' h, μ h * ν (h⁻¹ * g) * (-Real.log q) := by
    rw [tsum_mul_right, Real.negMulLog]
    rw [hq]
    unfold conv
    ring
  rw [key, ENNReal.ofReal_tsum_of_nonneg (fun h => mul_nonneg (ht0 h) hlog)
    (hs.mul_right _)]
  refine ENNReal.tsum_le_tsum fun h => ENNReal.ofReal_le_ofReal ?_
  set t := μ h * ν (h⁻¹ * g) with ht
  rcases (ht0 h).lt_or_eq with htp | htz
  · have htq : t ≤ q := hs.le_tsum h (fun j _ => ht0 j)
    have : Real.log t ≤ Real.log q := Real.log_le_log htp htq
    rw [Real.negMulLog]
    nlinarith
  · rw [ht, ← htz]
    simp

lemma entE_conv_le {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν) :
    entE (conv μ ν) ≤ entE μ + entE ν := by
  unfold entE
  calc ∑' g, ENNReal.ofReal (Real.negMulLog (conv μ ν g))
      ≤ ∑' g, ∑' h, ENNReal.ofReal (Real.negMulLog (μ h * ν (h⁻¹ * g))) :=
        ENNReal.tsum_le_tsum fun g => ofReal_negMulLog_conv_le hμ hν g
    _ = ∑' h, ∑' k, ENNReal.ofReal (Real.negMulLog (μ h * ν k)) := by
        rw [ENNReal.tsum_comm]
        congr 1
        ext h
        rw [← tsum_mulLeft_eq _ h]
        simp only [inv_mul_cancel_left]
    _ = ∑' h, ∑' k, (ENNReal.ofReal (ν k) * ENNReal.ofReal (Real.negMulLog (μ h)) +
          ENNReal.ofReal (μ h) * ENNReal.ofReal (Real.negMulLog (ν k))) := by
        congr 1; ext h; congr 1; ext k
        have a0 := Real.negMulLog_nonneg (hμ.1 h) (le_one_of_isProb hμ h)
        have b0 := Real.negMulLog_nonneg (hν.1 k) (le_one_of_isProb hν k)
        rw [Real.negMulLog_mul, ENNReal.ofReal_add (mul_nonneg (hν.1 k) a0)
          (mul_nonneg (hμ.1 h) b0), ENNReal.ofReal_mul (hν.1 k), ENNReal.ofReal_mul (hμ.1 h)]
    _ = ∑' g, ENNReal.ofReal (Real.negMulLog (μ g)) +
          ∑' g, ENNReal.ofReal (Real.negMulLog (ν g)) := by
        simp_rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left,
          tsum_ofReal_of_isProb hν, one_mul]
        rw [ENNReal.tsum_mul_right, tsum_ofReal_of_isProb hμ, one_mul]

lemma entropy_eq_toReal {μ : Γ → ℝ} (hμ : IsProbability μ) : entropy μ = (entE μ).toReal := by
  unfold entropy entE
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  congr 1
  ext g
  rw [ENNReal.toReal_ofReal (Real.negMulLog_nonneg (hμ.1 g) (le_one_of_isProb hμ g))]

lemma entE_ne_top {μ : Γ → ℝ} (hμ : IsProbability μ) (hH : HasFiniteEntropy μ) : entE μ ≠ ⊤ := by
  unfold entE
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun g => Real.negMulLog_nonneg (hμ.1 g) (le_one_of_isProb hμ g)) hH]
  exact ENNReal.ofReal_ne_top

lemma entE_convPow_le {μ : Γ → ℝ} (hμ : IsProbability μ) (n : ℕ) :
    entE (convPow μ n) ≤ n * entE μ := by
  induction n with
  | zero =>
    classical
    have : convPow μ 0 = fun g => if g = 1 then (1 : ℝ) else 0 := by
      ext g; simp only [convPow]
    rw [this]
    unfold entE
    simp only [Nat.cast_zero, zero_mul, nonpos_iff_eq_zero, ENNReal.tsum_eq_zero]
    intro g
    split_ifs <;> simp
  | succ n ih =>
    calc entE (convPow μ (n + 1)) = entE (conv (convPow μ n) μ) := rfl
      _ ≤ entE (convPow μ n) + entE μ := entE_conv_le (isProb_convPow hμ n) hμ
      _ ≤ n * entE μ + entE μ := by gcongr
      _ = (n + 1 : ℕ) * entE μ := by push_cast; ring

end EntropyDev

end ErschlerZheng
end

section
open ErschlerZheng
open EntropyDev in
theorem solution {Γ : Type*} [Group Γ]
    [Countable Γ] (μ : Γ → ℝ) (hμ : IsProbability μ) (hH : HasFiniteEntropy μ) :
    (∀ n : ℕ, HasFiniteEntropy (convPow μ n)) ∧
    Filter.Tendsto (fun n : ℕ => entropy (convPow μ n) / n) Filter.atTop
      (nhds (asymptoticEntropy μ)) := by
  have hfin : ∀ n, entE (convPow μ n) ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) (entE_ne_top hμ hH))
      (entE_convPow_le hμ n)
  refine ⟨fun n => ?_, ?_⟩
  · have hp := isProb_convPow hμ n
    have h := hfin n
    unfold entE at h
    exact (ENNReal.summable_toReal h).congr fun g =>
      ENNReal.toReal_ofReal (Real.negMulLog_nonneg (hp.1 g) (le_one_of_isProb hp g))
  have hsub : Subadditive fun n => entropy (convPow μ n) := by
    intro m n
    simp only
    rw [entropy_eq_toReal (isProb_convPow hμ _), entropy_eq_toReal (isProb_convPow hμ _),
      entropy_eq_toReal (isProb_convPow hμ _), convPow_add hμ,
      ← ENNReal.toReal_add (hfin m) (hfin n)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin m, hfin n⟩)
      (entE_conv_le (isProb_convPow hμ m) (isProb_convPow hμ n))
  have hbdd : BddBelow (Set.range fun n : ℕ => entropy (convPow μ n) / n) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    simp only
    rw [entropy_eq_toReal (isProb_convPow hμ _)]
    positivity
  have T := hsub.tendsto_lim hbdd
  unfold asymptoticEntropy
  rwa [T.limUnder_eq]
end
