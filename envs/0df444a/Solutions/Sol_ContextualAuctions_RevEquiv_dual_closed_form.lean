-- Prove2me | solution 1 for ContextualAuctions.RevEquiv.dual_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T07:00:28.480039+00:00
-- url     : https://prove2.me/submissions/b8f866b9-fe91-446e-a6af-682b62e8551e

import Mathlib
import Definitions.Def_ContextualAuctions_RevEquiv_Setting

open MeasureTheory Set

namespace RevEqAbs

/-- If every `y ∈ S` has `λ(Iic y) ≤ C` then `λ S ≤ C`. -/
lemma measure_le_of_Iic (lam : Measure ℝ) (S : Set ℝ) (C : ENNReal)
    (h : ∀ y ∈ S, lam (Iic y) ≤ C) : lam S ≤ C := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · simp [hS]
  -- a monotone sequence of points `z n` with `S ⊆ ⋃ Iic (z n)` (or `S ⊆ Iic s` with `s ∈ S`)
  by_cases hb : BddAbove S
  · set s := sSup S
    by_cases hs : s ∈ S
    · exact (measure_mono (fun y hy => (le_csSup hb hy : y ≤ s))).trans (h s hs)
    · have hsub : S ⊆ ⋃ n : ℕ, Iic (s - 1 / ((n : ℝ) + 1)) := by
        intro y hy
        have hlt : y < s := lt_of_le_of_ne (le_csSup hb hy) (fun e => hs (e ▸ hy))
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
        exact mem_iUnion.mpr ⟨n, by simp only [mem_Iic]; linarith⟩
      refine (measure_mono hsub).trans ?_
      have hmono : Monotone (fun n : ℕ => Iic (s - 1 / ((n : ℝ) + 1))) := by
        intro m n hmn
        apply Iic_subset_Iic.mpr
        have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast Nat.add_le_add_right hmn 1
        linarith
      rw [hmono.measure_iUnion]
      refine iSup_le fun n => ?_
      have hz : s - 1 / ((n : ℝ) + 1) < s := by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      obtain ⟨y, hy, hzy⟩ := exists_lt_of_lt_csSup hS hz
      exact (measure_mono (Iic_subset_Iic.mpr hzy.le)).trans (h y hy)
  · have hsub : S ⊆ ⋃ n : ℕ, Iic (n : ℝ) := by
      intro y _
      obtain ⟨n, hn⟩ := exists_nat_ge y
      exact mem_iUnion.mpr ⟨n, hn⟩
    refine (measure_mono hsub).trans ?_
    have hmono : Monotone (fun n : ℕ => Iic (n : ℝ)) := by
      intro m n hmn; exact Iic_subset_Iic.mpr (by exact_mod_cast hmn)
    rw [hmono.measure_iUnion]
    refine iSup_le fun n => ?_
    rw [not_bddAbove_iff] at hb
    obtain ⟨y, hy, hny⟩ := hb n
    exact (measure_mono (Iic_subset_Iic.mpr hny.le)).trans (h y hy)

variable (lam : Measure ℝ) [IsProbabilityMeasure lam] (r : ℝ) (k : ℕ)

/-- `H(y) = λ((-∞, y])^k`. -/
noncomputable def Hf (y : ℝ) : ℝ := (lam (Iic y)).toReal ^ k

open Classical in
/-- First-price bidding function. -/
noncomputable def sig (x : ℝ) : ℝ :=
  if x < r then x else if Hf lam k x = 0 then 0 else
    x - (∫ s in r..x, Hf lam k s) / Hf lam k x

open Classical in
noncomputable def gf (x : ℝ) : ℝ :=
  if r ≤ x then ∫ s in r..x, Hf lam k s else 0

lemma Hf_nonneg (y : ℝ) : 0 ≤ Hf lam k y := by unfold Hf; positivity

lemma Hf_mono : Monotone (Hf lam k) := by
  intro a b hab
  unfold Hf
  apply pow_le_pow_left₀ ENNReal.toReal_nonneg
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Iic_subset_Iic.mpr hab))

lemma Hf_le_one (y : ℝ) : Hf lam k y ≤ 1 := by
  unfold Hf
  apply pow_le_one₀ ENNReal.toReal_nonneg
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

lemma Hf_ii (a b : ℝ) : IntervalIntegrable (Hf lam k) volume a b :=
  (Hf_mono lam k).intervalIntegrable

/-- `∫_a^b H ≤ (b - a) H(b)` for `a ≤ b`. -/
lemma int_le_right {a b : ℝ} (hab : a ≤ b) :
    ∫ s in a..b, Hf lam k s ≤ (b - a) * Hf lam k b := by
  have := intervalIntegral.integral_mono_on hab (Hf_ii lam k a b)
    (intervalIntegrable_const (c := Hf lam k b))
    (fun s hs => Hf_mono lam k hs.2)
  simpa [mul_comm] using this

/-- `(b - a) H(a) ≤ ∫_a^b H` for `a ≤ b`. -/
lemma int_ge_left {a b : ℝ} (hab : a ≤ b) :
    (b - a) * Hf lam k a ≤ ∫ s in a..b, Hf lam k s := by
  have := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (c := Hf lam k a))
    (Hf_ii lam k a b) (fun s hs => Hf_mono lam k hs.1)
  simpa [mul_comm] using this

lemma int_nonneg {a b : ℝ} (hab : a ≤ b) : 0 ≤ ∫ s in a..b, Hf lam k s :=
  intervalIntegral.integral_nonneg hab (fun s _ => Hf_nonneg lam k s)

lemma gf_nonneg (x : ℝ) : 0 ≤ gf lam r k x := by
  unfold gf; split_ifs with h
  · exact int_nonneg lam k h
  · exact le_refl _

/-- Incentive compatibility: for `y ≥ r` with `H(y) > 0`, `(x - σ(y)) H(y) ≤ ∫_r^x H` when `r ≤ x`. -/
lemma ic (x y : ℝ) (hrx : r ≤ x) (hry : r ≤ y) (hy : 0 < Hf lam k y) :
    (x - sig lam r k y) * Hf lam k y ≤ ∫ s in r..x, Hf lam k s := by
  have hsig : sig lam r k y = y - (∫ s in r..y, Hf lam k s) / Hf lam k y := by
    unfold sig; rw [if_neg (not_lt.mpr hry), if_neg hy.ne']
  rw [hsig]
  have e : (x - (y - (∫ s in r..y, Hf lam k s) / Hf lam k y)) * Hf lam k y =
      (x - y) * Hf lam k y + ∫ s in r..y, Hf lam k s := by
    field_simp; ring
  rw [e, ← intervalIntegral.integral_add_adjacent_intervals (Hf_ii lam k r y) (Hf_ii lam k y x)]
  rcases le_total y x with hyx | hxy
  · have := int_ge_left lam k hyx; linarith
  · have h1 := int_le_right lam k hxy
    have h2 := intervalIntegral.integral_symm (f := Hf lam k) (μ := volume) x y
    linarith

/-- Claim A: no bid `b ≥ r` beats the closed form. -/
lemma claimA (x b : ℝ) (hrb : r ≤ b) (hk : 1 ≤ k) :
    (x - b) * (lam {y | sig lam r k y ≤ b}).toReal ^ k ≤ gf lam r k x := by
  rcases le_or_gt x b with hxb | hbx
  · have : (x - b) * (lam {y | sig lam r k y ≤ b}).toReal ^ k ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    exact this.trans (gf_nonneg lam r k x)
  have hrx : r ≤ x := hrb.trans hbx.le
  have hg : gf lam r k x = ∫ s in r..x, Hf lam k s := by unfold gf; rw [if_pos hrx]
  rw [hg]
  set I := ∫ s in r..x, Hf lam k s
  have hxb : 0 < x - b := by linarith
  have hk0 : k ≠ 0 := by omega
  -- every `y` with `σ(y) ≤ b` has `(x - b) L(y)^k ≤ I`
  have key : ∀ y, sig lam r k y ≤ b → (x - b) * Hf lam k y ≤ I := by
    intro y hy
    by_cases hyr : y < r
    · have h1 := int_ge_left lam k hrx
      have h2 : Hf lam k y ≤ Hf lam k r := Hf_mono lam k hyr.le
      have h3 : (x - b) * Hf lam k y ≤ (x - r) * Hf lam k r :=
        mul_le_mul (by linarith) h2 (Hf_nonneg lam k y) (by linarith)
      linarith
    · push_neg at hyr
      by_cases hH : Hf lam k y = 0
      · rw [hH, mul_zero]; exact int_nonneg lam k hrx
      · have hpos : 0 < Hf lam k y := lt_of_le_of_ne (Hf_nonneg lam k y) (Ne.symm hH)
        have := ic lam r k x y hrx hyr hpos
        have h4 : (x - b) * Hf lam k y ≤ (x - sig lam r k y) * Hf lam k y :=
          mul_le_mul_of_nonneg_right (by linarith) hpos.le
        linarith
  set c0 : ℝ := (I / (x - b)) ^ ((k : ℝ)⁻¹)
  have hI : 0 ≤ I := int_nonneg lam k hrx
  have hc0 : 0 ≤ c0 := by positivity
  have hbound : ∀ y ∈ {y | sig lam r k y ≤ b}, lam (Iic y) ≤ ENNReal.ofReal c0 := by
    intro y hy
    have h1 := key y hy
    have h2 : (lam (Iic y)).toReal ^ k ≤ I / (x - b) := by
      rw [le_div_iff₀ hxb]; unfold Hf at h1; linarith
    have h3 : (lam (Iic y)).toReal ≤ c0 := by
      have := Real.rpow_le_rpow (by positivity) h2 (by positivity : (0:ℝ) ≤ (k : ℝ)⁻¹)
      rwa [Real.pow_rpow_inv_natCast ENNReal.toReal_nonneg hk0] at this
    rw [← ENNReal.ofReal_toReal (measure_ne_top lam (Iic y))]
    exact ENNReal.ofReal_le_ofReal h3
  have hS := measure_le_of_Iic lam _ _ hbound
  have hS' : (lam {y | sig lam r k y ≤ b}).toReal ≤ c0 :=
    ENNReal.toReal_le_of_le_ofReal hc0 hS
  have hpow : (lam {y | sig lam r k y ≤ b}).toReal ^ k ≤ I / (x - b) := by
    calc _ ≤ c0 ^ k := pow_le_pow_left₀ ENNReal.toReal_nonneg hS' k
      _ = I / (x - b) := Real.rpow_inv_natCast_pow (by positivity) hk0
  rw [le_div_iff₀ hxb] at hpow
  linarith

/-- `H(s) = 0` for `s ≤ 0` when `λ(Iic 0) = 0`. -/
lemma Hf_nonpos (h0 : lam (Iic 0) = 0) (hk : 1 ≤ k) (s : ℝ) (hs : s ≤ 0) : Hf lam k s = 0 := by
  unfold Hf
  have : lam (Iic s) = 0 := measure_mono_null (Iic_subset_Iic.mpr hs) h0
  rw [this]; simp; omega

/-- Monotonicity of `σ` on `{H > 0} ∩ [r, ∞)`. -/
lemma sig_mono (y x : ℝ) (hry : r ≤ y) (hyx : y ≤ x) (hy : 0 < Hf lam k y) :
    sig lam r k y ≤ sig lam r k x := by
  have hx : 0 < Hf lam k x := lt_of_lt_of_le hy (Hf_mono lam k hyx)
  have hsy : sig lam r k y = y - (∫ s in r..y, Hf lam k s) / Hf lam k y := by
    unfold sig; rw [if_neg (not_lt.mpr hry), if_neg hy.ne']
  have hsx : sig lam r k x = x - (∫ s in r..x, Hf lam k s) / Hf lam k x := by
    unfold sig; rw [if_neg (not_lt.mpr (hry.trans hyx)), if_neg hx.ne']
  rw [hsy, hsx, ← intervalIntegral.integral_add_adjacent_intervals (Hf_ii lam k r y)
    (Hf_ii lam k y x)]
  set Iy := ∫ s in r..y, Hf lam k s
  have h1 := int_le_right lam k hyx
  have hIy : 0 ≤ Iy := int_nonneg lam k hry
  have h2 : Iy / Hf lam k x ≤ Iy / Hf lam k y :=
    div_le_div_of_nonneg_left hIy hy (Hf_mono lam k hyx)
  have h3 : (∫ s in y..x, Hf lam k s) / Hf lam k x ≤ x - y := by
    rw [div_le_iff₀ hx]; linarith
  rw [add_div]
  linarith

/-- `σ(x) ≥ 0` and `σ(x) ≥ r` for `x > 0`, `r ≤ x`, `H(x) > 0`. -/
lemma sig_ge (x : ℝ) (h0 : lam (Iic 0) = 0) (hk : 1 ≤ k) (hx0 : 0 < x) (hrx : r ≤ x)
    (hx : 0 < Hf lam k x) : r ≤ sig lam r k x ∧ 0 ≤ sig lam r k x := by
  have hsx : sig lam r k x = x - (∫ s in r..x, Hf lam k s) / Hf lam k x := by
    unfold sig; rw [if_neg (not_lt.mpr hrx), if_neg hx.ne']
  rw [hsx]
  have h1 := int_le_right lam k hrx
  have hA : (∫ s in r..x, Hf lam k s) / Hf lam k x ≤ x - r := by
    rw [div_le_iff₀ hx]; linarith
  refine ⟨by linarith, ?_⟩
  rcases le_total 0 r with hr0 | hr0
  · linarith
  · have hsplit := intervalIntegral.integral_add_adjacent_intervals (Hf_ii lam k r 0)
      (Hf_ii lam k 0 x)
    have hz : ∫ s in r..0, Hf lam k s = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
      · simp
      · intro s hs
        rw [uIcc_of_le hr0] at hs
        exact Hf_nonpos lam k h0 hk s hs.2
    have h2 := int_le_right lam k hx0.le
    have hB : (∫ s in r..x, Hf lam k s) / Hf lam k x ≤ x := by
      rw [div_le_iff₀ hx]; linarith
    linarith

/-- Claim B: the bid `σ(x)` attains the closed form. -/
lemma claimB (x : ℝ) (h0 : lam (Iic 0) = 0) (hk : 1 ≤ k) (hx0 : 0 < x) :
    gf lam r k x ≤ (if r ≤ sig lam r k x then
      (x - sig lam r k x) * (lam {y | sig lam r k y ≤ sig lam r k x}).toReal ^ k else 0) := by
  by_cases hrx : r ≤ x
  swap
  · push_neg at hrx
    unfold gf; rw [if_neg (not_le.mpr hrx)]
    split_ifs
    · have hs : sig lam r k x = x := by unfold sig; rw [if_pos hrx]
      linarith
    · exact le_refl _
  by_cases hH : Hf lam k x = 0
  · have hg : gf lam r k x = 0 := by
      unfold gf; rw [if_pos hrx]
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
      · simp
      · intro s hs
        rw [uIcc_of_le hrx] at hs
        exact le_antisymm (hH ▸ Hf_mono lam k hs.2) (Hf_nonneg lam k s)
    have hs : sig lam r k x = 0 := by unfold sig; rw [if_neg (not_lt.mpr hrx), if_pos hH]
    rw [hg, hs]
    split_ifs
    · simp only [sub_zero]; positivity
    · exact le_refl _
  have hpos : 0 < Hf lam k x := lt_of_le_of_ne (Hf_nonneg lam k x) (Ne.symm hH)
  obtain ⟨hrs, hs0⟩ := sig_ge lam r k x h0 hk hx0 hrx hpos
  rw [if_pos hrs]
  have hsx : sig lam r k x = x - (∫ s in r..x, Hf lam k s) / Hf lam k x := by
    unfold sig; rw [if_neg (not_lt.mpr hrx), if_neg hH]
  have hg : gf lam r k x = ∫ s in r..x, Hf lam k s := by unfold gf; rw [if_pos hrx]
  -- `λ{σ ≤ σ(x)} ≥ λ(Iic x)`
  have hsub : Iic x ∩ Ioi 0 ⊆ {y | sig lam r k y ≤ sig lam r k x} := by
    intro y ⟨hyx, hy0⟩
    simp only [mem_setOf_eq]
    by_cases hyr : y < r
    · have : sig lam r k y = y := by unfold sig; rw [if_pos hyr]
      rw [this]; linarith
    · push_neg at hyr
      by_cases hHy : Hf lam k y = 0
      · have : sig lam r k y = 0 := by unfold sig; rw [if_neg (not_lt.mpr hyr), if_pos hHy]
        rw [this]; exact hs0
      · exact sig_mono lam r k y x hyr hyx (lt_of_le_of_ne (Hf_nonneg lam k y) (Ne.symm hHy))
  have hmeas : lam (Iic x) ≤ lam {y | sig lam r k y ≤ sig lam r k x} := by
    have : Iic x ⊆ (Iic x ∩ Ioi 0) ∪ Iic 0 := by
      intro y hy
      by_cases h : 0 < y
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr (not_lt.mp h)
    calc lam (Iic x) ≤ lam ((Iic x ∩ Ioi 0) ∪ Iic 0) := measure_mono this
      _ ≤ lam (Iic x ∩ Ioi 0) + lam (Iic 0) := measure_union_le _ _
      _ = lam (Iic x ∩ Ioi 0) := by rw [h0, add_zero]
      _ ≤ _ := measure_mono hsub
  have hreal : Hf lam k x ≤ (lam {y | sig lam r k y ≤ sig lam r k x}).toReal ^ k := by
    unfold Hf
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg
      (ENNReal.toReal_mono (measure_ne_top _ _) hmeas) k
  rw [hg]
  have hd : 0 ≤ x - sig lam r k x := by
    rw [hsx]; have := int_nonneg lam k hrx; simp only [sub_sub_cancel]; positivity
  calc (∫ s in r..x, Hf lam k s) = (x - sig lam r k x) * Hf lam k x := by
        rw [hsx]; field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hreal hd

end RevEqAbs

namespace RevEqAbs

variable (lam : Measure ℝ) [IsProbabilityMeasure lam] (r : ℝ) (k : ℕ)

lemma sig_bounds (x : ℝ) (h0 : lam (Iic 0) = 0) (hk : 1 ≤ k) (hx0 : 0 < x) :
    0 ≤ sig lam r k x ∧ sig lam r k x ≤ x := by
  by_cases hxr : x < r
  · have : sig lam r k x = x := by unfold sig; rw [if_pos hxr]
    rw [this]; exact ⟨hx0.le, le_refl _⟩
  push_neg at hxr
  by_cases hH : Hf lam k x = 0
  · have : sig lam r k x = 0 := by unfold sig; rw [if_neg (not_lt.mpr hxr), if_pos hH]
    rw [this]; exact ⟨le_refl _, hx0.le⟩
  have hpos : 0 < Hf lam k x := lt_of_le_of_ne (Hf_nonneg lam k x) (Ne.symm hH)
  refine ⟨(sig_ge lam r k x h0 hk hx0 hxr hpos).2, ?_⟩
  have hsx : sig lam r k x = x - (∫ s in r..x, Hf lam k s) / Hf lam k x := by
    unfold sig; rw [if_neg (not_lt.mpr hxr), if_neg hH]
  rw [hsx]
  have := int_nonneg lam k hxr
  have : 0 ≤ (∫ s in r..x, Hf lam k s) / Hf lam k x := by positivity
  linarith

end RevEqAbs

open MeasureTheory Set

namespace ContextualAuctions.RevEquiv
namespace CFAux

open RevEqAbs

variable (M : Model) (μ : Buyer M → ℝ)

lemma measurable_val : Measurable (fun q : Buyer M × Context M => val M q.1 q.2) := by
  unfold val
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).mul
    ((measurable_pi_apply i).comp measurable_snd)

lemma measurable_paced (hμ : Measurable μ) :
    Measurable (fun q : Buyer M × Context M => paced M μ q.1 q.2) := by
  unfold paced
  exact (measurable_val M).div (measurable_const.add (hμ.comp measurable_fst))

lemma measurable_H [SFinite M.G] (hμ : Measurable μ) :
    Measurable (fun p : Context M × ℝ => H M μ p.1 p.2) := by
  have hE : MeasurableSet {q : (Context M × ℝ) × Buyer M | paced M μ q.2 q.1.1 ≤ q.1.2} := by
    apply measurableSet_le
    · exact (measurable_paced M μ hμ).comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
    · exact measurable_snd.comp measurable_fst
  have := measurable_measure_prodMk_left (ν := M.G) hE
  unfold H
  exact (this.ennreal_toReal).pow_const _

lemma measurable_intH [SFinite M.G] (hμ : Measurable μ) (hr : Measurable M.r) :
    Measurable (fun p : Context M × ℝ => ∫ s in (M.r p.1)..p.2, H M μ p.1 s) := by
  have hH := measurable_H M μ hμ
  -- integrand over Ioc (r α) x
  have h1 : ∀ (lo hi : Context M × ℝ → ℝ), Measurable lo → Measurable hi →
      Measurable (fun p : Context M × ℝ => ∫ s in Ioc (lo p) (hi p), H M μ p.1 s) := by
    intro lo hi hlo hhi
    have hS : MeasurableSet {q : (Context M × ℝ) × ℝ | lo q.1 < q.2 ∧ q.2 ≤ hi q.1} :=
      (measurableSet_lt (hlo.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hhi.comp measurable_fst))
    have hF : StronglyMeasurable (fun q : (Context M × ℝ) × ℝ =>
        ({q : (Context M × ℝ) × ℝ | lo q.1 < q.2 ∧ q.2 ≤ hi q.1}).indicator
          (fun q => H M μ q.1.1 q.2) q) := by
      apply Measurable.stronglyMeasurable
      exact (hH.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).indicator hS
    have := hF.integral_prod_right' (ν := (volume : Measure ℝ))
    convert this.measurable using 1
    funext p
    rw [← integral_indicator measurableSet_Ioc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [indicator, mem_setOf_eq, mem_Ioc]
  have hfst : Measurable (fun p : Context M × ℝ => M.r p.1) := hr.comp measurable_fst
  have := (h1 _ _ hfst measurable_snd).sub (h1 _ _ measurable_snd hfst)
  convert this using 1
  funext p
  rfl

lemma measurable_sigma [SFinite M.G] (hμ : Measurable μ) (hr : Measurable M.r) :
    Measurable (fun p : Context M × ℝ => sigma M μ p.1 p.2) := by
  have hH := measurable_H M μ hμ
  have hI := measurable_intH M μ hμ hr
  unfold sigma
  refine Measurable.ite (measurableSet_lt measurable_snd (hr.comp measurable_fst)) measurable_snd
    (Measurable.ite (measurableSet_eq_fun hH measurable_const) measurable_const
      (measurable_snd.sub (hI.div hH)))

lemma measurable_beta [SFinite M.G] (hμ : Measurable μ) (hr : Measurable M.r) :
    Measurable (fun q : Buyer M × Context M => beta M μ q.1 q.2) := by
  unfold beta
  exact (measurable_sigma M μ hμ hr).comp (measurable_snd.prodMk (measurable_paced M μ hμ))

end CFAux
end ContextualAuctions.RevEquiv

open MeasureTheory Set

namespace ContextualAuctions.RevEquiv
namespace CFAux

open RevEqAbs
open Classical

/-- The law of the paced value for context `α`. -/
noncomputable def lamA (M : Model) (μ : Buyer M → ℝ) (α : Context M) : Measure ℝ :=
  M.G.map (fun θ => paced M μ θ α)

lemma measurable_paced_left (M : Model) (μ : Buyer M → ℝ) (hμ : Measurable μ) (α : Context M) :
    Measurable (fun θ => paced M μ θ α) :=
  (measurable_paced M μ hμ).comp (measurable_id.prodMk measurable_const)

lemma lamA_prob (M : Model) [IsProbabilityMeasure M.G] (μ : Buyer M → ℝ) (hμ : Measurable μ)
    (α : Context M) : IsProbabilityMeasure (lamA M μ α) :=
  Measure.isProbabilityMeasure_map (measurable_paced_left M μ hμ α).aemeasurable

lemma H_eq (M : Model) (μ : Buyer M → ℝ) (hμ : Measurable μ) (α : Context M) :
    H M μ α = Hf (lamA M μ α) (M.n - 1) := by
  funext y
  unfold H Hf lamA
  rw [Measure.map_apply (measurable_paced_left M μ hμ α) measurableSet_Iic]
  rfl

lemma sigma_eq (M : Model) (μ : Buyer M → ℝ) (hμ : Measurable μ) (α : Context M) :
    sigma M μ α = sig (lamA M μ α) (M.r α) (M.n - 1) := by
  funext x
  unfold sigma sig
  rw [H_eq M μ hμ α]

lemma G_beta_le (M : Model) [SFinite M.G] (μ : Buyer M → ℝ) (hμ : Measurable μ)
    (hr : Measurable M.r) (α : Context M) (c : ℝ) :
    M.G {θ' | beta M μ θ' α ≤ c} = lamA M μ α {y | sig (lamA M μ α) (M.r α) (M.n - 1) y ≤ c} := by
  have hs : Measurable (fun x => sigma M μ α x) :=
    (measurable_sigma M μ hμ hr).comp (measurable_const.prodMk measurable_id)
  rw [sigma_eq M μ hμ α] at hs
  have hmap : lamA M μ α {y | sig (lamA M μ α) (M.r α) (M.n - 1) y ≤ c} =
      M.G ((fun θ => paced M μ θ α) ⁻¹' {y | sig (lamA M μ α) (M.r α) (M.n - 1) y ≤ c}) :=
    Measure.map_apply (measurable_paced_left M μ hμ α) (measurableSet_le hs measurable_const)
  rw [hmap]
  unfold beta
  rw [sigma_eq M μ hμ α]
  rfl

lemma val_pos (M : Model) (hM : M.Standing) (θ : Buyer M) (hθ : θ ∈ Theta M) (α : Context M)
    (hα : α ∈ M.A) : 0 < val M θ α := by
  unfold val
  haveI : Nonempty (Fin M.d) := ⟨⟨0, by have := hM.dim; omega⟩⟩
  apply Finset.sum_pos
  · intro i _
    exact mul_pos (hθ.1 i).1 (hM.positiveA hα i)
  · exact Finset.univ_nonempty

lemma lamA_Iic0 (M : Model) (hM : M.Standing) (μ : Buyer M → ℝ) (hμ : IsPacing M μ)
    (α : Context M) (hα : α ∈ M.A) : lamA M μ α (Iic 0) = 0 := by
  unfold lamA
  rw [Measure.map_apply (measurable_paced_left M μ hμ.1 α) measurableSet_Iic]
  apply measure_mono_null _ hM.supportedG
  intro θ hθ hθT
  simp only [mem_preimage, mem_Iic] at hθ
  have h1 := val_pos M hM θ hθT α hα
  have h2 := hμ.2 θ hθT
  have : 0 < paced M μ θ α := by unfold paced; positivity
  linarith

/-- The winning-probability formula for the inner integral. -/
lemma inner_eq (M : Model) [IsProbabilityMeasure M.G] (μ : Buyer M → ℝ) (hμ : Measurable μ)
    (hr : Measurable M.r) (b : Context M → ℝ) (α : Context M) (c : ℝ) :
    ∫ θs, (if wins M (beta M μ) b (α, θs) then c else 0) ∂(Measure.pi fun _ : Fin (M.n - 1) => M.G)
      = if M.r α ≤ b α then c * (M.G {θ' | beta M μ θ' α ≤ b α}).toReal ^ (M.n - 1) else 0 := by
  set S := {θ' | beta M μ θ' α ≤ b α}
  have hS : MeasurableSet S :=
    measurableSet_le ((measurable_beta M μ hμ hr).comp (measurable_id.prodMk measurable_const))
      measurable_const
  by_cases hrb : M.r α ≤ b α
  · rw [if_pos hrb]
    have : (fun θs : Fin (M.n - 1) → Buyer M => if wins M (beta M μ) b (α, θs) then c else 0) =
        (Set.univ.pi fun _ => S).indicator (fun _ => c) := by
      funext θs
      by_cases h : ∀ i, beta M μ (θs i) α ≤ b α
      · rw [if_pos ⟨hrb, h⟩, indicator_of_mem (by simpa [S] using h)]
      · rw [if_neg (fun h' => h h'.2), indicator_of_notMem (by simpa [S] using h)]
    rw [this, integral_indicator_const _ (MeasurableSet.univ_pi fun _ => hS)]
    simp only [smul_eq_mul, measureReal_def]
    rw [Measure.pi_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
    ring
  · rw [if_neg hrb]
    have : (fun θs : Fin (M.n - 1) → Buyer M => if wins M (beta M μ) b (α, θs) then c else 0) =
        fun _ => 0 := by
      funext θs
      rw [if_neg (fun h' => hrb h'.1)]
    rw [this, integral_zero]


lemma measurableSet_wins (M : Model) [SFinite M.G] (μ : Buyer M → ℝ) (hμ : Measurable μ)
    (hr : Measurable M.r) (b : Context M → ℝ) (hb : Measurable b) :
    MeasurableSet {ω : Context M × (Fin (M.n - 1) → Buyer M) | wins M (beta M μ) b ω} := by
  have e : {ω : Context M × (Fin (M.n - 1) → Buyer M) | wins M (beta M μ) b ω} =
      {ω | M.r ω.1 ≤ b ω.1} ∩ ⋂ i, {ω | beta M μ (ω.2 i) ω.1 ≤ b ω.1} := by
    ext ω; simp [wins]
  rw [e]
  refine (measurableSet_le (hr.comp measurable_fst) (hb.comp measurable_fst)).inter
    (MeasurableSet.iInter fun i => ?_)
  have h1 : Measurable (fun ω : Context M × (Fin (M.n - 1) → Buyer M) => (ω.2 i, ω.1)) :=
    ((measurable_pi_apply i).comp measurable_snd).prodMk measurable_fst
  exact measurableSet_le ((measurable_beta M μ hμ hr).comp h1) (hb.comp measurable_fst)

/-- The integrand after integrating out the competitors. -/
noncomputable def phiB (M : Model) (μ : Buyer M → ℝ) (θ : Buyer M) (t : ℝ) (b : Context M → ℝ)
    (α : Context M) : ℝ :=
  if M.r α ≤ b α then
    (val M θ α - (1 + t) * b α) * (M.G {θ' | beta M μ θ' α ≤ b α}).toReal ^ (M.n - 1) else 0

/-- The closed-form integrand. -/
noncomputable def gC (M : Model) (μ : Buyer M → ℝ) (θ : Buyer M) (t : ℝ) (α : Context M) : ℝ :=
  if M.r α ≤ val M θ α / (1 + t) then
    ∫ s in (M.r α)..(val M θ α / (1 + t)), H M μ α s else 0

lemma fubini_eq (M : Model) [IsProbabilityMeasure M.F] [IsProbabilityMeasure M.G]
    (μ : Buyer M → ℝ) (hμ : Measurable μ) (hr : Measurable M.r) (θ : Buyer M) (t : ℝ)
    (b : Context M → ℝ)
    (hi : Integrable (fun ω : Context M × (Fin (M.n - 1) → Buyer M) =>
      if wins M (beta M μ) b ω then val M θ ω.1 - (1 + t) * b ω.1 else 0) (P M)) :
    (∫ ω, (if wins M (beta M μ) b ω then val M θ ω.1 - (1 + t) * b ω.1 else 0) ∂P M)
      = ∫ α, phiB M μ θ t b α ∂M.F ∧ Integrable (phiB M μ θ t b) M.F := by
  haveI : SigmaFinite (Measure.pi fun _ : Fin (M.n - 1) => M.G) := Measure.pi.sigmaFinite _
  unfold P at hi ⊢
  have e : (fun α => ∫ θs, (fun ω : Context M × (Fin (M.n - 1) → Buyer M) =>
      if wins M (beta M μ) b ω then val M θ ω.1 - (1 + t) * b ω.1 else 0) (α, θs)
        ∂(Measure.pi fun _ : Fin (M.n - 1) => M.G)) = phiB M μ θ t b := by
    funext α
    exact inner_eq M μ hμ hr b α (val M θ α - (1 + t) * b α)
  refine ⟨?_, ?_⟩
  · rw [integral_prod _ hi, e]
  · have := hi.integral_prod_left
    rwa [e] at this

lemma gC_eq (M : Model) [IsProbabilityMeasure M.G] (μ : Buyer M → ℝ) (hμ : Measurable μ)
    (θ : Buyer M) (t : ℝ) (α : Context M) :
    gC M μ θ t α = gf (lamA M μ α) (M.r α) (M.n - 1) (val M θ α / (1 + t)) := by
  unfold gC gf
  rw [H_eq M μ hμ α]

lemma phi_le (M : Model) (hM : M.Standing) [IsProbabilityMeasure M.G] (μ : Buyer M → ℝ)
    (hμ : Measurable μ) (θ : Buyer M) (t : ℝ) (ht : 0 ≤ t) (b : Context M → ℝ) (α : Context M) :
    phiB M μ θ t b α ≤ (1 + t) * gC M μ θ t α := by
  haveI := lamA_prob M μ hμ α
  have hk : 1 ≤ M.n - 1 := by have := hM.buyers; omega
  have ht1 : 0 < 1 + t := by linarith
  rw [gC_eq M μ hμ θ t α]
  unfold phiB
  split_ifs with hrb
  · rw [G_beta_le M μ hμ hM.measurableR α]
    have hA := claimA (lamA M μ α) (M.r α) (M.n - 1) (val M θ α / (1 + t)) (b α) hrb hk
    have e : val M θ α - (1 + t) * b α = (1 + t) * (val M θ α / (1 + t) - b α) := by
      field_simp
    rw [e, mul_assoc]
    exact mul_le_mul_of_nonneg_left hA ht1.le
  · exact mul_nonneg ht1.le (gf_nonneg _ _ _ _)

/-- The candidate optimal bid `σ^μ_α(wᵀα / (1 + t))`. -/
noncomputable def bstar (M : Model) (μ : Buyer M → ℝ) (θ : Buyer M) (t : ℝ) (α : Context M) : ℝ :=
  sigma M μ α (val M θ α / (1 + t))

lemma phi_ge (M : Model) (hM : M.Standing) [IsProbabilityMeasure M.G] (μ : Buyer M → ℝ)
    (hμ : IsPacing M μ) (θ : Buyer M) (hθ : θ ∈ Theta M) (t : ℝ) (ht : 0 ≤ t)
    (α : Context M) (hα : α ∈ M.A) :
    (1 + t) * gC M μ θ t α ≤ phiB M μ θ t (bstar M μ θ t) α := by
  haveI := lamA_prob M μ hμ.1 α
  have hk : 1 ≤ M.n - 1 := by have := hM.buyers; omega
  have ht1 : 0 < 1 + t := by linarith
  have hx0 : 0 < val M θ α / (1 + t) := div_pos (val_pos M hM θ hθ α hα) ht1
  have hB := claimB (lamA M μ α) (M.r α) (M.n - 1) (val M θ α / (1 + t))
    (lamA_Iic0 M hM μ hμ α hα) hk hx0
  rw [gC_eq M μ hμ.1 θ t α]
  unfold phiB bstar
  rw [G_beta_le M μ hμ.1 hM.measurableR α, sigma_eq M μ hμ.1 α]
  set x := val M θ α / (1 + t)
  set sx := sig (lamA M μ α) (M.r α) (M.n - 1) x
  have e : val M θ α - (1 + t) * sx = (1 + t) * (x - sx) := by
    simp only [x]; field_simp
  split_ifs at hB ⊢ with h
  · rw [e, mul_assoc]
    exact mul_le_mul_of_nonneg_left hB ht1.le
  · simpa using mul_le_mul_of_nonneg_left hB ht1.le


lemma gC_nonneg (M : Model) [IsProbabilityMeasure M.G] (μ : Buyer M → ℝ) (hμ : Measurable μ)
    (θ : Buyer M) (t : ℝ) (α : Context M) : 0 ≤ gC M μ θ t α := by
  haveI := lamA_prob M μ hμ α
  rw [gC_eq M μ hμ θ t α]; exact gf_nonneg _ _ _ _

theorem closed_form (M : Model) (hM : M.Standing) (μ : Buyer M → ℝ) (hμ : IsPacing M μ)
    (θ : Buyer M) (hθ : θ ∈ Theta M) (t : ℝ) (ht : 0 ≤ t) :
    qDual M μ θ t =
      (1 + t) * ∫ α, (if M.r α ≤ val M θ α / (1 + t) then
        ∫ s in (M.r α)..(val M θ α / (1 + t)), H M μ α s else 0) ∂M.F + t * θ.2 := by
  haveI := hM.probF
  haveI := hM.probG
  have hr := hM.measurableR
  haveI : IsProbabilityMeasure (P M) := by unfold P; infer_instance
  have ht1 : 0 < 1 + t := by linarith
  have hk : 1 ≤ M.n - 1 := by have := hM.buyers; omega
  obtain ⟨R, hR⟩ := hM.boundedA.subset_closedBall 0
  set C := ∑ i, |θ.1 i| * R with hC
  have hval : ∀ α ∈ M.A, |val M θ α| ≤ C := by
    intro α hα
    have hα' : ‖α‖ ≤ R := by simpa using hR hα
    unfold val
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm α i).trans hα') (abs_nonneg _)
  have hAae : ∀ᵐ α ∂M.F, α ∈ M.A := ae_iff.mpr hM.supportedF
  have hAaeP : ∀ᵐ ω ∂P M, ω.1 ∈ M.A := by
    unfold P
    exact Measure.quasiMeasurePreserving_fst.ae hAae
  have hvm : Measurable (fun α : Context M => val M θ α) :=
    (measurable_val M).comp (measurable_const.prodMk measurable_id)
  have hbm : Measurable (bstar M μ θ t) :=
    (measurable_sigma M μ hμ.1 hr).comp (measurable_id.prodMk (hvm.div_const _))
  have hbb : ∀ α ∈ M.A, 0 ≤ bstar M μ θ t α ∧ bstar M μ θ t α ≤ val M θ α / (1 + t) := by
    intro α hα
    haveI := lamA_prob M μ hμ.1 α
    unfold bstar
    rw [sigma_eq M μ hμ.1 α]
    exact sig_bounds _ _ _ _ (lamA_Iic0 M hM μ hμ α hα) hk
      (div_pos (val_pos M hM θ hθ α hα) ht1)
  have hwm := measurableSet_wins M μ hμ.1 hr (bstar M μ θ t) hbm
  have hfi : Integrable (fun ω : Context M × (Fin (M.n - 1) → Buyer M) =>
      if wins M (beta M μ) (bstar M μ θ t) ω then
        val M θ ω.1 - (1 + t) * bstar M μ θ t ω.1 else 0) (P M) := by
    refine Integrable.mono' (integrable_const C) ?_ ?_
    · exact (Measurable.ite hwm ((hvm.comp measurable_fst).sub
        (measurable_const.mul (hbm.comp measurable_fst))) measurable_const).aestronglyMeasurable
    · filter_upwards [hAaeP] with ω hω
      have h1 := hbb ω.1 hω
      have h2 := hval ω.1 hω
      have h3 := val_pos M hM θ hθ ω.1 hω
      have h4 : (1 + t) * bstar M μ θ t ω.1 ≤ val M θ ω.1 := by
        have := h1.2; rw [le_div_iff₀ ht1] at this; linarith
      have h5 : 0 ≤ (1 + t) * bstar M μ θ t ω.1 := mul_nonneg ht1.le h1.1
      split_ifs
      · rw [Real.norm_eq_abs, abs_le]; rw [abs_le] at h2
        exact ⟨by linarith, by linarith⟩
      · simp only [norm_zero]; exact (abs_nonneg _).trans (h2)
  have hpay : Integrable (fun ω : Context M × (Fin (M.n - 1) → Buyer M) =>
      if wins M (beta M μ) (bstar M μ θ t) ω then bstar M μ θ t ω.1 else 0) (P M) := by
    refine Integrable.mono' (integrable_const C) ?_ ?_
    · exact (Measurable.ite hwm (hbm.comp measurable_fst) measurable_const).aestronglyMeasurable
    · filter_upwards [hAaeP] with ω hω
      have h1 := hbb ω.1 hω
      have h2 := hval ω.1 hω
      have h3 := val_pos M hM θ hθ ω.1 hω
      have h6 : val M θ ω.1 / (1 + t) ≤ val M θ ω.1 := div_le_self h3.le (by linarith)
      split_ifs
      · rw [Real.norm_eq_abs, abs_of_nonneg h1.1]
        exact h1.2.trans (h6.trans ((le_abs_self _).trans h2))
      · simp only [norm_zero]; exact (abs_nonneg _).trans h2
  have hadm : Admissible M (beta M μ) (bstar M μ θ t) :=
    ⟨hbm, fun α hα => (hbb α hα).1, hpay⟩
  obtain ⟨hF1, hφi⟩ := fubini_eq M μ hμ.1 hr θ t (bstar M μ θ t) hfi
  have hφeq : phiB M μ θ t (bstar M μ θ t) =ᵐ[M.F] fun α => (1 + t) * gC M μ θ t α := by
    filter_upwards [hAae] with α hα
    exact le_antisymm (phi_le M hM μ hμ.1 θ t ht _ α) (phi_ge M hM μ hμ θ hθ t ht α hα)
  have hgi : Integrable (fun α => (1 + t) * gC M μ θ t α) M.F := hφi.congr hφeq
  unfold qDual
  congr 1
  change _ = (1 + t) * ∫ α, gC M μ θ t α ∂M.F
  apply IsGreatest.csSup_eq
  refine ⟨⟨bstar M μ θ t, hadm, ?_⟩, ?_⟩
  · rw [hF1, integral_congr_ae hφeq, integral_const_mul]
  · rintro v ⟨b, hb, rfl⟩
    by_cases hi : Integrable (fun ω : Context M × (Fin (M.n - 1) → Buyer M) =>
        if wins M (beta M μ) b ω then val M θ ω.1 - (1 + t) * b ω.1 else 0) (P M)
    · obtain ⟨h1, h2⟩ := fubini_eq M μ hμ.1 hr θ t b hi
      rw [h1, ← integral_const_mul]
      exact integral_mono h2 hgi (fun α => phi_le M hM μ hμ.1 θ t ht b α)
    · rw [integral_undef hi]
      exact mul_nonneg ht1.le (integral_nonneg fun α => gC_nonneg M μ hμ.1 θ t α)

end CFAux
end ContextualAuctions.RevEquiv


open MeasureTheory ContextualAuctions.RevEquiv

theorem solution (M : Model) (hM : M.Standing) (μ : Buyer M → ℝ) (hμ : IsPacing M μ)
    (θ : Buyer M) (hθ : θ ∈ Theta M) (t : ℝ) (ht : 0 ≤ t) :
    qDual M μ θ t =
      (1 + t) * ∫ α, (if M.r α ≤ val M θ α / (1 + t) then
        ∫ s in (M.r α)..(val M θ α / (1 + t)), H M μ α s else 0) ∂M.F + t * θ.2 :=
  CFAux.closed_form M hM μ hμ θ hθ t ht
