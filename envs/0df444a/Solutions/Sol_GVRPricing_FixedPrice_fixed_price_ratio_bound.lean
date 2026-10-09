-- Prove2me | solution 1 for GVRPricing.FixedPrice.fixed_price_ratio_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T14:06:17.870218+00:00
-- url     : https://prove2.me/submissions/e38c1c66-36ee-4972-9f29-26d2137143b4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GVRPricing_FixedPrice_Model
import Definitions.Def_GVRPricing_FixedPrice_SalesProcess
import Definitions.Def_GVRPricing_FixedPrice_Deterministic
import Theorems.Thm_GVRPricing_FixedPrice_optValue_le_detValue
import Theorems.Thm_GVRPricing_FixedPrice_deterministic_solution
import Theorems.Thm_GVRPricing_FixedPrice_fp_scarce_bound
import Theorems.Thm_GVRPricing_FixedPrice_fp_abundant_bound

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace BC8F
open GVRPricing.FixedPrice

lemma rstar_pos (M : Model) (hl : 0 < M.lstar) : 0 < M.rstar := by
  have hmax := M.isLeast_lstar.1.2
  have h0 : M.r 0 = 0 := by simp [Model.r]
  have hge : 0 ≤ M.rstar := by
    have := hmax 0 M.zero_mem
    simpa [Model.rstar, Model.r] using this
  rcases hge.lt_or_eq with h | h
  · exact h
  · exfalso
    have hmem : (0:ℝ) ∈ {l ∈ M.Λ | ∀ m ∈ M.Λ, m * M.p m ≤ l * M.p l} := by
      refine ⟨M.zero_mem, fun m hm => ?_⟩
      have := hmax m hm
      have h' : M.lstar * M.p M.lstar = 0 := by simpa [Model.rstar, Model.r] using h.symm
      simpa [h'] using this
    have := M.isLeast_lstar.2 hmem
    linarith

lemma lD_mem (M : Model) (n : ℕ) (t : ℝ) (ht : 0 < t) :
    min M.lstar ((n : ℝ) / t) ∈ M.Λ := by
  have hls := M.isLeast_lstar.1.1
  have h0 : (0:ℝ) ≤ min M.lstar ((n : ℝ) / t) :=
    le_min (M.nonneg _ hls) (by positivity)
  exact M.ordConnected.out M.zero_mem hls ⟨h0, min_le_left _ _⟩

/-- `r` on `[0, λ*]` is at least the chord `θ r*`. -/
lemma r_ge_chord (M : Model) (hl : 0 < M.lstar) (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ M.lstar) :
    x / M.lstar * M.rstar ≤ M.r x := by
  have hls := M.isLeast_lstar.1.1
  set θ := x / M.lstar with hθ
  have hθ0 : 0 ≤ θ := div_nonneg hx0 hl.le
  have hθ1 : θ ≤ 1 := (div_le_one hl).2 hx
  have hc := M.concaveOn.2 M.zero_mem hls (sub_nonneg.2 hθ1) hθ0 (by ring)
  have hx' : (1 - θ) • (0:ℝ) + θ • M.lstar = x := by
    simp [smul_eq_mul, hθ]; field_simp
  rw [hx'] at hc
  simpa [smul_eq_mul, Model.r, Model.rstar] using hc

theorem fixed_price_ratio_bound_of (M : Model) (n : ℕ) (t : ℝ) (hn : 1 ≤ n) (ht : 0 < t)
    (hl : 0 < M.lstar)
    (hC1 : optValue M n t ≤ ENNReal.ofReal (t * M.r (min M.lstar ((n : ℝ) / t))))
    (hC3 : (n : ℝ) < M.lstar * t →
      ENNReal.ofReal (n * M.p (n / t) * (1 - 1 / (2 * Real.sqrt n))) ≤ fpValue M n t)
    (hC4 : M.lstar * t ≤ n →
      ENNReal.ofReal (M.pstar * (M.lstar * t -
        (Real.sqrt (M.lstar * t + ((n : ℝ) - M.lstar * t) ^ 2) - ((n : ℝ) - M.lstar * t)) / 2))
        ≤ fpValue M n t) :
    optValue M n t ≠ ∞ ∧ 0 < optValue M n t ∧
    (fpValue M n t).toReal / (optValue M n t).toReal ≤
      (ofpValue M n t).toReal / (optValue M n t).toReal ∧
    1 - 1 / (2 * Real.sqrt (min (n : ℝ) (M.lstar * t))) ≤
      (fpValue M n t).toReal / (optValue M n t).toReal := by
  set D := t * M.r (min M.lstar ((n : ℝ) / t)) with hD
  set k := 1 - 1 / (2 * Real.sqrt (min (n : ℝ) (M.lstar * t))) with hk
  have hmem := lD_mem M n t ht
  -- F ≤ O ≤ J
  have hFO : fpValue M n t ≤ ofpValue M n t := by
    unfold fpValue ofpValue
    exact le_iSup₂ (f := fun c (_ : c ∈ M.Λ) => (constPolicy M c).expectedRevenue n t) _ hmem
  have hOJ : ofpValue M n t ≤ optValue M n t := by
    unfold ofpValue optValue
    exact iSup₂_le fun c _ => le_iSup (fun u : Policy M => u.expectedRevenue n t) (constPolicy M c)
  have hJfin : optValue M n t ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hC1
  have hOfin : ofpValue M n t ≠ ∞ := ne_top_of_le_ne_top hJfin hOJ
  have hFfin : fpValue M n t ≠ ∞ := ne_top_of_le_ne_top hOfin hFO
  have hrs := rstar_pos M hl
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  -- lower bound L with 0 < L, D * k ≤ L, ofReal L ≤ F
  obtain ⟨L, hLpos, hDL, hLF⟩ : ∃ L : ℝ, 0 < L ∧ D * k ≤ L ∧ ENNReal.ofReal L ≤ fpValue M n t := by
    rcases lt_or_ge (n : ℝ) (M.lstar * t) with hs | ha
    · -- scarce
      have hnt : (n : ℝ) / t < M.lstar := by rwa [div_lt_iff₀ ht]
      have hmin : min M.lstar ((n : ℝ) / t) = n / t := min_eq_right hnt.le
      have hm : min (n : ℝ) (M.lstar * t) = n := min_eq_left hs.le
      have hnt0 : 0 < (n : ℝ) / t := by positivity
      have hr := r_ge_chord M hl (n / t) hnt0.le hnt.le
      have hrpos : 0 < M.r (n / t) := lt_of_lt_of_le (by positivity) hr
      have hsq : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact hn1
      have hkpos : 0 < 1 - 1 / (2 * Real.sqrt n) := by
        have : 1 / (2 * Real.sqrt n) ≤ 1 / 2 := by
          apply one_div_le_one_div_of_le (by norm_num); linarith
        linarith
      have hDeq : D = n * M.p (n / t) := by
        rw [hD, hmin]; simp only [Model.r]; field_simp
      refine ⟨n * M.p (n / t) * (1 - 1 / (2 * Real.sqrt n)), ?_, ?_, hC3 hs⟩
      · rw [← hDeq]; rw [hD, hmin]; positivity
      · rw [hk, hm, hDeq]
    · -- abundant
      have hmin : min M.lstar ((n : ℝ) / t) = M.lstar := min_eq_left (by rwa [le_div_iff₀ ht])
      have hm : min (n : ℝ) (M.lstar * t) = M.lstar * t := min_eq_right ha
      set a := M.lstar * t with ha_def
      have hapos : 0 < a := by positivity
      set d := (n : ℝ) - a with hd_def
      have hd0 : 0 ≤ d := by linarith
      have hps : 0 < M.pstar := by
        have : M.rstar = M.lstar * M.pstar := rfl
        rw [this] at hrs; exact pos_of_mul_pos_right hrs hl.le
      have hDeq : D = M.pstar * a := by
        rw [hD, hmin]; simp only [Model.r, Model.pstar]; rw [ha_def]; ring
      refine ⟨M.pstar * (a - (Real.sqrt (a + d ^ 2) - d) / 2), ?_, ?_, hC4 ha⟩
      · apply mul_pos hps
        have hlt : Real.sqrt (a + d ^ 2) < 2 * a + d := by
          rw [Real.sqrt_lt' (by linarith)]
          nlinarith
        linarith
      · rw [hk, hm, hDeq]
        have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 hapos
        have hsa2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt hapos.le
        have hle : Real.sqrt (a + d ^ 2) ≤ Real.sqrt a + d := by
          rw [Real.sqrt_le_left (by positivity)]
          nlinarith
        have : a * (1 - 1 / (2 * Real.sqrt a)) = a - Real.sqrt a / 2 := by
          have e : a / (2 * Real.sqrt a) = Real.sqrt a / 2 := by
            rw [div_eq_div_iff (by positivity) (by norm_num)]
            linear_combination (-2:ℝ) * hsa2
          calc a * (1 - 1 / (2 * Real.sqrt a)) = a - a / (2 * Real.sqrt a) := by ring
            _ = a - Real.sqrt a / 2 := by rw [e]
        rw [mul_assoc, this]
        apply mul_le_mul_of_nonneg_left _ hps.le
        linarith
  have hFpos : 0 < fpValue M n t := lt_of_lt_of_le (ENNReal.ofReal_pos.2 hLpos) hLF
  have hJpos : 0 < optValue M n t := lt_of_lt_of_le hFpos (hFO.trans hOJ)
  refine ⟨hJfin, hJpos, ?_, ?_⟩
  · have hJr : 0 ≤ (optValue M n t).toReal := ENNReal.toReal_nonneg
    exact div_le_div_of_nonneg_right (ENNReal.toReal_mono hOfin hFO) hJr
  · have hJr : 0 < (optValue M n t).toReal := ENNReal.toReal_pos hJpos.ne' hJfin
    have hJD : (optValue M n t).toReal ≤ D := by
      have hD0 : 0 ≤ D := by
        have := ENNReal.toReal_nonneg (a := optValue M n t)
        by_contra h; rw [not_le] at h
        have : optValue M n t ≤ 0 := by
          rw [ENNReal.ofReal_of_nonpos h.le] at hC1; exact hC1
        exact absurd hJpos (not_lt.2 this)
      exact (ENNReal.toReal_le_toReal hJfin ENNReal.ofReal_ne_top).2 hC1 |>.trans
        (ENNReal.toReal_ofReal hD0).le
    have hLF' : L ≤ (fpValue M n t).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hFfin).1 hLF
    rw [le_div_iff₀ hJr]
    rcases le_total k 0 with hk0 | hk0
    · nlinarith [ENNReal.toReal_nonneg (a := fpValue M n t)]
    · calc k * (optValue M n t).toReal ≤ k * D := mul_le_mul_of_nonneg_left hJD hk0
        _ = D * k := by ring
        _ ≤ L := hDL
        _ ≤ _ := hLF'

end BC8F

open GVRPricing.FixedPrice in
theorem solution (M : Model) (n : ℕ) (t : ℝ) (hn : 1 ≤ n) (ht : 0 < t)
    (hl : 0 < M.lstar) :
    optValue M n t ≠ ∞ ∧ 0 < optValue M n t ∧
    (fpValue M n t).toReal / (optValue M n t).toReal ≤
      (ofpValue M n t).toReal / (optValue M n t).toReal ∧
    1 - 1 / (2 * Real.sqrt (min (n : ℝ) (M.lstar * t))) ≤
      (fpValue M n t).toReal / (optValue M n t).toReal := by
  have hC1 : optValue M n t ≤ ENNReal.ofReal (t * M.r (min M.lstar ((n : ℝ) / t))) := by
    have h1 := optValue_le_detValue M n t ht.le
    have h2 := (deterministic_solution M (n : ℝ) t (Nat.cast_nonneg n) ht).2.2.1
    rw [h2] at h1
    exact h1
  exact BC8F.fixed_price_ratio_bound_of M n t hn ht hl hC1
    (fun h => (fp_scarce_bound M n t hn ht h).1)
    (fun h => (fp_abundant_bound M n t ht hl h).1)
