-- Prove2me | solution 1 for ConvexityBound.lindelofMu_convexOn
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:33:38.340303+00:00
-- url     : https://prove2.me/submissions/bc373549-699f-496b-8528-fafcfa19d755

import Mathlib
import Definitions.Def_ConvexityBound_LindelofMu
import Theorems.Thm_MasulloGRH_halfStrip_convexity

open scoped ENNReal

set_option autoImplicit false

namespace Sol_ConvexityBound_lindelofMu_convexOn

open Filter Asymptotics ConvexityBound
open scoped NNReal

/-- Eventually along `cocompact ℝ` means: for all `t` with `|t|` large. -/
lemma eventually_cocompact_iff (P : ℝ → Prop) :
    (∀ᶠ t in cocompact ℝ, P t) ↔ ∃ T : ℝ, ∀ t : ℝ, T ≤ |t| → P t := by
  constructor
  · intro h
    obtain ⟨K, hK, hPK⟩ := (Filter.hasBasis_cocompact).eventually_iff.mp h
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    refine ⟨R + 1, fun t ht => hPK ?_⟩
    intro htK
    have h1 := hR htK
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
    linarith
  · rintro ⟨T, hT⟩
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop T] with t ht
    exact hT t (by simpa [Real.norm_eq_abs] using ht)

lemma lindelofMu_le_of_isBigO (f : ℂ → ℂ) (σ : ℝ) (k : ℝ≥0)
    (hk : (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) =O[cocompact ℝ]
      fun t : ℝ => |t| ^ (k : ℝ)) :
    lindelofMu f σ ≤ k :=
  sInf_le ⟨k, hk, rfl⟩

lemma isBigO_of_bound (f : ℂ → ℂ) (σ C T e : ℝ)
    (h : ∀ t : ℝ, T ≤ |t| → ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * |t| ^ e) :
    (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) =O[cocompact ℝ] fun t : ℝ => |t| ^ e := by
  refine IsBigO.of_bound C ?_
  rw [eventually_cocompact_iff]
  refine ⟨T, fun t ht => ?_⟩
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg t) e)]
  exact h t ht

lemma bound_of_isBigO (f : ℂ → ℂ) (σ e : ℝ)
    (h : (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) =O[cocompact ℝ]
      fun t : ℝ => |t| ^ e) :
    ∃ C T : ℝ, ∀ t : ℝ, T ≤ |t| → ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * |t| ^ e := by
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨T, hT⟩ := (eventually_cocompact_iff _).mp hC
  refine ⟨C, T, fun t ht => ?_⟩
  have h1 := hT t ht
  rwa [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg t) e)] at h1

lemma lindelofMu_ne_top_of_bound (f : ℂ → ℂ) (σ M C T : ℝ)
    (h : ∀ t : ℝ, T ≤ |t| → ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * |t| ^ M) :
    lindelofMu f σ ≠ ⊤ := by
  have key : ∀ t : ℝ, max T 1 ≤ |t| →
      ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ |C| * |t| ^ ((Real.toNNReal M : ℝ≥0) : ℝ) := by
    intro t ht
    have h1 : 1 ≤ |t| := le_trans (le_max_right _ _) ht
    have h2 := h t (le_trans (le_max_left _ _) ht)
    rw [Real.coe_toNNReal']
    calc ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * |t| ^ M := h2
      _ ≤ |C| * |t| ^ M :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (abs_nonneg t) M)
      _ ≤ |C| * |t| ^ (max M 0) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 (le_max_left _ _))
            (abs_nonneg C)
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top
    (lindelofMu_le_of_isBigO f σ _ (isBigO_of_bound f σ _ _ _ key))

lemma exists_lt_of_ne_top (f : ℂ → ℂ) (σ : ℝ) (h : lindelofMu f σ ≠ ⊤) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℝ≥0, ((fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) =O[cocompact ℝ]
      fun t : ℝ => |t| ^ (k : ℝ)) ∧ (k : ℝ) < (lindelofMu f σ).toReal + ε := by
  have hlt : lindelofMu f σ < lindelofMu f σ + ENNReal.ofReal ε :=
    ENNReal.lt_add_right h (ENNReal.ofReal_pos.mpr hε).ne'
  obtain ⟨b, ⟨k, hk, rfl⟩, hb⟩ := sInf_lt_iff.mp hlt
  refine ⟨k, hk, ?_⟩
  have h1 := ENNReal.toReal_strict_mono (ENNReal.add_ne_top.mpr ⟨h, ENNReal.ofReal_ne_top⟩) hb
  rwa [ENNReal.toReal_add h ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε.le,
    ENNReal.coe_toReal] at h1

lemma convex_step (f : ℂ → ℂ) (x y : ℝ) (hxy : x < y) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (M C T : ℝ)
    (hfxy : ∀ s : ℂ, x ≤ s.re → s.re ≤ y → T ≤ |s.im| →
      DifferentiableAt ℂ f s ∧ ‖f s‖ ≤ C * |s.im| ^ M)
    (k₁ k₂ : ℝ≥0)
    (h₁ : (fun t : ℝ => f ((x : ℂ) + (t : ℂ) * Complex.I)) =O[cocompact ℝ]
      fun t : ℝ => |t| ^ (k₁ : ℝ))
    (h₂ : (fun t : ℝ => f ((y : ℂ) + (t : ℂ) * Complex.I)) =O[cocompact ℝ]
      fun t : ℝ => |t| ^ (k₂ : ℝ)) :
    (lindelofMu f (a * x + b * y)).toReal ≤ a * k₁ + b * k₂ := by
  obtain ⟨C₁, T₁, hC₁⟩ := bound_of_isBigO f x _ h₁
  obtain ⟨C₂, T₂, hC₂⟩ := bound_of_isBigO f y _ h₂
  have hT : T ≤ max (max T T₁) (max T₂ 1) := le_trans (le_max_left _ _) (le_max_left _ _)
  have hT₁ : T₁ ≤ max (max T T₁) (max T₂ 1) := le_trans (le_max_right _ _) (le_max_left _ _)
  have hT₂ : T₂ ≤ max (max T T₁) (max T₂ 1) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hT₀ : 1 ≤ max (max T T₁) (max T₂ 1) := le_trans (le_max_right _ _) (le_max_right _ _)
  have hA : C ≤ max (max C C₁) C₂ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hA₁ : C₁ ≤ max (max C C₁) C₂ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hA₂ : C₂ ≤ max (max C C₁) C₂ := le_max_right _ _
  obtain ⟨C', T', hC'⟩ := MasulloGRH.halfStrip_convexity f x y k₁ k₂ M (max (max C C₁) C₂)
    (max (max T T₁) (max T₂ 1)) hxy hT₀
    (fun s h1 h2 h3 => (hfxy s h1 h2 (le_trans hT h3)).1)
    (fun s h1 h2 h3 => le_trans (hfxy s h1 h2 (le_trans hT h3)).2
      (mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg (abs_nonneg _) _)))
    (fun t ht => le_trans (hC₁ t (le_trans hT₁ ht))
      (mul_le_mul_of_nonneg_right hA₁ (Real.rpow_nonneg (abs_nonneg _) _)))
    (fun t ht => le_trans (hC₂ t (le_trans hT₂ ht))
      (mul_le_mul_of_nonneg_right hA₂ (Real.rpow_nonneg (abs_nonneg _) _)))
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr hxy.ne'
  have hexp : k₁ * (y - (a * x + b * y)) / (y - x) + k₂ * ((a * x + b * y) - x) / (y - x)
      = a * k₁ + b * k₂ := by
    rw [← add_div, div_eq_iff hyx]
    linear_combination (-( (k₁ : ℝ) * y - k₂ * x)) * hab
  have key : ∀ t : ℝ, T' ≤ |t| →
      ‖f (((a * x + b * y : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C' * |t| ^ (a * k₁ + b * k₂) := by
    intro t ht
    have hs_re : (((a * x + b * y : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = a * x + b * y := by simp
    have hs_im : (((a * x + b * y : ℝ) : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    have e1 : a * x + b * y - x = b * (y - x) := by linear_combination x * hab
    have e2 : y - (a * x + b * y) = a * (y - x) := by linear_combination (-y) * hab
    have p1 := mul_pos hb (sub_pos.mpr hxy)
    have p2 := mul_pos ha (sub_pos.mpr hxy)
    have h1 := hC' (((a * x + b * y : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      (by rw [hs_re]; linarith) (by rw [hs_re]; linarith) (by rw [hs_im]; exact ht)
    rw [hs_re, hs_im, hexp] at h1
    exact h1
  have hnn : 0 ≤ a * (k₁ : ℝ) + b * k₂ := by positivity
  have hle := lindelofMu_le_of_isBigO f (a * x + b * y) (Real.toNNReal (a * k₁ + b * k₂))
    (by rw [Real.coe_toNNReal _ hnn]; exact isBigO_of_bound f _ C' T' _ key)
  have h2 := ENNReal.toReal_mono ENNReal.coe_ne_top hle
  rwa [ENNReal.coe_toReal, Real.coe_toNNReal _ hnn] at h2

end Sol_ConvexityBound_lindelofMu_convexOn

open Sol_ConvexityBound_lindelofMu_convexOn in
open ConvexityBound in
theorem solution (f : ℂ → ℂ) (I : Set ℝ) (hI : IsOpen I) (hI' : I.OrdConnected)
    (hf : ∀ σ₁ σ₂ : ℝ, σ₁ ∈ I → σ₂ ∈ I → σ₁ ≤ σ₂ →
      ∃ M C T : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T ≤ |s.im| →
        DifferentiableAt ℂ f s ∧ ‖f s‖ ≤ C * |s.im| ^ M) :
    (∀ σ ∈ I, lindelofMu f σ ≠ ⊤) ∧
      ConvexOn ℝ I (fun σ : ℝ => (lindelofMu f σ).toReal) ∧
      ContinuousOn (fun σ : ℝ => (lindelofMu f σ).toReal) I := by
  have hfin : ∀ σ ∈ I, lindelofMu f σ ≠ ⊤ := by
    intro σ hσ
    obtain ⟨M, C, T, h⟩ := hf σ σ hσ hσ le_rfl
    refine lindelofMu_ne_top_of_bound f σ M C T (fun t ht => ?_)
    have hs_re : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
    have hs_im : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    have h1 := (h ((σ : ℂ) + (t : ℂ) * Complex.I) (le_of_eq hs_re.symm) (le_of_eq hs_re)
      (by rw [hs_im]; exact ht)).2
    rwa [hs_im] at h1
  have hconv : ConvexOn ℝ I (fun σ : ℝ => (lindelofMu f σ).toReal) := by
    refine LinearOrder.convexOn_of_lt hI'.convex ?_
    intro x hx y hy hxy a b ha hb hab
    simp only [smul_eq_mul]
    obtain ⟨M, C, T, h⟩ := hf x y hx hy hxy.le
    refine le_of_forall_pos_lt_add (fun ε hε => ?_)
    obtain ⟨k₁, hk₁, hk₁lt⟩ := exists_lt_of_ne_top f x (hfin x hx) ε hε
    obtain ⟨k₂, hk₂, hk₂lt⟩ := exists_lt_of_ne_top f y (hfin y hy) ε hε
    have h0 := convex_step f x y hxy a b ha hb hab M C T h k₁ k₂ hk₁ hk₂
    have h1 := mul_lt_mul_of_pos_left hk₁lt ha
    have h2 := mul_lt_mul_of_pos_left hk₂lt hb
    have h3 : a * ε + b * ε = ε := by rw [← add_mul, hab, one_mul]
    nlinarith
  exact ⟨hfin, hconv, hconv.continuousOn hI⟩
