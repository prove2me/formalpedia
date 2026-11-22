-- Prove2me | solution 1 for ConvexityBound.norm_le_rpow_lindelofMu_add
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:38:25.417739+00:00
-- url     : https://prove2.me/submissions/69693553-1d23-42ef-8933-3b1a67bf015e

import Mathlib
import Definitions.Def_ConvexityBound_LindelofMu
import Theorems.Thm_MasulloGRH_halfStrip_convexity
import Theorems.Thm_ConvexityBound_lindelofMu_convexOn

open scoped ENNReal

set_option autoImplicit false

namespace Sol_ConvexityBound_norm_le_rpow_lindelofMu_add

open Filter Asymptotics ConvexityBound
open scoped NNReal Topology

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

lemma bound_of_isBigO (f : ℂ → ℂ) (σ e : ℝ)
    (h : (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) =O[cocompact ℝ]
      fun t : ℝ => |t| ^ e) :
    ∃ C T : ℝ, ∀ t : ℝ, T ≤ |t| → ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * |t| ^ e := by
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨T, hT⟩ := (eventually_cocompact_iff _).mp hC
  refine ⟨C, T, fun t ht => ?_⟩
  have h1 := hT t ht
  rwa [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg t) e)] at h1

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

/-- Phragmén–Lindelöf on a half-strip `x ≤ Re s ≤ y`, with the interpolated exponent bounded by
the larger of the two edge exponents. -/
lemma strip_bound_max (f : ℂ → ℂ) (x y : ℝ) (hxy : x < y) (M C T : ℝ)
    (hfxy : ∀ s : ℂ, x ≤ s.re → s.re ≤ y → T ≤ |s.im| →
      DifferentiableAt ℂ f s ∧ ‖f s‖ ≤ C * |s.im| ^ M)
    (k₁ k₂ : ℝ≥0)
    (h₁ : (fun t : ℝ => f ((x : ℂ) + (t : ℂ) * Complex.I)) =O[cocompact ℝ]
      fun t : ℝ => |t| ^ (k₁ : ℝ))
    (h₂ : (fun t : ℝ => f ((y : ℂ) + (t : ℂ) * Complex.I)) =O[cocompact ℝ]
      fun t : ℝ => |t| ^ (k₂ : ℝ)) :
    ∃ C' T' : ℝ, ∀ s : ℂ, x ≤ s.re → s.re ≤ y → T' ≤ |s.im| →
      ‖f s‖ ≤ C' * |s.im| ^ (max (k₁ : ℝ) k₂) := by
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
  refine ⟨|C'|, max T' 1, fun s h1 h2 h3 => ?_⟩
  have hT'1 : T' ≤ |s.im| := le_trans (le_max_left _ _) h3
  have h1s : 1 ≤ |s.im| := le_trans (le_max_right _ _) h3
  have hb := hC' s h1 h2 hT'1
  have hexp : (k₁ : ℝ) * (y - s.re) / (y - x) + (k₂ : ℝ) * (s.re - x) / (y - x)
      ≤ max (k₁ : ℝ) k₂ := by
    rw [← add_div, div_le_iff₀ (sub_pos.mpr hxy)]
    have e1 := mul_le_mul_of_nonneg_right (le_max_left (k₁ : ℝ) k₂) (sub_nonneg.mpr h2)
    have e2 := mul_le_mul_of_nonneg_right (le_max_right (k₁ : ℝ) k₂) (sub_nonneg.mpr h1)
    nlinarith
  calc ‖f s‖ ≤ C' * |s.im| ^ ((k₁ : ℝ) * (y - s.re) / (y - x)
        + (k₂ : ℝ) * (s.re - x) / (y - x)) := hb
    _ ≤ |C'| * |s.im| ^ ((k₁ : ℝ) * (y - s.re) / (y - x)
        + (k₂ : ℝ) * (s.re - x) / (y - x)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (abs_nonneg _) _)
    _ ≤ |C'| * |s.im| ^ (max (k₁ : ℝ) k₂) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1s hexp) (abs_nonneg _)

end Sol_ConvexityBound_norm_le_rpow_lindelofMu_add

open Sol_ConvexityBound_norm_le_rpow_lindelofMu_add in
open ConvexityBound in
theorem solution (f : ℂ → ℂ) (I : Set ℝ) (hI : IsOpen I)
    (hI' : I.OrdConnected)
    (hf : ∀ σ₁ σ₂ : ℝ, σ₁ ∈ I → σ₂ ∈ I → σ₁ ≤ σ₂ →
      ∃ M C T : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T ≤ |s.im| →
        DifferentiableAt ℂ f s ∧ ‖f s‖ ≤ C * |s.im| ^ M)
    (σ₁ σ₂ : ℝ) (h₁ : σ₁ ∈ I) (h₂ : σ₂ ∈ I) (h₁₂ : σ₁ ≤ σ₂) (ε : ℝ) (hε : 0 < ε) :
    ∃ C T : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T ≤ |s.im| →
      ‖f s‖ ≤ C * |s.im| ^ ((lindelofMu f s.re).toReal + ε) := by
  obtain ⟨hfin, -, hcont⟩ := ConvexityBound.lindelofMu_convexOn f I hI hI' hf
  have key : ∃ C T : ℝ, ∀ s : ℂ, s.re ∈ Set.Icc σ₁ σ₂ → T ≤ |s.im| →
      ‖f s‖ ≤ C * |s.im| ^ ((lindelofMu f s.re).toReal + ε) := by
    refine isCompact_Icc.induction_on
      (p := fun S => ∃ C T : ℝ, ∀ s : ℂ, s.re ∈ S → T ≤ |s.im| →
        ‖f s‖ ≤ C * |s.im| ^ ((lindelofMu f s.re).toReal + ε)) ?_ ?_ ?_ ?_
    · exact ⟨0, 0, fun s hs _ => by simp at hs⟩
    · rintro S S' hSS' ⟨C, T, h⟩
      exact ⟨C, T, fun s hs hT => h s (hSS' hs) hT⟩
    · rintro S S' ⟨C, T, h⟩ ⟨C', T', h'⟩
      refine ⟨max C C', max T T', fun s hs hT => ?_⟩
      rcases hs with hs | hs
      · exact le_trans (h s hs (le_trans (le_max_left _ _) hT))
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _))
      · exact le_trans (h' s hs (le_trans (le_max_right _ _) hT))
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (abs_nonneg _) _))
    · intro x hx
      have hxI : x ∈ I := hI'.out h₁ h₂ hx
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hI x hxI
      have hcx : ContinuousAt (fun σ : ℝ => (lindelofMu f σ).toReal) x :=
        hcont.continuousAt (hI.mem_nhds hxI)
      obtain ⟨δ, hδ, hδx⟩ := Metric.continuousAt_iff.mp hcx (ε / 4) (by linarith)
      have hρpos : 0 < min (r / 2) (δ / 2) := lt_min (by linarith) (by linarith)
      have hρr : min (r / 2) (δ / 2) < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hρδ : min (r / 2) (δ / 2) < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      set ρ := min (r / 2) (δ / 2) with hρ
      have hsub : ∀ y : ℝ, x - ρ ≤ y → y ≤ x + ρ →
          y ∈ I ∧ |(lindelofMu f y).toReal - (lindelofMu f x).toReal| < ε / 4 := by
        intro y hy1 hy2
        have hd : |y - x| ≤ ρ := abs_le.mpr ⟨by linarith, by linarith⟩
        refine ⟨hball ?_, ?_⟩
        · rw [Metric.mem_ball, Real.dist_eq]; linarith
        · have := hδx (show dist y x < δ by rw [Real.dist_eq]; linarith)
          rwa [Real.dist_eq] at this
      have ha := hsub (x - ρ) le_rfl (by linarith)
      have hb := hsub (x + ρ) (by linarith) le_rfl
      obtain ⟨M, C, T, hMCT⟩ := hf (x - ρ) (x + ρ) ha.1 hb.1 (by linarith)
      obtain ⟨k₁, hk₁, hk₁lt⟩ := exists_lt_of_ne_top f (x - ρ) (hfin _ ha.1) (ε / 4) (by linarith)
      obtain ⟨k₂, hk₂, hk₂lt⟩ := exists_lt_of_ne_top f (x + ρ) (hfin _ hb.1) (ε / 4) (by linarith)
      obtain ⟨C', T', hC'⟩ :=
        strip_bound_max f (x - ρ) (x + ρ) (by linarith) M C T hMCT k₁ k₂ hk₁ hk₂
      refine ⟨Set.Icc (x - ρ) (x + ρ),
        mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith)),
        |C'|, max T' 1, fun s hs hT => ?_⟩
      have hsI := hsub s.re hs.1 hs.2
      have hexp : max (k₁ : ℝ) k₂ ≤ (lindelofMu f s.re).toReal + ε := by
        have e1 := abs_lt.mp ha.2
        have e2 := abs_lt.mp hb.2
        have e3 := abs_lt.mp hsI.2
        rw [max_le_iff]
        constructor <;> linarith
      have h1s : 1 ≤ |s.im| := le_trans (le_max_right _ _) hT
      calc ‖f s‖ ≤ C' * |s.im| ^ (max (k₁ : ℝ) k₂) :=
            hC' s hs.1 hs.2 (le_trans (le_max_left _ _) hT)
        _ ≤ |C'| * |s.im| ^ (max (k₁ : ℝ) k₂) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (abs_nonneg _) _)
        _ ≤ |C'| * |s.im| ^ ((lindelofMu f s.re).toReal + ε) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1s hexp) (abs_nonneg _)
  obtain ⟨C, T, h⟩ := key
  exact ⟨C, T, fun s hs1 hs2 hT => h s ⟨hs1, hs2⟩ hT⟩
