-- Prove2me | solution 1 for ClarkScarf.Serial.eq18_eq19
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T02:02:57.34899+00:00
-- url     : https://prove2.me/submissions/dcaae4ce-39d8-4e21-8344-1a5f34169486

import Mathlib
import Definitions.Def_ClarkScarf_Serial_Model

open MeasureTheory Set


namespace ClarkScarf.Serial

namespace CSX

variable (M : Model)

lemma phi_int : IntegrableOn M.φ (Ioi (0:ℝ)) := by
  by_contra h
  have := M.φ_total
  rw [integral_undef h] at this
  norm_num at this

noncomputable def K (g : ℝ → ℝ) (u : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), g (u - t) * M.φ t

def Good (g : ℝ → ℝ) : Prop :=
  ConvexOn ℝ univ g ∧ ∃ A B : ℝ, 0 ≤ B ∧ ∀ x, |g x| ≤ A + B * |x|

lemma good_cont {g : ℝ → ℝ} (hg : Good g) : Continuous g := by
  have := hg.1.continuousOn isOpen_univ
  exact continuousOn_univ.mp this

lemma K_int {g : ℝ → ℝ} (hg : Good g) (u : ℝ) :
    Integrable (fun t => g (u - t) * M.φ t) (volume.restrict (Ioi (0:ℝ))) := by
  obtain ⟨A, B, hB, hb⟩ := hg.2
  have h1 := phi_int M
  have h2 := M.φ_mean
  refine Integrable.mono' ((h1.const_mul (A + B * |u|)).add (h2.const_mul B)) ?_ ?_
  · exact ((good_cont hg).comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
      h1.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : (0:ℝ) < t := ht
    have hp := M.φ_nonneg t
    have := hb (u - t)
    have hab : |u - t| ≤ |u| + t := by
      have := abs_sub u t; rw [abs_of_pos ht'] at this; exact this
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
    have : |g (u - t)| ≤ A + B * |u| + B * t := by nlinarith
    simp only [Pi.add_apply]
    nlinarith

lemma K_convex {g : ℝ → ℝ} (hg : Good g) : ConvexOn ℝ univ (K M g) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [K, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
  · refine setIntegral_mono_on ?_ ?_ measurableSet_Ioi ?_
    · exact K_int M hg _
    · exact ((K_int M hg x).const_mul a).add ((K_int M hg y).const_mul b)
    · intro t _
      have hp := M.φ_nonneg t
      have := hg.1.2 (mem_univ (x - t)) (mem_univ (y - t)) ha hb hab
      simp only [smul_eq_mul] at this
      have e : a * x + b * y - t = a * (x - t) + b * (y - t) := by
        have : t = (a + b) * t := by rw [hab]; ring
        linarith [this]
      rw [e]
      nlinarith
  · exact (K_int M hg x).const_mul a
  · exact (K_int M hg y).const_mul b

lemma K_growth {g : ℝ → ℝ} (hg : Good g) :
    ∃ A B : ℝ, 0 ≤ B ∧ ∀ x, |K M g x| ≤ A + B * |x| := by
  obtain ⟨A, B, hB, hb⟩ := hg.2
  set m := ∫ t in Ioi (0:ℝ), t * M.φ t
  refine ⟨A + B * m, B, hB, fun u => ?_⟩
  have h1 := phi_int M
  have h2 := M.φ_mean
  calc |K M g u| = ‖∫ t in Ioi (0:ℝ), g (u - t) * M.φ t‖ := rfl
    _ ≤ ∫ t in Ioi (0:ℝ), ((A + B * |u|) * M.φ t + B * (t * M.φ t)) := by
        refine norm_integral_le_of_norm_le ((h1.const_mul _).add (h2.const_mul B)) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht' : (0:ℝ) < t := ht
        have hp := M.φ_nonneg t
        have := hb (u - t)
        have hab : |u - t| ≤ |u| + t := by
          have := abs_sub u t; rw [abs_of_pos ht'] at this; exact this
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
        have : |g (u - t)| ≤ A + B * |u| + B * t := by nlinarith
        nlinarith
    _ = A + B * m + B * |u| := by
        rw [integral_add (h1.const_mul _) (h2.const_mul B), integral_const_mul, integral_const_mul,
          M.φ_total]
        ring

lemma K_good {g : ℝ → ℝ} (hg : Good g) : Good (K M g) := ⟨K_convex M hg, K_growth M hg⟩

lemma K_nonneg {g : ℝ → ℝ} (hg : ∀ x, 0 ≤ g x) (u : ℝ) : 0 ≤ K M g u :=
  setIntegral_nonneg measurableSet_Ioi (fun t _ => mul_nonneg (hg _) (M.φ_nonneg t))

lemma good_add {f g : ℝ → ℝ} (hf : Good f) (hg : Good g) : Good (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  obtain ⟨A, B, hB, hb⟩ := hf.2
  obtain ⟨A', B', hB', hb'⟩ := hg.2
  refine ⟨A + A', B + B', by linarith, fun x => ?_⟩
  have := abs_add_le (f x) (g x)
  have := hb x; have := hb' x
  nlinarith

lemma good_smul {f : ℝ → ℝ} (hf : Good f) {c : ℝ} (hc : 0 ≤ c) : Good (fun x => c * f x) := by
  refine ⟨hf.1.smul hc, ?_⟩
  obtain ⟨A, B, hB, hb⟩ := hf.2
  refine ⟨c * A, c * B, mul_nonneg hc hB, fun x => ?_⟩
  rw [abs_mul, abs_of_nonneg hc]
  have := hb x
  nlinarith

lemma good_add_lin {f : ℝ → ℝ} (hf : Good f) (c d : ℝ) : Good (fun x => c * x + d + f x) := by
  refine good_add ⟨?_, ?_⟩ hf
  · refine ⟨convex_univ, fun x _ y _ a b _ _ hab => le_of_eq ?_⟩
    simp only [smul_eq_mul]
    linear_combination (-d) * hab
  · refine ⟨|d|, |c|, abs_nonneg _, fun x => ?_⟩
    calc |c * x + d| ≤ |c * x| + |d| := abs_add_le _ _
      _ = |d| + |c| * |x| := by rw [abs_mul]; ring


lemma good_maxpos : Good (fun x : ℝ => max x 0) := by
  refine ⟨⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩, 0, 1, zero_le_one, fun x => ?_⟩
  · simp only [smul_eq_mul]
    apply max_le
    · nlinarith [le_max_left x 0, le_max_left y 0]
    · nlinarith [le_max_right x 0, le_max_right y 0]
  · rw [abs_le]
    constructor
    · nlinarith [le_max_right x 0, abs_nonneg x]
    · have := max_le (le_abs_self x) (abs_nonneg x); linarith

lemma good_maxneg : Good (fun x : ℝ => max (-x) 0) := by
  refine ⟨⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩, 0, 1, zero_le_one, fun x => ?_⟩
  · simp only [smul_eq_mul]
    apply max_le
    · nlinarith [le_max_left (-x) 0, le_max_left (-y) 0]
    · nlinarith [le_max_right (-x) 0, le_max_right (-y) 0]
  · rw [abs_le]
    constructor
    · nlinarith [le_max_right (-x) 0, abs_nonneg x]
    · have := max_le (neg_le_abs x) (abs_nonneg x); linarith

lemma L_eq (x : ℝ) : M.L x = M.h * max x 0 + M.p * K M (fun s => max (-s) 0) x := by
  unfold Model.L K
  split_ifs with hx
  · rw [max_eq_left hx.le]
    congr 2
    symm
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (Ioi_subset_Ioi hx.le)]
    · refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      have ht' : x < t := ht
      beta_reduce
      rw [max_eq_left (by linarith)]; ring
    · intro t ht
      have ht' : t ≤ x := not_lt.mp ht.2
      beta_reduce
      rw [max_eq_right (by linarith)]; ring
  · rw [max_eq_right (not_lt.mp hx)]
    simp only [mul_zero, zero_add]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : 0 < t := ht
    beta_reduce
    rw [max_eq_left (by linarith)]; ring

lemma L_good : Good M.L := by
  have : M.L = fun x => M.h * max x 0 + M.p * K M (fun s => max (-s) 0) x := funext (L_eq M)
  rw [this]
  exact good_add (good_smul good_maxpos M.h_nonneg) (good_smul (K_good M good_maxneg) M.p_nonneg)

lemma L_nonneg (x : ℝ) : 0 ≤ M.L x := by
  rw [L_eq]
  exact add_nonneg (mul_nonneg M.h_nonneg (le_max_right _ _))
    (mul_nonneg M.p_nonneg (K_nonneg M (fun _ => le_max_right _ _) _))

lemma KK_eq (y : ℝ) : (∫ t₁ in Ioi (0 : ℝ), ∫ t₂ in Ioi (0 : ℝ),
      M.L (y - t₁ - t₂) * M.φ t₁ * M.φ t₂) = K M (K M M.L) y := by
  simp only [K]
  congr 1; funext t₁
  rw [← integral_mul_const]
  congr 1; funext t₂
  ring

theorem L_one_period_convex_core :
    ConvexOn ℝ univ (fun y : ℝ => M.α * ∫ t₁ in Ioi (0 : ℝ), ∫ t₂ in Ioi (0 : ℝ),
      M.L (y - t₁ - t₂) * M.φ t₁ * M.φ t₂) := by
  have : (fun y : ℝ => M.α * ∫ t₁ in Ioi (0 : ℝ), ∫ t₂ in Ioi (0 : ℝ),
      M.L (y - t₁ - t₂) * M.φ t₁ * M.φ t₂) = fun y => M.α * K M (K M M.L) y := by
    funext y; rw [KK_eq]
  rw [this]
  exact (good_smul (K_good M (K_good M (L_good M))) M.α_nonneg).1

lemma inf_good (J : ℝ → ℝ) (hJ : Good J) (hJ0 : ∀ y, 0 ≤ J y) (c : ℝ) (hc : 0 ≤ c) :
    Good (fun u => ⨅ y : {y : ℝ // u ≤ y}, (c * ((y:ℝ) - u) + J y)) ∧
    ∀ u, 0 ≤ ⨅ y : {y : ℝ // u ≤ y}, (c * ((y:ℝ) - u) + J y) := by
  have bdd : ∀ u : ℝ, BddBelow (range fun y : {y : ℝ // u ≤ y} => c * ((y:ℝ) - u) + J y) :=
    fun u => ⟨0, by rintro _ ⟨y, rfl⟩; exact add_nonneg (mul_nonneg hc (sub_nonneg.2 y.2)) (hJ0 y)⟩
  have nn : ∀ u, 0 ≤ ⨅ y : {y : ℝ // u ≤ y}, (c * ((y:ℝ) - u) + J y) := by
    intro u
    have : Nonempty {y : ℝ // u ≤ y} := ⟨⟨u, le_rfl⟩⟩
    exact le_ciInf fun y => add_nonneg (mul_nonneg hc (sub_nonneg.2 y.2)) (hJ0 y)
  refine ⟨⟨⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩, ?_⟩, nn⟩
  · simp only [smul_eq_mul]
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    obtain ⟨y1, hy1⟩ := exists_lt_of_ciInf_lt
      (lt_add_of_pos_right (⨅ y : {y : ℝ // x ≤ y}, (c * ((y:ℝ) - x) + J y)) hε)
    obtain ⟨y2, hy2⟩ := exists_lt_of_ciInf_lt
      (lt_add_of_pos_right (⨅ y' : {y' : ℝ // y ≤ y'}, (c * ((y':ℝ) - y) + J y')) hε)
    have hy1' := y1.2; have hy2' := y2.2
    have hmem : a * x + b * y ≤ a * (y1:ℝ) + b * (y2:ℝ) := by nlinarith
    have h1 := ciInf_le (bdd (a * x + b * y)) ⟨a * (y1:ℝ) + b * (y2:ℝ), hmem⟩
    have h2 := hJ.1.2 (mem_univ (y1:ℝ)) (mem_univ (y2:ℝ)) ha hb hab
    simp only [smul_eq_mul] at h2 h1
    have h3 := mul_le_mul_of_nonneg_left hy1.le ha
    have h4 := mul_le_mul_of_nonneg_left hy2.le hb
    have e : ε = a * ε + b * ε := by rw [← add_mul, hab, one_mul]
    nlinarith
  · obtain ⟨A, B, hB, hb⟩ := hJ.2
    refine ⟨A, B, hB, fun u => ?_⟩
    rw [abs_of_nonneg (nn u)]
    have := ciInf_le (bdd u) ⟨u, le_rfl⟩
    simp only [sub_self, mul_zero, zero_add] at this
    have := hb u
    have := le_abs_self (J u)
    linarith

lemma fLag_eq (n : ℕ) (u : ℝ) : M.fLag (n+3) u = ⨅ y : {y : ℝ // u ≤ y},
    (M.c1 * ((y:ℝ) - u) + (M.α^2 * K M (K M M.L) y + M.α * K M (M.fLag (n+2)) y)) := by
  rw [Model.fLag]
  beta_reduce
  congr 1; funext y
  rw [KK_eq]; simp only [K]; ring

lemma good_zero : Good (fun _ : ℝ => (0:ℝ)) :=
  ⟨convexOn_const 0 convex_univ, 0, 0, le_rfl, fun x => by simp⟩

theorem fLag_good : ∀ n, Good (M.fLag n) ∧ ∀ u, 0 ≤ M.fLag n u
  | 0 => ⟨good_zero, fun _ => le_rfl⟩
  | 1 => ⟨good_zero, fun _ => le_rfl⟩
  | 2 => ⟨good_zero, fun _ => le_rfl⟩
  | n + 3 => by
    have ih := fLag_good (n + 2)
    have hJ : Good (fun y => M.α^2 * K M (K M M.L) y + M.α * K M (M.fLag (n+2)) y) :=
      good_add (good_smul (K_good M (K_good M (L_good M))) (sq_nonneg _))
        (good_smul (K_good M ih.1) M.α_nonneg)
    have hJ0 : ∀ y, 0 ≤ M.α^2 * K M (K M M.L) y + M.α * K M (M.fLag (n+2)) y := fun y =>
      add_nonneg (mul_nonneg (sq_nonneg _) (K_nonneg M (K_nonneg M (L_nonneg M)) _))
        (mul_nonneg M.α_nonneg (K_nonneg M ih.2 _))
    have := inf_good _ hJ hJ0 M.c1 M.c1_nonneg
    have e : M.fLag (n+3) = fun u => ⨅ y : {y : ℝ // u ≤ y},
      (M.c1 * ((y:ℝ) - u) + (M.α^2 * K M (K M M.L) y + M.α * K M (M.fLag (n+2)) y)) :=
      funext (fLag_eq M n)
    rw [e]
    exact this

theorem fLag_convex_core (n : ℕ) : ConvexOn ℝ univ (M.fLag n) := (fLag_good M n).1.1


lemma iInf_ge_eq (u y0 : ℝ) (f : ℝ → ℝ) (hy0 : u ≤ y0) (h : ∀ y, u ≤ y → f y0 ≤ f y) :
    ⨅ y : {y : ℝ // u ≤ y}, f y = f y0 := by
  have : Nonempty {y : ℝ // u ≤ y} := ⟨⟨u, le_rfl⟩⟩
  refine le_antisymm ?_ (le_ciInf fun y => h y y.2)
  have hb : BddBelow (range fun y : {y : ℝ // u ≤ y} => f y) :=
    ⟨f y0, by rintro _ ⟨⟨y, hy⟩, rfl⟩; exact h y hy⟩
  exact ciInf_le hb ⟨y0, hy0⟩

lemma iInf_const_add {ι : Type*} [Nonempty ι] (C : ℝ) (h : ι → ℝ) (h0 : ∀ i, 0 ≤ h i) :
    ⨅ i, (C + h i) = C + ⨅ i, h i := by
  have b1 : BddBelow (range h) := ⟨0, by rintro _ ⟨i, rfl⟩; exact h0 i⟩
  have b2 : BddBelow (range fun i => C + h i) :=
    ⟨C, by rintro _ ⟨i, rfl⟩; have := h0 i; simp only; linarith⟩
  apply le_antisymm
  · have : (⨅ i, (C + h i)) - C ≤ ⨅ i, h i :=
      le_ciInf fun i => by have := ciInf_le b2 i; linarith
    linarith
  · exact le_ciInf fun i => by have := ciInf_le b1 i; linarith

lemma iso1 (a b : ℝ) : M.isoCost 1 a b = M.L a := by
  rw [show (1:ℕ) = 0 + 1 from rfl, Model.isoCost_succ]
  have e : ∀ y, M.isoObj 0 a b y = M.c1 * (y - a - b) + M.L a := by
    intro y; simp [Model.isoObj, Model.isoCost]
  simp only [e]
  rw [iInf_ge_eq (a + b) (a + b) (fun y => M.c1 * (y - a - b) + M.L a) le_rfl]
  · ring
  · intro y hy
    have := mul_nonneg M.c1_nonneg (show 0 ≤ y - a - b by linarith)
    nlinarith

def Dec (m : ℕ) : Prop := ∀ x₁ w₁ : ℝ,
  M.isoCost (m + 2) x₁ w₁ = M.L x₁ + M.α * K M M.L (x₁ + w₁) + M.fLag (m + 2) (x₁ + w₁)

lemma isoObj_eq (m : ℕ) (hD : Dec M m) (x₁ w₁ y : ℝ) :
    M.isoObj (m + 2) x₁ w₁ y = M.L x₁ + M.α * K M M.L (x₁ + w₁) +
      (M.c1 * (y - (x₁ + w₁)) + (M.α^2 * K M (K M M.L) y + M.α * K M (M.fLag (m+2)) y)) := by
  have hpt : ∀ t, M.isoCost (m+2) (x₁ + w₁ - t) (y - x₁ - w₁) * M.φ t =
      M.L (x₁ + w₁ - t) * M.φ t + M.α * (K M M.L (y - t) * M.φ t) +
        M.fLag (m+2) (y - t) * M.φ t := by
    intro t
    rw [hD]
    have e : x₁ + w₁ - t + (y - x₁ - w₁) = y - t := by ring
    rw [e]; ring
  unfold Model.isoObj
  simp only [hpt]
  have i1 := K_int M (L_good M) (x₁ + w₁)
  have i2 := (K_int M (K_good M (L_good M)) y).const_mul M.α
  have i3 := K_int M (fLag_good M (m+2)).1 y
  have i12 : Integrable (fun t => M.L (x₁ + w₁ - t) * M.φ t + M.α * (K M M.L (y - t) * M.φ t))
    (volume.restrict (Ioi (0:ℝ))) := i1.add i2
  rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul]
  simp only [K]
  ring

lemma dec_all : ∀ m, Dec M m
  | 0 => by
    intro x₁ w₁
    rw [show (0 + 2 : ℕ) = 1 + 1 from rfl, Model.isoCost_succ]
    have e : ∀ y, M.isoObj 1 x₁ w₁ y = M.c1 * (y - x₁ - w₁) + (M.L x₁ + M.α * K M M.L (x₁ + w₁)) := by
      intro y; simp only [Model.isoObj, iso1, K]
      have : ∀ t, x₁ + w₁ - t = x₁ + w₁ - t := fun _ => rfl
      ring
    simp only [e]
    rw [iInf_ge_eq (x₁ + w₁) (x₁ + w₁) (fun y => M.c1 * (y - x₁ - w₁) + (M.L x₁ + M.α * K M M.L (x₁ + w₁))) le_rfl]
    · show _ = _ + 0; ring
    · intro y hy
      have := mul_nonneg M.c1_nonneg (show 0 ≤ y - x₁ - w₁ by linarith)
      nlinarith
  | m + 1 => by
    have hD := dec_all m
    intro x₁ w₁
    rw [show m + 1 + 2 = (m + 2) + 1 from rfl, Model.isoCost_succ]
    simp only [isoObj_eq M m hD x₁ w₁]
    have : Nonempty {y : ℝ // x₁ + w₁ ≤ y} := ⟨⟨x₁ + w₁, le_rfl⟩⟩
    rw [iInf_const_add]
    · rw [show m + 1 + 2 = m + 3 from rfl, fLag_eq]
    · intro y
      exact add_nonneg (mul_nonneg M.c1_nonneg (sub_nonneg.2 y.2))
        (add_nonneg (mul_nonneg (sq_nonneg _) (K_nonneg M (K_nonneg M (L_nonneg M)) _))
          (mul_nonneg M.α_nonneg (K_nonneg M (fLag_good M (m+2)).2 _)))

theorem isoCost_decomposition_core (n : ℕ) (hn : 2 ≤ n) (x₁ w₁ : ℝ) :
    M.isoCost n x₁ w₁ =
      M.L x₁ + M.α * (∫ t in Ioi (0 : ℝ), M.L (x₁ + w₁ - t) * M.φ t) + M.fLag n (x₁ + w₁) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact dec_all M m x₁ w₁

theorem lambda_eq25_core (n : ℕ) (hn : 2 ≤ n) (xbar : ℝ)
    (hxbar : M.IsCriticalNumber n xbar) (x₁ w₁ x₂ : ℝ) (hdom : x₁ + w₁ ≤ x₂) (hlt : x₂ < xbar) :
    M.c1 * (x₂ - x₁ - w₁) + M.L x₁ +
        M.α * (∫ t in Ioi (0 : ℝ), M.isoCost n (x₁ + w₁ - t) (x₂ - x₁ - w₁) * M.φ t) -
        M.isoCost (n + 1) x₁ w₁ =
      M.c1 * (x₂ - xbar) +
        M.α ^ 2 * (∫ t in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ),
          (M.L (x₂ - t - y) - M.L (xbar - t - y)) * M.φ t * M.φ y) +
        M.α * ∫ t in Ioi (0 : ℝ), (M.fLag n (x₂ - t) - M.fLag n (xbar - t)) * M.φ t := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hD := dec_all M m
  have h1 : M.isoCost (m + 2 + 1) x₁ w₁ = M.isoObj (m+2) x₁ w₁ xbar := by
    rw [Model.isoCost_succ, iInf_ge_eq (x₁ + w₁) (max (x₁ + w₁) xbar) (M.isoObj (m+2) x₁ w₁)
      (le_max_left _ _) (hxbar x₁ w₁)]
    rw [max_eq_right (by linarith)]
  rw [h1]
  change M.isoObj (m+2) x₁ w₁ x₂ - M.isoObj (m+2) x₁ w₁ xbar = _
  rw [isoObj_eq M m hD, isoObj_eq M m hD]
  have hdbl : (∫ t in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ),
          (M.L (x₂ - t - y) - M.L (xbar - t - y)) * M.φ t * M.φ y) =
      K M (K M M.L) x₂ - K M (K M M.L) xbar := by
    have : ∀ t, (∫ y in Ioi (0 : ℝ), (M.L (x₂ - t - y) - M.L (xbar - t - y)) * M.φ t * M.φ y) =
        K M M.L (x₂ - t) * M.φ t - K M M.L (xbar - t) * M.φ t := by
      intro t
      have : (∫ y in Ioi (0 : ℝ), (M.L (x₂ - t - y) - M.L (xbar - t - y)) * M.φ t * M.φ y) =
          ∫ y in Ioi (0 : ℝ), (M.L (x₂ - t - y) * M.φ y - M.L (xbar - t - y) * M.φ y) * M.φ t := by
        congr 1; funext y; ring
      rw [this, integral_mul_const, integral_sub (K_int M (L_good M) _) (K_int M (L_good M) _),
        sub_mul]
      rfl
    simp only [this]
    rw [integral_sub (K_int M (K_good M (L_good M)) _) (K_int M (K_good M (L_good M)) _)]
    rfl
  have hf : (∫ t in Ioi (0 : ℝ), (M.fLag (m+2) (x₂ - t) - M.fLag (m+2) (xbar - t)) * M.φ t) =
      K M (M.fLag (m+2)) x₂ - K M (M.fLag (m+2)) xbar := by
    simp only [sub_mul]
    rw [integral_sub (K_int M (fLag_good M (m+2)).1 _) (K_int M (fLag_good M (m+2)).1 _)]
    rfl
  rw [hdbl, hf]
  ring


/-! ## Part 3: system cost -/

def Gm (g : ℝ → ℝ) : Prop := Measurable g ∧ ∃ A B : ℝ, 0 ≤ B ∧ ∀ x, |g x| ≤ A + B * |x|

lemma K_int2 {g : ℝ → ℝ} (hg : Gm g) (u : ℝ) :
    Integrable (fun t => g (u - t) * M.φ t) (volume.restrict (Ioi (0:ℝ))) := by
  obtain ⟨A, B, hB, hb⟩ := hg.2
  have h1 := phi_int M
  have h2 := M.φ_mean
  refine Integrable.mono' ((h1.const_mul (A + B * |u|)).add (h2.const_mul B)) ?_ ?_
  · exact (hg.1.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
      h1.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : (0:ℝ) < t := ht
    have hp := M.φ_nonneg t
    have := hb (u - t)
    have hab : |u - t| ≤ |u| + t := by
      have := abs_sub u t; rw [abs_of_pos ht'] at this; exact this
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
    have : |g (u - t)| ≤ A + B * |u| + B * t := by nlinarith
    simp only [Pi.add_apply]
    nlinarith

lemma K_growth2 {g : ℝ → ℝ} (hg : Gm g) :
    ∃ A B : ℝ, 0 ≤ B ∧ ∀ x, |K M g x| ≤ A + B * |x| := by
  obtain ⟨A, B, hB, hb⟩ := hg.2
  set m := ∫ t in Ioi (0:ℝ), t * M.φ t
  refine ⟨A + B * m, B, hB, fun u => ?_⟩
  have h1 := phi_int M
  have h2 := M.φ_mean
  calc |K M g u| = ‖∫ t in Ioi (0:ℝ), g (u - t) * M.φ t‖ := rfl
    _ ≤ ∫ t in Ioi (0:ℝ), ((A + B * |u|) * M.φ t + B * (t * M.φ t)) := by
        refine norm_integral_le_of_norm_le ((h1.const_mul _).add (h2.const_mul B)) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht' : (0:ℝ) < t := ht
        have hp := M.φ_nonneg t
        have := hb (u - t)
        have hab : |u - t| ≤ |u| + t := by
          have := abs_sub u t; rw [abs_of_pos ht'] at this; exact this
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
        have : |g (u - t)| ≤ A + B * |u| + B * t := by nlinarith
        nlinarith
    _ = A + B * m + B * |u| := by
        rw [integral_add (h1.const_mul _) (h2.const_mul B), integral_const_mul, integral_const_mul,
          M.φ_total]
        ring

lemma K_meas {g : ℝ → ℝ} (hg : Measurable g) : Measurable (K M g) := by
  have hφ := (phi_int M).aestronglyMeasurable
  have e : K M g = fun x => ∫ t, g (x - t) * hφ.mk M.φ t ∂(volume.restrict (Ioi (0:ℝ))) := by
    funext x
    refine integral_congr_ae ?_
    filter_upwards [hφ.ae_eq_mk] with t ht
    rw [ht]
  rw [e]
  have : StronglyMeasurable (fun p : ℝ × ℝ => g (p.1 - p.2) * hφ.mk M.φ p.2) :=
    ((hg.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable).mul
      (hφ.stronglyMeasurable_mk.comp_measurable measurable_snd)
  exact (this.integral_prod_right' (ν := volume.restrict (Ioi (0:ℝ)))).measurable

lemma orderCost_nonneg (z : ℝ) : 0 ≤ M.orderCost z := by
  unfold Model.orderCost
  split_ifs with h
  · exact add_nonneg M.K_nonneg (mul_nonneg M.c_nonneg h.le)
  · exact le_rfl

lemma orderCost_zero : M.orderCost 0 = 0 := by simp [Model.orderCost]

noncomputable def Psx : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => fun _ => 0
  | m + 2 => fun y => M.α^2 * K M (K M M.L) y + M.α * K M (M.fLag (m+2)) y

noncomputable def Ps (n : ℕ) (y : ℝ) : ℝ := M.c1 * y + Psx M n y

lemma Psx_good : ∀ n, Good (Psx M n) ∧ ∀ y, 0 ≤ Psx M n y
  | 0 => ⟨good_zero, fun _ => le_rfl⟩
  | 1 => ⟨good_zero, fun _ => le_rfl⟩
  | m + 2 => ⟨good_add (good_smul (K_good M (K_good M (L_good M))) (sq_nonneg _))
      (good_smul (K_good M (fLag_good M (m+2)).1) M.α_nonneg),
      fun y => add_nonneg (mul_nonneg (sq_nonneg _) (K_nonneg M (K_nonneg M (L_nonneg M)) _))
        (mul_nonneg M.α_nonneg (K_nonneg M (fLag_good M (m+2)).2 _))⟩

lemma Ps_good (n : ℕ) : Good (Ps M n) := by
  have : Ps M n = fun x => M.c1 * x + 0 + Psx M n x := by funext x; simp [Ps]
  rw [this]; exact good_add_lin (Psx_good M n).1 _ _

lemma Ps_ge (n : ℕ) (y : ℝ) : M.c1 * y ≤ Ps M n y := by
  have := (Psx_good M n).2 y; unfold Ps; linarith

lemma shape (n : ℕ) (x₁ w₁ : ℝ) : ∃ P : ℝ, ∀ y, M.isoObj n x₁ w₁ y = P + Ps M n y := by
  match n with
  | 0 => exact ⟨M.L x₁ - M.c1 * (x₁ + w₁), fun y => by
      simp [Model.isoObj, Model.isoCost, Ps, Psx]; ring⟩
  | 1 => exact ⟨M.L x₁ + M.α * K M M.L (x₁ + w₁) - M.c1 * (x₁ + w₁), fun y => by
      simp only [Model.isoObj, iso1, Ps, Psx, K]; ring⟩
  | m + 2 => exact ⟨M.L x₁ + M.α * K M M.L (x₁ + w₁) - M.c1 * (x₁ + w₁), fun y => by
      rw [isoObj_eq M m (dec_all M m)]; simp only [Ps, Psx]; ring⟩

lemma iso_int (n : ℕ) (a b : ℝ) :
    Integrable (fun t => M.isoCost n (a - t) b * M.φ t) (volume.restrict (Ioi (0:ℝ))) := by
  match n with
  | 0 => simp [Model.isoCost]
  | 1 => simp only [iso1]; exact K_int M (L_good M) a
  | m + 2 =>
    have : (fun t => M.isoCost (m+2) (a - t) b * M.φ t) = fun t =>
        (M.L (a - t) * M.φ t + M.α * (K M M.L (a + b - t) * M.φ t)) +
          M.fLag (m+2) (a + b - t) * M.φ t := by
      funext t; rw [dec_all M m]; rw [show a - t + b = a + b - t by ring]; ring
    rw [this]
    exact ((K_int M (L_good M) a).add ((K_int M (K_good M (L_good M)) (a+b)).const_mul _)).add
      (K_int M (fLag_good M (m+2)).1 (a+b))

lemma iInf_add_bdd {ι : Type*} [Nonempty ι] (C : ℝ) (h : ι → ℝ) (hb : BddBelow (range h)) :
    ⨅ i, (C + h i) = C + ⨅ i, h i := by
  obtain ⟨m, hm⟩ := hb
  have hm' : ∀ i, m ≤ h i := fun i => hm (mem_range_self i)
  have b2 : BddBelow (range fun i => C + h i) :=
    ⟨C + m, by rintro _ ⟨i, rfl⟩; have := hm' i; linarith⟩
  have b1 : BddBelow (range h) := ⟨m, by rintro _ ⟨i, rfl⟩; exact hm' i⟩
  apply le_antisymm
  · have : (⨅ i, (C + h i)) - C ≤ ⨅ i, h i :=
      le_ciInf fun i => by have := ciInf_le b2 i; linarith
    linarith
  · exact le_ciInf fun i => by have := ciInf_le b1 i; linarith

lemma iInf_split (u x₂ : ℝ) (hux : u ≤ x₂) (A B : ℝ → ℝ) (a b : ℝ) (hA : ∀ y, u ≤ y → a ≤ A y)
    (hB : ∀ z, 0 ≤ z → b ≤ B z) :
    ⨅ q : {q : ℝ × ℝ // u ≤ q.1 ∧ q.1 ≤ x₂ ∧ 0 ≤ q.2}, (A (q : ℝ × ℝ).1 + B (q : ℝ × ℝ).2) =
      (⨅ y : {y : ℝ // u ≤ y ∧ y ≤ x₂}, A y) + ⨅ z : {z : ℝ // 0 ≤ z}, B z := by
  have n1 : Nonempty {y : ℝ // u ≤ y ∧ y ≤ x₂} := ⟨⟨u, le_rfl, hux⟩⟩
  have n2 : Nonempty {z : ℝ // 0 ≤ z} := ⟨⟨0, le_rfl⟩⟩
  have n3 : Nonempty {q : ℝ × ℝ // u ≤ q.1 ∧ q.1 ≤ x₂ ∧ 0 ≤ q.2} :=
    ⟨⟨(u, 0), le_rfl, hux, le_rfl⟩⟩
  have bA : BddBelow (range fun y : {y : ℝ // u ≤ y ∧ y ≤ x₂} => A y) :=
    ⟨a, by rintro _ ⟨y, rfl⟩; exact hA (y:ℝ) y.2.1⟩
  have bB : BddBelow (range fun z : {z : ℝ // 0 ≤ z} => B z) :=
    ⟨b, by rintro _ ⟨z, rfl⟩; exact hB (z:ℝ) z.2⟩
  have bQ : BddBelow (range fun q : {q : ℝ × ℝ // u ≤ q.1 ∧ q.1 ≤ x₂ ∧ 0 ≤ q.2} =>
      A (q : ℝ × ℝ).1 + B (q : ℝ × ℝ).2) :=
    ⟨a + b, by rintro _ ⟨q, rfl⟩; exact add_le_add (hA _ q.2.1) (hB _ q.2.2.2)⟩
  apply le_antisymm
  · have h1 : ∀ y : {y : ℝ // u ≤ y ∧ y ≤ x₂}, ∀ z : {z : ℝ // 0 ≤ z},
        (⨅ q : {q : ℝ × ℝ // u ≤ q.1 ∧ q.1 ≤ x₂ ∧ 0 ≤ q.2}, (A (q : ℝ × ℝ).1 + B (q : ℝ × ℝ).2))
          ≤ A y + B z :=
      fun y z => ciInf_le bQ ⟨((y : ℝ), (z : ℝ)), y.2.1, y.2.2, z.2⟩
    have h2 : ∀ z : {z : ℝ // 0 ≤ z},
        (⨅ q : {q : ℝ × ℝ // u ≤ q.1 ∧ q.1 ≤ x₂ ∧ 0 ≤ q.2}, (A (q : ℝ × ℝ).1 + B (q : ℝ × ℝ).2))
          - B z ≤ ⨅ y : {y : ℝ // u ≤ y ∧ y ≤ x₂}, A y :=
      fun z => le_ciInf fun y => by have := h1 y z; linarith
    have h3 : (⨅ q : {q : ℝ × ℝ // u ≤ q.1 ∧ q.1 ≤ x₂ ∧ 0 ≤ q.2},
        (A (q : ℝ × ℝ).1 + B (q : ℝ × ℝ).2)) - (⨅ y : {y : ℝ // u ≤ y ∧ y ≤ x₂}, A y) ≤
          ⨅ z : {z : ℝ // 0 ≤ z}, B z :=
      le_ciInf fun z => by have := h2 z; linarith
    linarith
  · exact le_ciInf fun q => add_le_add (ciInf_le bA ⟨_, q.2.1, q.2.2.1⟩) (ciInf_le bB ⟨_, q.2.2.2⟩)

lemma iInf_Icc_eq (u x₂ y0 : ℝ) (f : ℝ → ℝ) (hy0 : u ≤ y0 ∧ y0 ≤ x₂)
    (h : ∀ y, u ≤ y → y ≤ x₂ → f y0 ≤ f y) :
    ⨅ y : {y : ℝ // u ≤ y ∧ y ≤ x₂}, f y = f y0 := by
  have : Nonempty {y : ℝ // u ≤ y ∧ y ≤ x₂} := ⟨⟨y0, hy0⟩⟩
  refine le_antisymm ?_ (le_ciInf fun y => h y y.2.1 y.2.2)
  have hb : BddBelow (range fun y : {y : ℝ // u ≤ y ∧ y ≤ x₂} => f y) :=
    ⟨f y0, by rintro _ ⟨⟨y, hy⟩, rfl⟩; exact h y hy.1 hy.2⟩
  exact ciInf_le hb ⟨y0, hy0⟩

lemma sysObj_split (n : ℕ) (G : ℝ → ℝ) (hGm : Gm G)
    (hG : ∀ x₁ w₁ x₂ : ℝ, x₁ + w₁ ≤ x₂ → M.sysCost n x₁ w₁ x₂ = M.isoCost n x₁ w₁ + G x₂)
    (x₁ w₁ x₂ y z : ℝ) (hy : y ≤ x₂) (hz : 0 ≤ z) :
    M.sysObj n x₁ w₁ x₂ y z = M.isoObj n x₁ w₁ y +
      (M.orderCost z + M.Lt x₂ + M.α * ∫ t in Ioi (0:ℝ), G (x₂ + z - t) * M.φ t) := by
  have hpt : ∀ t, M.sysCost n (x₁ + w₁ - t) (y - x₁ - w₁) (x₂ + z - t) * M.φ t =
      M.isoCost n (x₁ + w₁ - t) (y - x₁ - w₁) * M.φ t + G (x₂ + z - t) * M.φ t := by
    intro t; rw [hG _ _ _ (by linarith)]; ring
  unfold Model.sysObj Model.isoObj
  simp only [hpt]
  rw [integral_add (iso_int M n _ _) (K_int2 M hGm (x₂ + z))]
  ring

lemma step (n : ℕ) (G : ℝ → ℝ) (hGm : Gm G) (hG0 : ∀ x, 0 ≤ G x)
    (hG : ∀ x₁ w₁ x₂ : ℝ, x₁ + w₁ ≤ x₂ → M.sysCost n x₁ w₁ x₂ = M.isoCost n x₁ w₁ + G x₂)
    (x₁ w₁ x₂ : ℝ) (hdom : x₁ + w₁ ≤ x₂) :
    M.sysCost (n+1) x₁ w₁ x₂ = (⨅ y : {y : ℝ // x₁ + w₁ ≤ y ∧ y ≤ x₂}, M.isoObj n x₁ w₁ y) +
      ⨅ z : {z : ℝ // 0 ≤ z}, (M.orderCost (z:ℝ) + M.Lt x₂ +
        M.α * ∫ t in Ioi (0:ℝ), G (x₂ + (z:ℝ) - t) * M.φ t) := by
  rw [Model.sysCost_succ]
  have : (fun q : {q : ℝ × ℝ // x₁ + w₁ ≤ q.1 ∧ q.1 ≤ x₂ ∧ 0 ≤ q.2} =>
      M.sysObj n x₁ w₁ x₂ (q : ℝ × ℝ).1 (q : ℝ × ℝ).2) =
      fun q : {q : ℝ × ℝ // x₁ + w₁ ≤ q.1 ∧ q.1 ≤ x₂ ∧ 0 ≤ q.2} => M.isoObj n x₁ w₁ (q : ℝ × ℝ).1 +
      (fun z => M.orderCost z + M.Lt x₂ + M.α * ∫ t in Ioi (0:ℝ), G (x₂ + z - t) * M.φ t)
        (q : ℝ × ℝ).2 := by
    funext q; exact sysObj_split M n G hGm hG _ _ _ _ _ q.2.2.1 q.2.2.2
  rw [show (⨅ q : {q : ℝ × ℝ // x₁ + w₁ ≤ q.1 ∧ q.1 ≤ x₂ ∧ 0 ≤ q.2},
      M.sysObj n x₁ w₁ x₂ (q : ℝ × ℝ).1 (q : ℝ × ℝ).2) = _ from congrArg iInf this]
  obtain ⟨P, hP⟩ := shape M n x₁ w₁
  refine iInf_split (x₁ + w₁) x₂ hdom (M.isoObj n x₁ w₁)
    (fun z => M.orderCost z + M.Lt x₂ + M.α * ∫ t in Ioi (0:ℝ), G (x₂ + z - t) * M.φ t)
    (P + M.c1 * (x₁ + w₁)) 0 ?_ ?_
  · intro y hy; rw [hP]; have := Ps_ge M n y
    have := mul_le_mul_of_nonneg_left hy M.c1_nonneg; linarith
  · intro z hz
    exact add_nonneg (add_nonneg (orderCost_nonneg M z) (M.Lt_nonneg x₂))
      (mul_nonneg M.α_nonneg (K_nonneg M hG0 _))

noncomputable def D (n : ℕ) (x : ℝ) : ℝ := Ps M n x - ⨅ y : {y : ℝ // x ≤ y}, Ps M n y

lemma Ps_bdd (n : ℕ) (u : ℝ) : BddBelow (range fun y : {y : ℝ // u ≤ y} => Ps M n y) :=
  ⟨M.c1 * u, by
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    have := Ps_ge M n y; have := mul_le_mul_of_nonneg_left hy M.c1_nonneg; linarith⟩

lemma Ps_bdd' (n : ℕ) (u x₂ : ℝ) :
    BddBelow (range fun y : {y : ℝ // u ≤ y ∧ y ≤ x₂} => Ps M n y) :=
  ⟨M.c1 * u, by
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    have := Ps_ge M n y; have := mul_le_mul_of_nonneg_left hy.1 M.c1_nonneg; linarith⟩

lemma D_props (n : ℕ) : Gm (D M n) ∧ ∀ x, 0 ≤ D M n x := by
  have hmono : Monotone (fun x => ⨅ y : {y : ℝ // x ≤ y}, Ps M n y) := by
    intro x x' hxx'
    have : Nonempty {y : ℝ // x' ≤ y} := ⟨⟨x', le_rfl⟩⟩
    exact le_ciInf fun y => ciInf_le (Ps_bdd M n x) ⟨y, hxx'.trans y.2⟩
  have hc : Continuous (Ps M n) := good_cont (Ps_good M n)
  have nn : ∀ x, 0 ≤ D M n x := fun x => by
    unfold D; have := ciInf_le (Ps_bdd M n x) ⟨x, le_rfl⟩; linarith
  refine ⟨⟨hc.measurable.sub hmono.measurable, ?_⟩, nn⟩
  obtain ⟨A, B, hB, hb⟩ := (Ps_good M n).2
  refine ⟨A, B + M.c1, by linarith [M.c1_nonneg], fun x => ?_⟩
  rw [abs_of_nonneg (nn x)]
  have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_rfl⟩⟩
  have h1 : M.c1 * x ≤ ⨅ y : {y : ℝ // x ≤ y}, Ps M n y := le_ciInf fun y => by
    have := Ps_ge M n y; have := mul_le_mul_of_nonneg_left y.2 M.c1_nonneg; linarith
  unfold D
  have := hb x; have := le_abs_self (Ps M n x)
  have := mul_le_mul_of_nonneg_left (neg_abs_le x) M.c1_nonneg
  nlinarith

lemma cvx_aux {Ψ : ℝ → ℝ} (hΨ : ConvexOn ℝ univ Ψ) {y x y' : ℝ} (h1 : y ≤ x) (h2 : x < y')
    (h3 : Ψ y' ≤ Ψ x) : Ψ x ≤ Ψ y := by
  rcases eq_or_lt_of_le h1 with h | h
  · rw [h]
  · have hd : 0 < y' - y := by linarith
    set θ := (y' - x) / (y' - y) with hθ
    have hθ0 : 0 < θ := div_pos (by linarith) hd
    have hθ1 : θ ≤ 1 := (div_le_one hd).2 (by linarith)
    have hx : θ * y + (1 - θ) * y' = x := by rw [hθ]; field_simp <;> ring
    have := hΨ.2 (mem_univ y) (mem_univ y') hθ0.le (by linarith) (by ring : θ + (1 - θ) = 1)
    simp only [smul_eq_mul] at this
    rw [hx] at this
    have h4 : (1 - θ) * Ψ y' ≤ (1 - θ) * Ψ x := mul_le_mul_of_nonneg_left h3 (by linarith)
    have h5 : θ * Ψ x ≤ θ * Ψ y := by linarith
    exact le_of_mul_le_mul_left h5 hθ0

lemma Q_lem (n : ℕ) (x₁ w₁ x₂ : ℝ) (hdom : x₁ + w₁ ≤ x₂) :
    (⨅ y : {y : ℝ // x₁ + w₁ ≤ y ∧ y ≤ x₂}, M.isoObj n x₁ w₁ y) =
      M.isoCost (n+1) x₁ w₁ + D M n x₂ := by
  obtain ⟨P, hP⟩ := shape M n x₁ w₁
  have ne1 : Nonempty {y : ℝ // x₁ + w₁ ≤ y ∧ y ≤ x₂} := ⟨⟨x₁ + w₁, le_rfl, hdom⟩⟩
  have ne2 : Nonempty {y : ℝ // x₁ + w₁ ≤ y} := ⟨⟨x₁ + w₁, le_rfl⟩⟩
  have ne3 : Nonempty {y : ℝ // x₂ ≤ y} := ⟨⟨x₂, le_rfl⟩⟩
  rw [Model.isoCost_succ]
  simp only [hP]
  rw [iInf_add_bdd _ _ (Ps_bdd' M n (x₁ + w₁) x₂), iInf_add_bdd _ _ (Ps_bdd M n (x₁ + w₁))]
  unfold D
  suffices h : (⨅ y : {y : ℝ // x₁ + w₁ ≤ y ∧ y ≤ x₂}, Ps M n y) =
      (⨅ y : {y : ℝ // x₁ + w₁ ≤ y}, Ps M n y) +
        (Ps M n x₂ - ⨅ y : {y : ℝ // x₂ ≤ y}, Ps M n y) by rw [h]; ring
  have hcv := (Ps_good M n).1
  by_cases hmin : ∀ y, x₂ ≤ y → Ps M n x₂ ≤ Ps M n y
  · rw [iInf_ge_eq x₂ x₂ (Ps M n) le_rfl hmin, sub_self, add_zero]
    apply le_antisymm
    · exact le_ciInf fun y => by
        rcases le_total (y:ℝ) x₂ with h | h
        · exact ciInf_le (Ps_bdd' M n (x₁ + w₁) x₂) ⟨y, y.2, h⟩
        · exact (ciInf_le (Ps_bdd' M n (x₁ + w₁) x₂) ⟨x₂, hdom, le_rfl⟩).trans (hmin y h)
    · exact le_ciInf fun y => ciInf_le (Ps_bdd M n (x₁ + w₁)) ⟨y, y.2.1⟩
  · push_neg at hmin
    obtain ⟨y', hy'1, hy'2⟩ := hmin
    have hlt : x₂ < y' := lt_of_le_of_ne hy'1 (by rintro rfl; exact lt_irrefl _ hy'2)
    have hdec : ∀ y, y ≤ x₂ → Ps M n x₂ ≤ Ps M n y := fun y hy => cvx_aux hcv hy hlt hy'2.le
    have ha : (⨅ y : {y : ℝ // x₁ + w₁ ≤ y ∧ y ≤ x₂}, Ps M n y) = Ps M n x₂ :=
      iInf_Icc_eq _ x₂ x₂ (Ps M n) ⟨hdom, le_rfl⟩ (fun y _ hy => hdec y hy)
    have hc : (⨅ y : {y : ℝ // x₁ + w₁ ≤ y}, Ps M n y) = ⨅ y : {y : ℝ // x₂ ≤ y}, Ps M n y := by
      apply le_antisymm
      · exact le_ciInf fun y => ciInf_le (Ps_bdd M n (x₁ + w₁)) ⟨y, hdom.trans y.2⟩
      · exact le_ciInf fun y => by
          rcases le_total (y:ℝ) x₂ with h | h
          · exact (ciInf_le (Ps_bdd M n x₂) ⟨x₂, le_rfl⟩).trans (hdec y h)
          · exact ciInf_le (Ps_bdd M n x₂) ⟨y, h⟩
    rw [ha, hc]; ring

noncomputable def gen (Λ : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => ⨅ z : {z : ℝ // 0 ≤ z},
      (M.orderCost (z : ℝ) + M.Lt x + Λ n x +
        M.α * ∫ t in Ioi (0 : ℝ), gen Λ n (x + (z : ℝ) - t) * M.φ t)

lemma gen_succ_eq (Λ : ℕ → ℝ → ℝ) (n : ℕ) (hg0 : ∀ x, 0 ≤ gen M Λ n x) (x : ℝ) :
    gen M Λ (n+1) x = Λ n x + M.Lt x +
      ⨅ z : {z : ℝ // 0 ≤ z}, (M.orderCost (z:ℝ) + M.α * K M (gen M Λ n) (x + (z:ℝ))) := by
  rw [gen]
  have : ∀ z : {z : ℝ // 0 ≤ z}, M.orderCost (z : ℝ) + M.Lt x + Λ n x +
        M.α * (∫ t in Ioi (0 : ℝ), gen M Λ n (x + (z : ℝ) - t) * M.φ t) =
      (Λ n x + M.Lt x) + (M.orderCost (z:ℝ) + M.α * K M (gen M Λ n) (x + (z:ℝ))) := by
    intro z; simp only [K]; ring
  simp only [this]
  have : Nonempty {z : ℝ // 0 ≤ z} := ⟨⟨0, le_rfl⟩⟩
  rw [iInf_add_bdd]
  refine ⟨0, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact add_nonneg (orderCost_nonneg M _) (mul_nonneg M.α_nonneg (K_nonneg M hg0 _))

lemma W_eq (H : ℝ → ℝ) (hH0 : ∀ x, 0 ≤ H x) (x : ℝ) :
    (⨅ z : {z : ℝ // 0 ≤ z}, (M.orderCost (z:ℝ) + H (x + (z:ℝ)))) =
      min (H x) (M.K - M.c * x + ⨅ v : {v : ℝ // x < v}, (M.c * (v:ℝ) + H v)) := by
  have ne1 : Nonempty {z : ℝ // 0 ≤ z} := ⟨⟨0, le_rfl⟩⟩
  have ne2 : Nonempty {v : ℝ // x < v} := ⟨⟨x + 1, by linarith⟩⟩
  have bV : BddBelow (range fun v : {v : ℝ // x < v} => M.c * (v:ℝ) + H v) :=
    ⟨M.c * x, by
      rintro _ ⟨⟨v, hv⟩, rfl⟩
      have := mul_le_mul_of_nonneg_left hv.le M.c_nonneg; have := hH0 v; simp only; linarith⟩
  have bW : BddBelow (range fun z : {z : ℝ // 0 ≤ z} => M.orderCost (z:ℝ) + H (x + (z:ℝ))) :=
    ⟨0, by rintro _ ⟨z, rfl⟩; exact add_nonneg (orderCost_nonneg M _) (hH0 _)⟩
  apply le_antisymm
  · apply le_min
    · have := ciInf_le bW ⟨0, le_rfl⟩
      simp only [orderCost_zero, add_zero, zero_add] at this
      exact this
    · have : (⨅ z : {z : ℝ // 0 ≤ z}, (M.orderCost (z:ℝ) + H (x + (z:ℝ)))) - M.K + M.c * x ≤
          ⨅ v : {v : ℝ // x < v}, (M.c * (v:ℝ) + H v) := le_ciInf fun v => by
        have h := ciInf_le bW ⟨(v:ℝ) - x, by linarith [v.2]⟩
        have hp : 0 < (v:ℝ) - x := by linarith [v.2]
        have hoc : M.orderCost ((v:ℝ) - x) = M.K + M.c * ((v:ℝ) - x) := if_pos hp
        rw [hoc] at h
        rw [show x + ((v:ℝ) - x) = v by ring] at h
        linarith
      linarith
  · refine le_ciInf fun z => ?_
    rcases eq_or_lt_of_le z.2 with h | h
    · rw [← h, orderCost_zero, add_zero, zero_add]; exact min_le_left _ _
    · refine (min_le_right _ _).trans ?_
      have := ciInf_le bV ⟨x + (z:ℝ), by linarith⟩
      have hoc : M.orderCost (z:ℝ) = M.K + M.c * (z:ℝ) := if_pos h
      rw [hoc]
      linarith

lemma W_meas (H : ℝ → ℝ) (hH : Measurable H) (hH0 : ∀ x, 0 ≤ H x) :
    Measurable (fun x => ⨅ z : {z : ℝ // 0 ≤ z}, (M.orderCost (z:ℝ) + H (x + (z:ℝ)))) := by
  have e := funext (W_eq M H hH0)
  rw [e]
  have hmono : Monotone (fun x => ⨅ v : {v : ℝ // x < v}, (M.c * (v:ℝ) + H v)) := by
    intro x x' hxx'
    have : Nonempty {v : ℝ // x' < v} := ⟨⟨x' + 1, by linarith⟩⟩
    have bV : BddBelow (range fun v : {v : ℝ // x < v} => M.c * (v:ℝ) + H v) :=
      ⟨M.c * x, by
        rintro _ ⟨⟨v, hv⟩, rfl⟩
        have := mul_le_mul_of_nonneg_left hv.le M.c_nonneg; have := hH0 v; simp only; linarith⟩
    exact le_ciInf fun v => ciInf_le bV ⟨v, lt_of_le_of_lt hxx' v.2⟩
  exact hH.min ((measurable_const.sub (measurable_const.mul measurable_id)).add hmono.measurable)

lemma Lt_bound : ∃ a b : ℝ, 0 ≤ b ∧ ∀ x, M.Lt x ≤ a + b * |x| := by
  obtain ⟨a, b, h⟩ := M.Lt_growth
  refine ⟨a, max b 0, le_max_right _ _, fun x => (h x).trans ?_⟩
  have := mul_le_mul_of_nonneg_right (le_max_left b 0) (abs_nonneg x)
  linarith

theorem core : ∀ n, Gm (gen M (D M) n) ∧ (∀ x, 0 ≤ gen M (D M) n x) ∧
    ∀ x₁ w₁ x₂ : ℝ, x₁ + w₁ ≤ x₂ → M.sysCost n x₁ w₁ x₂ = M.isoCost n x₁ w₁ + gen M (D M) n x₂
  | 0 => ⟨⟨measurable_const, 0, 0, le_rfl, fun x => by simp [gen]⟩, fun x => le_rfl,
      fun x₁ w₁ x₂ _ => by simp [Model.sysCost, Model.isoCost, gen]⟩
  | n + 1 => by
    obtain ⟨hm, h0, hdec⟩ := core n
    have hH0 : ∀ v, 0 ≤ M.α * K M (gen M (D M) n) v :=
      fun v => mul_nonneg M.α_nonneg (K_nonneg M h0 _)
    have hW0 : ∀ x, 0 ≤ ⨅ z : {z : ℝ // 0 ≤ z},
        (M.orderCost (z:ℝ) + M.α * K M (gen M (D M) n) (x + (z:ℝ))) := fun x => by
      have : Nonempty {z : ℝ // 0 ≤ z} := ⟨⟨0, le_rfl⟩⟩
      exact le_ciInf fun z => add_nonneg (orderCost_nonneg M _) (hH0 _)
    have e : gen M (D M) (n+1) = fun x => D M n x + M.Lt x +
        ⨅ z : {z : ℝ // 0 ≤ z}, (M.orderCost (z:ℝ) + M.α * K M (gen M (D M) n) (x + (z:ℝ))) :=
      funext (gen_succ_eq M (D M) n h0)
    have hDp := D_props M n
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [e]
      exact (hDp.1.1.add (M.Lt_cont.measurable)).add
        (W_meas M _ ((K_meas M hm.1).const_mul _) hH0)
    · obtain ⟨A1, B1, hB1, hb1⟩ := hDp.1.2
      obtain ⟨a, b, hb, hlt⟩ := Lt_bound M
      obtain ⟨A3, B3, hB3, hb3⟩ := K_growth2 M hm
      refine ⟨A1 + a + M.α * A3, B1 + b + M.α * B3,
        by have := mul_nonneg M.α_nonneg hB3; linarith, fun x => ?_⟩
      rw [e]
      have hnn := add_nonneg (add_nonneg (hDp.2 x) (M.Lt_nonneg x)) (hW0 x)
      rw [abs_of_nonneg hnn]
      have hb' : BddBelow (range fun z : {z : ℝ // 0 ≤ z} =>
          M.orderCost (z:ℝ) + M.α * K M (gen M (D M) n) (x + (z:ℝ))) :=
        ⟨0, by rintro _ ⟨z, rfl⟩; exact add_nonneg (orderCost_nonneg M _) (hH0 _)⟩
      have h1 := ciInf_le hb' ⟨0, le_rfl⟩
      simp only [orderCost_zero, add_zero, zero_add] at h1
      have h2 := hb1 x; have h3 := hlt x; have h4 := hb3 x
      have h5 := le_abs_self (D M n x)
      have h6 := mul_le_mul_of_nonneg_left ((le_abs_self (K M (gen M (D M) n) x)).trans h4)
        M.α_nonneg
      nlinarith
    · intro x; rw [e]; exact add_nonneg (add_nonneg (hDp.2 x) (M.Lt_nonneg x)) (hW0 x)
    · intro x₁ w₁ x₂ hdom
      rw [step M n _ hm h0 hdec x₁ w₁ x₂ hdom, Q_lem M n x₁ w₁ x₂ hdom, e]
      have : ∀ z : {z : ℝ // 0 ≤ z}, M.orderCost (z:ℝ) + M.Lt x₂ +
          M.α * (∫ t in Ioi (0:ℝ), gen M (D M) n (x₂ + (z:ℝ) - t) * M.φ t) =
          M.Lt x₂ + (M.orderCost (z:ℝ) + M.α * K M (gen M (D M) n) (x₂ + (z:ℝ))) := by
        intro z; simp only [K]; ring
      simp only [this]
      have : Nonempty {z : ℝ // 0 ≤ z} := ⟨⟨0, le_rfl⟩⟩
      rw [iInf_add_bdd _ _ ⟨0, by rintro _ ⟨z, rfl⟩; exact add_nonneg (orderCost_nonneg M _) (hH0 _)⟩]
      ring


lemma isoObj_sub (n : ℕ) (x₁ w₁ : ℝ) :
    M.isoObj n x₁ w₁ (x₁ + w₁) - M.isoCost (n+1) x₁ w₁ = D M n (x₁ + w₁) := by
  obtain ⟨P, hP⟩ := shape M n x₁ w₁
  have : Nonempty {y : ℝ // x₁ + w₁ ≤ y} := ⟨⟨x₁ + w₁, le_rfl⟩⟩
  rw [Model.isoCost_succ]
  simp only [hP]
  rw [iInf_add_bdd _ _ (Ps_bdd M n _)]
  unfold D; ring

lemma D_zero (x : ℝ) : D M 0 x = 0 := by
  unfold D
  rw [iInf_ge_eq x x (Ps M 0) le_rfl (fun y hy => by
    simp only [Ps, Psx]; nlinarith [M.c1_nonneg])]
  ring

lemma D_one (x : ℝ) : D M 1 x = 0 := by
  unfold D
  rw [iInf_ge_eq x x (Ps M 1) le_rfl (fun y hy => by
    simp only [Ps, Psx]; nlinarith [M.c1_nonneg])]
  ring

theorem theorem1_core :
    (∃ g : ℕ → ℝ → ℝ, (∀ x₂ : ℝ, g 1 x₂ = M.Lt x₂) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ x₁ w₁ x₂ : ℝ, x₁ + w₁ ≤ x₂ →
        M.sysCost n x₁ w₁ x₂ = M.isoCost n x₁ w₁ + g n x₂) ∧
    (∀ (n : ℕ) (x₁ w₁ x₂ yiso : ℝ), x₁ + w₁ ≤ x₂ → x₁ + w₁ ≤ yiso →
      (∀ y : ℝ, x₁ + w₁ ≤ y → M.isoObj n x₁ w₁ yiso ≤ M.isoObj n x₁ w₁ y) →
      ∀ y z : ℝ, x₁ + w₁ ≤ y → y ≤ x₂ → 0 ≤ z →
        M.sysObj n x₁ w₁ x₂ (min x₂ yiso) z ≤ M.sysObj n x₁ w₁ x₂ y z) := by
  refine ⟨⟨gen M (D M), fun x₂ => ?_, fun n _ => (core M n).2.2⟩, ?_⟩
  · rw [gen_succ_eq M (D M) 0 (core M 0).2.1, D_zero]
    have : ∀ z : {z : ℝ // 0 ≤ z},
        M.orderCost (z:ℝ) + M.α * K M (gen M (D M) 0) (x₂ + (z:ℝ)) = M.orderCost z := by
      intro z; simp [K, gen]
    simp only [this]
    rw [iInf_ge_eq 0 0 (M.orderCost) le_rfl
      (fun z _ => by rw [orderCost_zero]; exact orderCost_nonneg M z), orderCost_zero]
    ring
  · intro n x₁ w₁ x₂ yiso hdom hy0 hopt y z hy1 hy2 hz
    have hc := core M n
    rw [sysObj_split M n _ hc.1 hc.2.2 _ _ _ _ _ (min_le_left _ _) hz,
        sysObj_split M n _ hc.1 hc.2.2 _ _ _ _ _ hy2 hz]
    have : M.isoObj n x₁ w₁ (min x₂ yiso) ≤ M.isoObj n x₁ w₁ y := by
      rcases le_total yiso x₂ with h | h
      · rw [min_eq_right h]; exact hopt y hy1
      · rw [min_eq_left h]
        obtain ⟨P, hP⟩ := shape M n x₁ w₁
        rcases eq_or_lt_of_le h with h' | h'
        · rw [h']; exact hopt y hy1
        · have h1 := hopt x₂ hdom
          rw [hP, hP] at h1 ⊢
          have := cvx_aux (Ps_good M n).1 hy2 h' (by linarith)
          linarith
    linarith

lemma Lambda_eq_D (xbar : ℕ → ℝ) (hxbar : ∀ n : ℕ, 2 ≤ n → M.IsCriticalNumber n (xbar (n + 1)))
    (n : ℕ) (x : ℝ) : M.Lambda n (xbar (n+1)) x = D M n x := by
  match n with
  | 0 => rw [D_zero]; simp [Model.Lambda]
  | 1 => rw [D_one]; simp [Model.Lambda]
  | m + 2 =>
    have hc := hxbar (m+2) (by omega)
    have hs := isoObj_sub M (m+2) x 0
    rw [add_zero] at hs
    by_cases hx : x < xbar (m+2+1)
    · rw [Model.Lambda, if_pos ⟨by omega, hx⟩]
      have h := lambda_eq25_core M (m+2) (by omega) _ hc x 0 x (by simp) hx
      rw [← hs]
      exact h.symm
    · rw [Model.Lambda, if_neg (fun h => hx h.2), ← hs]
      have : M.isoCost (m+2+1) x 0 = M.isoObj (m+2) x 0 x := by
        rw [Model.isoCost_succ, iInf_ge_eq (x+0) (max (x+0) (xbar (m+2+1))) _ (le_max_left _ _)
          (hc x 0), max_eq_left (by simp; linarith), add_zero]
      rw [this, sub_self]

lemma gClark_eq (xbar : ℕ → ℝ) (hxbar : ∀ n : ℕ, 2 ≤ n → M.IsCriticalNumber n (xbar (n + 1))) :
    ∀ n, M.gClark xbar n = gen M (D M) n
  | 0 => rfl
  | n + 1 => by
    funext x
    have ih := gClark_eq xbar hxbar n
    rw [Model.gClark, gen, ih]
    simp only [Lambda_eq_D M xbar hxbar n x]

theorem theorem2_core (xbar : ℕ → ℝ)
    (hxbar : ∀ n : ℕ, 2 ≤ n → M.IsCriticalNumber n (xbar (n + 1))) :
    ∀ n : ℕ, 1 ≤ n → ∀ x₁ w₁ x₂ : ℝ, x₁ + w₁ ≤ x₂ →
      M.sysCost n x₁ w₁ x₂ = M.isoCost n x₁ w₁ + M.gClark xbar n x₂ := by
  intro n _ x₁ w₁ x₂ hdom
  rw [gClark_eq M xbar hxbar n]
  exact (core M n).2.2 x₁ w₁ x₂ hdom

theorem eq18_eq19_core (n : ℕ) (G : ℝ → ℝ)
    (hG : ∀ x₁ w₁ x₂ : ℝ, x₁ + w₁ ≤ x₂ → M.sysCost n x₁ w₁ x₂ = M.isoCost n x₁ w₁ + G x₂)
    (xbar : ℝ) (hxbar : M.IsCriticalNumber n xbar)
    (x₁ w₁ x₂ : ℝ) (hdom : x₁ + w₁ ≤ x₂) :
    (xbar ≤ x₂ →
      M.sysCost (n + 1) x₁ w₁ x₂ = M.isoCost (n + 1) x₁ w₁ +
        ⨅ z : {z : ℝ // 0 ≤ z}, (M.orderCost (z : ℝ) + M.Lt x₂ +
          M.α * ∫ t in Ioi (0 : ℝ), G (x₂ + (z : ℝ) - t) * M.φ t)) ∧
    (x₂ < xbar →
      M.sysCost (n + 1) x₁ w₁ x₂ = M.c1 * (x₂ - x₁ - w₁) + M.L x₁ +
        M.α * (∫ t in Ioi (0 : ℝ), M.isoCost n (x₁ + w₁ - t) (x₂ - x₁ - w₁) * M.φ t) +
        ⨅ z : {z : ℝ // 0 ≤ z}, (M.orderCost (z : ℝ) + M.Lt x₂ +
          M.α * ∫ t in Ioi (0 : ℝ), G (x₂ + (z : ℝ) - t) * M.φ t)) := by
  have hc := core M n
  have hGe : G = gen M (D M) n := by
    funext x
    have h1 := hG x 0 x (by simp)
    have h2 := hc.2.2 x 0 x (by simp)
    linarith
  subst hGe
  have hs := step M n _ hc.1 hc.2.1 hc.2.2 x₁ w₁ x₂ hdom
  obtain ⟨P, hP⟩ := shape M n x₁ w₁
  constructor
  · intro hx
    rw [hs]
    congr 1
    refine (iInf_Icc_eq (x₁ + w₁) x₂ (max (x₁ + w₁) xbar) (M.isoObj n x₁ w₁)
      ⟨le_max_left _ _, max_le hdom hx⟩ (fun y hy _ => hxbar x₁ w₁ y hy)).trans ?_
    rw [Model.isoCost_succ, iInf_ge_eq (x₁ + w₁) (max (x₁ + w₁) xbar) _ (le_max_left _ _)
      (hxbar x₁ w₁)]
  · intro hx
    rw [hs]
    congr 1
    refine (iInf_Icc_eq (x₁ + w₁) x₂ x₂ (M.isoObj n x₁ w₁) ⟨hdom, le_rfl⟩ ?_).trans rfl
    intro y hy1 hy2
    have h1 := hxbar x₁ w₁ x₂ hdom
    rw [max_eq_right (by linarith)] at h1
    rw [hP, hP] at h1 ⊢
    have := cvx_aux (Ps_good M n).1 hy2 hx (by linarith)
    linarith

end CSX
end ClarkScarf.Serial

open ClarkScarf.Serial


theorem solution (M : Model) (n : ℕ) (G : ℝ → ℝ)
    (hG : ∀ x₁ w₁ x₂ : ℝ, x₁ + w₁ ≤ x₂ → M.sysCost n x₁ w₁ x₂ = M.isoCost n x₁ w₁ + G x₂)
    (xbar : ℝ) (hxbar : M.IsCriticalNumber n xbar)
    (x₁ w₁ x₂ : ℝ) (hdom : x₁ + w₁ ≤ x₂) :
    (xbar ≤ x₂ →
      M.sysCost (n + 1) x₁ w₁ x₂ = M.isoCost (n + 1) x₁ w₁ +
        ⨅ z : {z : ℝ // 0 ≤ z}, (M.orderCost (z : ℝ) + M.Lt x₂ +
          M.α * ∫ t in Ioi (0 : ℝ), G (x₂ + (z : ℝ) - t) * M.φ t)) ∧
    (x₂ < xbar →
      M.sysCost (n + 1) x₁ w₁ x₂ = M.c1 * (x₂ - x₁ - w₁) + M.L x₁ +
        M.α * (∫ t in Ioi (0 : ℝ), M.isoCost n (x₁ + w₁ - t) (x₂ - x₁ - w₁) * M.φ t) +
        ⨅ z : {z : ℝ // 0 ≤ z}, (M.orderCost (z : ℝ) + M.Lt x₂ +
          M.α * ∫ t in Ioi (0 : ℝ), G (x₂ + (z : ℝ) - t) * M.φ t)) := by
  exact CSX.eq18_eq19_core M n G hG xbar hxbar x₁ w₁ x₂ hdom
