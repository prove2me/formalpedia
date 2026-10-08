-- Prove2me | solution 1 for ClarkScarf.Serial.isoCost_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T01:50:39.878381+00:00
-- url     : https://prove2.me/submissions/3892c680-89ed-4775-8a56-856ee4fe490a

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

end CSX
end ClarkScarf.Serial

open ClarkScarf.Serial


theorem solution (M : Model) (n : ℕ) (hn : 2 ≤ n) (x₁ w₁ : ℝ) :
    M.isoCost n x₁ w₁ =
      M.L x₁ + M.α * (∫ t in Ioi (0 : ℝ), M.L (x₁ + w₁ - t) * M.φ t) + M.fLag n (x₁ + w₁) := by
  exact CSX.isoCost_decomposition_core M n hn x₁ w₁
