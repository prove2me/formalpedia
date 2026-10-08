-- Prove2me | solution 1 for ClarkScarf.Serial.L_one_period_convex
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T01:47:18.1417+00:00
-- url     : https://prove2.me/submissions/be1b4b07-9097-4e06-be24-90660a1dbe07

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

end CSX
end ClarkScarf.Serial

open ClarkScarf.Serial


theorem solution (M : Model) :
    ConvexOn ℝ univ (fun y : ℝ => M.α * ∫ t₁ in Ioi (0 : ℝ), ∫ t₂ in Ioi (0 : ℝ),
      M.L (y - t₁ - t₂) * M.φ t₁ * M.φ t₂) := by
  exact CSX.L_one_period_convex_core M
