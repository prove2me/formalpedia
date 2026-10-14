-- Prove2me | solution 1 for Disjunctive.Polarity.hull_eq_polar_inter_reverse_polar
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:57:32.747052+00:00
-- url     : https://prove2.me/submissions/8276a6f6-27bb-40fe-bf5d-d159c203e9d8

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Polars



namespace Disjunctive.Polarity

open Pointwise

section PolarAux

variable {n : ℕ}

lemma pp_dual (f : StrongDual ℝ (Fin n → ℝ)) :
    ∃ w : Fin n → ℝ, ∀ y, f y = dotProduct w y := by
  refine ⟨fun i => f (fun j => if i = j then 1 else 0), fun y => ?_⟩
  have := LinearMap.pi_apply_eq_sum_univ f.toLinearMap y
  simp only [ContinuousLinearMap.coe_coe] at this
  rw [this, dotProduct]
  exact Finset.sum_congr rfl (fun i _ => by rw [smul_eq_mul, mul_comm])

lemma pp_isLinear (w : Fin n → ℝ) : IsLinearMap ℝ (fun y : Fin n → ℝ => dotProduct w y) :=
  ⟨fun x y => dotProduct_add w x y, fun c x => dotProduct_smul c w x⟩

lemma pp_cont (w : Fin n → ℝ) : Continuous (fun y : Fin n → ℝ => dotProduct w y) := by
  simp only [dotProduct]; fun_prop

lemma pp_ge_closed (w : Fin n → ℝ) (c : ℝ) : IsClosed {y : Fin n → ℝ | c ≤ dotProduct w y} :=
  isClosed_le continuous_const (pp_cont w)

lemma pp_le_closed (w : Fin n → ℝ) (c : ℝ) : IsClosed {y : Fin n → ℝ | dotProduct w y ≤ c} :=
  isClosed_le (pp_cont w) continuous_const

lemma pp_hull_ge (S : Set (Fin n → ℝ)) (w : Fin n → ℝ) (c : ℝ)
    (h : ∀ y ∈ S, c ≤ dotProduct w y) : ∀ y ∈ closure (convexHull ℝ S), c ≤ dotProduct w y := by
  intro y hy
  have : closure (convexHull ℝ S) ⊆ {y | c ≤ dotProduct w y} :=
    closure_minimal (convexHull_min h (convex_halfSpace_ge (pp_isLinear w) c)) (pp_ge_closed w c)
  exact this hy

lemma pp_hull_le (S : Set (Fin n → ℝ)) (w : Fin n → ℝ) (c : ℝ)
    (h : ∀ y ∈ S, dotProduct w y ≤ c) : ∀ y ∈ closure (convexHull ℝ S), dotProduct w y ≤ c := by
  intro y hy
  have : closure (convexHull ℝ S) ⊆ {y | dotProduct w y ≤ c} :=
    closure_minimal (convexHull_min h (convex_halfSpace_le (pp_isLinear w) c)) (pp_le_closed w c)
  exact this hy

lemma pp_dot_sum {k : ℕ} (x : Fin n → ℝ) (c : Fin k → ℝ) (y : Fin k → Fin n → ℝ) :
    dotProduct x (∑ i, c i • y i) = ∑ i, c i * dotProduct x (y i) := by
  simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

lemma pp_cone_add (S : Set (Fin n → ℝ)) {x1 x2 : Fin n → ℝ} (h1 : x1 ∈ ConeHull S)
    (h2 : x2 ∈ ConeHull S) : x1 + x2 ∈ ConeHull S := by
  obtain ⟨k1, c1, y1, hc1, rfl⟩ := h1
  obtain ⟨k2, c2, y2, hc2, rfl⟩ := h2
  refine ⟨k1 + k2, Fin.append c1 c2, Fin.append y1 y2, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa using hc1 i
    · simpa using hc2 i
  · rw [Fin.sum_univ_add]; simp

lemma pp_cone_smul (S : Set (Fin n → ℝ)) {x : Fin n → ℝ} (h : x ∈ ConeHull S) {t : ℝ}
    (ht : 0 ≤ t) : t • x ∈ ConeHull S := by
  obtain ⟨k, c, y, hc, rfl⟩ := h
  refine ⟨k, fun i => t * c i, y, fun i => ⟨mul_nonneg ht (hc i).1, (hc i).2⟩, ?_⟩
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [smul_smul])

lemma pp_cone_mem (S : Set (Fin n → ℝ)) {y : Fin n → ℝ} (h : y ∈ S) : y ∈ ConeHull S :=
  ⟨1, fun _ => 1, fun _ => y, fun _ => ⟨zero_le_one, h⟩, by simp⟩

lemma pp_cone_zero (S : Set (Fin n → ℝ)) : (0 : Fin n → ℝ) ∈ ConeHull S :=
  ⟨0, fun _ => 1, fun _ => 0, fun i => i.elim0, by simp⟩

lemma pp_hull_sub_cone (S : Set (Fin n → ℝ)) : convexHull ℝ S ⊆ ConeHull S := by
  apply convexHull_min (fun y hy => pp_cone_mem S hy)
  intro x hx y hy a b ha hb _
  exact pp_cone_add S (pp_cone_smul S hx ha) (pp_cone_smul S hy hb)

lemma pp_smul_closure (S : Set (Fin n → ℝ)) {c : Fin n → ℝ} (hc : c ∈ closure (convexHull ℝ S))
    {t : ℝ} (ht : 0 ≤ t) : t • c ∈ closure (ConeHull S) := by
  have h1 : (fun y => t • y) '' closure (convexHull ℝ S) ⊆
      closure ((fun y => t • y) '' convexHull ℝ S) :=
    image_closure_subset_closure_image (continuous_const_smul t)
  have h2 : (fun y => t • y) '' convexHull ℝ S ⊆ ConeHull S := by
    rintro _ ⟨y, hy, rfl⟩
    exact pp_cone_smul S (pp_hull_sub_cone S hy) ht
  exact closure_mono h2 (h1 ⟨c, hc, rfl⟩)

lemma pp_exists_rev (S : Set (Fin n → ℝ)) (h0 : 0 ∉ closure (convexHull ℝ S)) :
    ∃ x0 : Fin n → ℝ, ∀ y ∈ S, 1 ≤ dotProduct x0 y := by
  obtain ⟨f, u, hfu, hb⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ S).closure
    isClosed_closure h0
  obtain ⟨w, hw⟩ := pp_dual f
  have hu : 0 < u := by simpa using hfu
  refine ⟨u⁻¹ • w, fun y hy => ?_⟩
  have := hb y (subset_closure (subset_convexHull ℝ S hy))
  rw [hw] at this
  rw [smul_dotProduct, smul_eq_mul, le_inv_mul_iff₀ hu, mul_one]
  exact this.le

/-- The set `D = ⋃_{λ ≥ 1} λ C`. -/
def ppD (S : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {z | ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 ∧ μ • z ∈ closure (convexHull ℝ S)}

lemma ppD_closed (S : Set (Fin n → ℝ)) (h0 : 0 ∉ closure (convexHull ℝ S)) :
    IsClosed (ppD S) := by
  have heq : ppD S = Prod.snd '' {p : Set.Icc (0:ℝ) 1 × (Fin n → ℝ) |
      (p.1 : ℝ) • p.2 ∈ closure (convexHull ℝ S)} := by
    ext z
    constructor
    · rintro ⟨μ, hμ0, hμ1, hμ⟩
      exact ⟨(⟨μ, hμ0.le, hμ1⟩, z), hμ, rfl⟩
    · rintro ⟨⟨⟨μ, hμ⟩, z'⟩, hp, rfl⟩
      have hp' : μ • z' ∈ closure (convexHull ℝ S) := hp
      refine ⟨μ, ?_, hμ.2, hp'⟩
      rcases hμ.1.lt_or_eq with h | h
      · exact h
      · exfalso; apply h0; rw [← h, zero_smul] at hp'; exact hp'
  rw [heq]
  apply isClosedMap_snd_of_compactSpace
  exact isClosed_closure.preimage ((continuous_subtype_val.comp continuous_fst).smul continuous_snd)

lemma ppD_convex (S : Set (Fin n → ℝ)) : Convex ℝ (ppD S) := by
  intro z1 hz1 z2 hz2 a b ha hb hab
  obtain ⟨μ1, h10, h11, h1⟩ := hz1
  obtain ⟨μ2, h20, h21, h2⟩ := hz2
  have hC : Convex ℝ (closure (convexHull ℝ S)) := (convex_convexHull ℝ S).closure
  set L := a / μ1 + b / μ2 with hL
  have hL1 : 1 ≤ L := by
    have e1 : a ≤ a / μ1 := by rw [le_div_iff₀ h10]; nlinarith
    have e2 : b ≤ b / μ2 := by rw [le_div_iff₀ h20]; nlinarith
    linarith
  have hL0 : 0 < L := by linarith
  refine ⟨L⁻¹, inv_pos.mpr hL0, inv_le_one_of_one_le₀ hL1, ?_⟩
  have key : L⁻¹ • (a • z1 + b • z2) =
      (L⁻¹ * a / μ1) • (μ1 • z1) + (L⁻¹ * b / μ2) • (μ2 • z2) := by
    rw [smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    congr 2
    · field_simp
    · field_simp
  rw [key]
  apply hC h1 h2
  · positivity
  · positivity
  · rw [mul_div_assoc, mul_div_assoc, ← mul_add, ← hL]; exact inv_mul_cancel₀ hL0.ne'

lemma ppD_smul (S : Set (Fin n → ℝ)) {c : Fin n → ℝ} (hc : c ∈ closure (convexHull ℝ S))
    {t : ℝ} (ht : 1 ≤ t) : t • c ∈ ppD S := by
  refine ⟨t⁻¹, inv_pos.mpr (by linarith), inv_le_one_of_one_le₀ ht, ?_⟩
  rw [smul_smul, inv_mul_cancel₀ (by linarith), one_smul]; exact hc

lemma pp_rr_sub_D (S : Set (Fin n → ℝ)) (h0 : 0 ∉ closure (convexHull ℝ S)) :
    ReversePolar (ReversePolar S) ⊆ ppD S := by
  intro z hz
  by_contra hzD
  obtain ⟨f, u, hfz, hfD⟩ := geometric_hahn_banach_point_closed (ppD_convex S)
    (ppD_closed S h0) hzD
  obtain ⟨w, hw⟩ := pp_dual f
  rw [hw] at hfz
  have hSC : ∀ y ∈ S, y ∈ closure (convexHull ℝ S) :=
    fun y hy => subset_closure (subset_convexHull ℝ S hy)
  have hSD : ∀ y ∈ S, u < dotProduct w y := by
    intro y hy
    have := hfD y (by simpa using ppD_smul S (hSC y hy) le_rfl)
    rwa [hw] at this
  rcases lt_or_ge 0 u with hu | hu
  · -- x = u⁻¹ w is in S#
    have hx : u⁻¹ • w ∈ ReversePolar S := by
      intro y hy
      rw [smul_dotProduct, smul_eq_mul, le_inv_mul_iff₀ hu, mul_one]
      exact (hSD y hy).le
    have := hz _ hx
    rw [dotProduct_comm, smul_dotProduct, smul_eq_mul, le_inv_mul_iff₀ hu, mul_one] at this
    linarith
  · have hwS : ∀ y ∈ S, 0 ≤ dotProduct w y := by
      intro y hy
      by_contra hneg
      push_neg at hneg
      have h1 : 1 ≤ u / dotProduct w y + 1 := by
        have : 0 ≤ u / dotProduct w y := div_nonneg_of_nonpos hu hneg.le
        linarith
      have := hfD _ (ppD_smul S (hSC y hy) h1)
      rw [hw, dotProduct_smul, smul_eq_mul, add_mul, div_mul_cancel₀ _ hneg.ne] at this
      linarith
    obtain ⟨x0, hx0⟩ := pp_exists_rev S h0
    have hwz : dotProduct w z < 0 := by linarith
    set t := (|dotProduct x0 z| + 1) / (-dotProduct w z) with ht
    have ht0 : 0 ≤ t := div_nonneg (by positivity) (by linarith)
    have hx : x0 + t • w ∈ ReversePolar S := by
      intro y hy
      rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
      have := hx0 y hy
      have := mul_nonneg ht0 (hwS y hy)
      linarith
    have := hz _ hx
    rw [dotProduct_comm, add_dotProduct, smul_dotProduct, smul_eq_mul] at this
    have htw : t * dotProduct w z = -(|dotProduct x0 z| + 1) := by
      rw [ht, div_mul_eq_mul_div, div_eq_iff (by linarith)]; ring
    have := le_abs_self (dotProduct x0 z)
    linarith

theorem reverse_polar_involution_core {n : ℕ} (S : Set (Fin n → ℝ))
    (h0 : 0 ∉ closure (convexHull ℝ S)) :
    ReversePolar (ReversePolar S) = closure (convexHull ℝ S) + closure (ConeHull S) := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨μ, hμ0, hμ1, hμ⟩ := pp_rr_sub_D S h0 hz
    rw [Set.mem_add]
    refine ⟨μ • z, hμ, (μ⁻¹ - 1) • (μ • z), pp_smul_closure S hμ ?_, ?_⟩
    · have : 1 ≤ μ⁻¹ := one_le_inv_iff₀.mpr ⟨hμ0, hμ1⟩
      linarith
    · have e : (1 + (μ⁻¹ - 1)) * μ = 1 := by
        rw [add_sub_cancel]; exact inv_mul_cancel₀ hμ0.ne'
      calc μ • z + (μ⁻¹ - 1) • (μ • z) = (1 + (μ⁻¹ - 1)) • (μ • z) := by rw [add_smul, one_smul]
        _ = z := by rw [smul_smul, e, one_smul]
  · intro z hz
    rw [Set.mem_add] at hz
    obtain ⟨c, hc, k, hk, rfl⟩ := hz
    intro x hx
    have h1 : 1 ≤ dotProduct x c := pp_hull_ge S x 1 hx c hc
    have h2 : 0 ≤ dotProduct x k := by
      have : closure (ConeHull S) ⊆ {y | 0 ≤ dotProduct x y} := by
        apply closure_minimal _ (pp_ge_closed x 0)
        rintro _ ⟨k', c', y', hcy, rfl⟩
        simp only [Set.mem_setOf_eq]
        rw [pp_dot_sum]
        exact Finset.sum_nonneg (fun i _ => mul_nonneg (hcy i).1
          (le_trans zero_le_one (hx _ (hcy i).2)))
      exact this hk
    rw [dotProduct_comm, dotProduct_add]
    linarith

theorem hull_eq_polar_inter_reverse_polar_core {n : ℕ} (S : Set (Fin n → ℝ))
    (h0 : 0 ∉ closure (convexHull ℝ S)) :
    closure (convexHull ℝ S) = Polar (Polar S) ∩ ReversePolar (ReversePolar S) := by
  apply Set.Subset.antisymm
  · intro c hc
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [dotProduct_comm]; exact pp_hull_le S x 1 hx c hc
    · rw [reverse_polar_involution_core S h0]
      exact Set.mem_add.mpr ⟨c, hc, 0, subset_closure (pp_cone_zero S), add_zero c⟩
  · rintro z ⟨hzP, hzR⟩
    obtain ⟨μ, hμ0, hμ1, hμ⟩ := pp_rr_sub_D S h0 hzR
    by_contra hzC
    obtain ⟨f, u, hfC, hfz⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ S).closure
      isClosed_closure hzC
    obtain ⟨w, hw⟩ := pp_dual f
    rw [hw] at hfz
    have h1 := hfC _ hμ
    rw [hw, dotProduct_smul, smul_eq_mul] at h1
    have hwz : 0 < dotProduct w z := by nlinarith
    have hu : 0 < u := by nlinarith
    have hx : u⁻¹ • w ∈ Polar S := by
      intro y hy
      have := hfC y (subset_closure (subset_convexHull ℝ S hy))
      rw [hw] at this
      rw [smul_dotProduct, smul_eq_mul, inv_mul_le_iff₀ hu, mul_one]
      exact this.le
    have := hzP _ hx
    rw [dotProduct_comm, smul_dotProduct, smul_eq_mul, inv_mul_le_iff₀ hu, mul_one] at this
    linarith

end PolarAux

end Disjunctive.Polarity

open Disjunctive.Polarity
open Pointwise

theorem solution {n : ℕ} (S : Set (Fin n → ℝ))
    (h0 : 0 ∉ closure (convexHull ℝ S)) :
    closure (convexHull ℝ S) = Polar (Polar S) ∩ ReversePolar (ReversePolar S) := by
  exact hull_eq_polar_inter_reverse_polar_core S h0
