-- Prove2me | solution 1 for Disjunctive.Polymatroids.polymatroid_union_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T16:37:12.205991+00:00
-- url     : https://prove2.me/submissions/c328b763-f24e-473d-b8c2-6ed67a0ff93e

import Mathlib
import Definitions.Def_Disjunctive_Polymatroids_Basic



namespace Disjunctive.Polymatroids

open Finset
open scoped Pointwise

section greedy
variable {n : ℕ} (σ : Equiv.Perm (Fin n))

def pmPos (i : Fin n) : ℕ := (σ.symm i : ℕ)

def pmS (k : ℕ) : Finset (Fin n) := univ.filter (fun i => pmPos σ i < k)

lemma pmS_zero : pmS σ 0 = ∅ := by
  ext i; simp [pmS]

lemma pmS_n : pmS σ n = univ := by
  ext i; simp [pmS, pmPos, (σ.symm i).isLt]

lemma pmS_succ (i : Fin n) : pmS σ (pmPos σ i + 1) = insert i (pmS σ (pmPos σ i)) := by
  ext j
  simp only [pmS, mem_filter, mem_univ, true_and, mem_insert]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
    · exact Or.inr h
    · left
      have : σ.symm j = σ.symm i := Fin.ext h
      exact σ.symm.injective this
  · rintro (h | h)
    · subst h; omega
    · omega

lemma pm_not_mem (i : Fin n) : i ∉ pmS σ (pmPos σ i) := by
  simp [pmS]

lemma pmPos_sigma (k : Fin n) : pmPos σ (σ k) = k := by
  simp [pmPos]

def pmGv (f : Finset (Fin n) → ℝ) (i : Fin n) : ℝ :=
  f (pmS σ (pmPos σ i + 1)) - f (pmS σ (pmPos σ i))

lemma pm_sum_reindex (H : ℕ → ℝ) : ∑ i : Fin n, H (pmPos σ i) = ∑ k ∈ range n, H k := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Equiv.sum_comp σ.symm (fun k : Fin n => H k)

lemma pmGv_nonneg {f : Finset (Fin n) → ℝ} (hf : IsPolymatroidRankFunction f) (i : Fin n) :
    0 ≤ pmGv σ f i := by
  unfold pmGv
  rw [pmS_succ]
  have := hf.2.1 _ _ (subset_insert i (pmS σ (pmPos σ i)))
  linarith

lemma pmGv_feasible {f : Finset (Fin n) → ℝ} (hf : IsPolymatroidRankFunction f)
    (A : Finset (Fin n)) : ∑ i ∈ A, pmGv σ f i ≤ f A := by
  set G : ℕ → ℝ := fun k => f (A ∩ pmS σ k) with hG
  have h1 : ∑ i ∈ A, pmGv σ f i ≤ ∑ i ∈ A, (G (pmPos σ i + 1) - G (pmPos σ i)) := by
    apply sum_le_sum
    intro i hi
    simp only [hG, pmGv]
    rw [pmS_succ]
    have hins : A ∩ insert i (pmS σ (pmPos σ i)) = insert i (A ∩ pmS σ (pmPos σ i)) := by
      rw [inter_insert_of_mem hi]
    rw [hins]
    have hsub := hf.2.2 (insert i (A ∩ pmS σ (pmPos σ i))) (pmS σ (pmPos σ i))
    have e1 : insert i (A ∩ pmS σ (pmPos σ i)) ∪ pmS σ (pmPos σ i) = insert i (pmS σ (pmPos σ i)) := by
      ext j; simp only [mem_union, mem_insert, mem_inter]; tauto
    have e2 : insert i (A ∩ pmS σ (pmPos σ i)) ∩ pmS σ (pmPos σ i) = A ∩ pmS σ (pmPos σ i) := by
      ext j; simp only [mem_insert, mem_inter]
      constructor
      · rintro ⟨h | h, h'⟩
        · subst h; exact absurd h' (pm_not_mem σ j)
        · exact h
      · rintro h; exact ⟨Or.inr h, h.2⟩
    rw [e1, e2] at hsub
    linarith
  have h2 : ∑ i ∈ A, (G (pmPos σ i + 1) - G (pmPos σ i)) =
      ∑ i : Fin n, (G (pmPos σ i + 1) - G (pmPos σ i)) := by
    apply sum_subset (subset_univ A)
    intro i _ hi
    simp only [hG]
    rw [pmS_succ, inter_insert_of_notMem hi, sub_self]
  have h3 : ∑ i : Fin n, (G (pmPos σ i + 1) - G (pmPos σ i)) = G n - G 0 := by
    rw [pm_sum_reindex σ (fun k => G (k + 1) - G k), sum_range_sub]
  have h4 : G n - G 0 = f A := by
    simp only [hG, pmS_n, pmS_zero, inter_univ, inter_empty, hf.1, sub_zero]
  linarith

end greedy

lemma pm_abel (D : ℕ → ℝ) (hD : Antitone D) (hD0 : ∀ k, 0 ≤ D k) (e : ℕ → ℝ) (he0 : e 0 = 0)
    (he : ∀ k, 0 ≤ e k) : ∀ N, D N * e N ≤ ∑ k ∈ range N, D k * (e (k + 1) - e k) := by
  intro N
  induction N with
  | zero => simp [he0]
  | succ N ih =>
    rw [sum_range_succ]
    have := hD (Nat.le_succ N)
    have := he (N + 1)
    nlinarith

lemma pm_convex {n : ℕ} (f : Finset (Fin n) → ℝ) : Convex ℝ (PolymatroidP f) := by
  intro y hy z hz a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro i
    simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hy.1 i; have := hz.1 i
    simp only [Pi.zero_apply] at *
    positivity
  · intro A
    have e : SumOver (a • y + b • z) A = a * SumOver y A + b * SumOver z A := by
      simp [SumOver, sum_add_distrib, mul_sum]
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left (hy.2 A) ha
    have h2 := mul_le_mul_of_nonneg_left (hz.2 A) hb
    have : a * f A + b * f A = f A := by rw [← add_mul, hab, one_mul]
    linarith

lemma pm_compact {n : ℕ} (f : Finset (Fin n) → ℝ) : IsCompact (PolymatroidP f) := by
  have hcl : IsClosed (PolymatroidP f) := by
    have : PolymatroidP f = {y | 0 ≤ y} ∩ ⋂ A : Finset (Fin n), {y | SumOver y A ≤ f A} := by
      ext y; simp [PolymatroidP]
    rw [this]
    apply IsClosed.inter (isClosed_le continuous_const continuous_id)
    apply isClosed_iInter
    intro A
    apply isClosed_le _ continuous_const
    unfold SumOver
    exact continuous_finsetSum _ (fun i _ => continuous_apply i)
  apply (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => f univ)).of_isClosed_subset hcl
  intro y hy
  refine ⟨hy.1, fun i => ?_⟩
  have h1 := hy.2 univ
  have h2 : y i ≤ SumOver y univ := by
    unfold SumOver
    exact single_le_sum (fun j _ => hy.1 j) (mem_univ i)
  simp only
  linarith

theorem pm_sum_thm {n : ℕ} (f g : Finset (Fin n) → ℝ) (hf : IsPolymatroidRankFunction f)
    (hg : IsPolymatroidRankFunction g) (x : Fin n → ℝ) (hx0 : 0 ≤ x)
    (hx : ∀ A, SumOver x A ≤ f A + g A) : x ∈ PolymatroidP f + PolymatroidP g := by
  by_contra hnot
  have hconv : Convex ℝ (PolymatroidP f + PolymatroidP g) := (pm_convex f).add (pm_convex g)
  have hclosed : IsClosed (PolymatroidP f + PolymatroidP g) :=
    ((pm_compact f).add (pm_compact g)).isClosed
  obtain ⟨φ, u, hQ, hux⟩ := geometric_hahn_banach_closed_point hconv hclosed hnot
  set c : Fin n → ℝ := fun i => φ (fun j => if i = j then 1 else 0) with hc
  have hφ : ∀ w : Fin n → ℝ, φ w = ∑ i, w i * c i := by
    intro w
    have := LinearMap.pi_apply_eq_sum_univ (φ : (Fin n → ℝ) →ₗ[ℝ] ℝ) w
    simpa [smul_eq_mul] using this
  set σ := Tuple.sort (fun i => -c i) with hσ
  have hmono := Tuple.monotone_sort (fun i => -c i)
  rw [← hσ] at hmono
  set yf : Fin n → ℝ := fun i => if 0 < c i then pmGv σ f i else 0 with hyf
  set yg : Fin n → ℝ := fun i => if 0 < c i then pmGv σ g i else 0 with hyg
  have memP : ∀ (h : Finset (Fin n) → ℝ), IsPolymatroidRankFunction h →
      (fun i => if 0 < c i then pmGv σ h i else 0) ∈ PolymatroidP h := by
    intro h hh
    refine ⟨fun i => ?_, fun A => ?_⟩
    · simp only [Pi.zero_apply]
      split_ifs
      · exact pmGv_nonneg σ hh i
      · exact le_rfl
    · refine le_trans ?_ (pmGv_feasible σ hh A)
      unfold SumOver
      apply sum_le_sum
      intro i _
      split_ifs
      · exact le_rfl
      · exact pmGv_nonneg σ hh i
  have hin : yf + yg ∈ PolymatroidP f + PolymatroidP g :=
    Set.add_mem_add (memP f hf) (memP g hg)
  have hlt := hQ _ hin
  -- key inequality
  set E : Finset (Fin n) → ℝ := fun A => f A + g A - SumOver x A with hE
  have hxi : ∀ i, SumOver x (pmS σ (pmPos σ i + 1)) - SumOver x (pmS σ (pmPos σ i)) = x i := by
    intro i
    unfold SumOver
    rw [pmS_succ, sum_insert (pm_not_mem σ i)]
    ring
  have hterm : ∀ i, (yf + yg) i * c i - x i * c i ≥
      max (c i) 0 * (E (pmS σ (pmPos σ i + 1)) - E (pmS σ (pmPos σ i))) := by
    intro i
    have hx := hxi i
    simp only [hE, Pi.add_apply, hyf, hyg, pmGv]
    have hxi0 : 0 ≤ x i := hx0 i
    split_ifs with h
    · rw [max_eq_left h.le]
      nlinarith
    · push_neg at h
      rw [max_eq_right h]
      nlinarith
  set D : ℕ → ℝ := fun k => if h : k < n then max (c (σ ⟨k, h⟩)) 0 else 0 with hD
  have hDanti : Antitone D := by
    intro k l hkl
    simp only [hD]
    split_ifs with h1 h2 h2
    · have := hmono (show (⟨k, h2⟩ : Fin n) ≤ ⟨l, h1⟩ from hkl)
      simp only [Function.comp] at this
      exact max_le_max (by linarith) le_rfl
    · omega
    · exact le_max_right _ _
    · exact le_rfl
  have hD0 : ∀ k, 0 ≤ D k := by
    intro k; simp only [hD]; split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  have hsumE : ∑ i : Fin n, max (c i) 0 * (E (pmS σ (pmPos σ i + 1)) - E (pmS σ (pmPos σ i))) =
      ∑ k ∈ range n, D k * (E (pmS σ (k + 1)) - E (pmS σ k)) := by
    rw [← Equiv.sum_comp σ, ← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro k _
    simp only [pmPos_sigma, hD, dif_pos k.isLt]
  have habel := pm_abel D hDanti hD0 (fun k => E (pmS σ k)) (by simp [hE, pmS_zero, hf.1, hg.1, SumOver])
    (fun k => by simp only [hE]; linarith [hx (pmS σ k)]) n
  have hEn : 0 ≤ D n * E (pmS σ n) := mul_nonneg (hD0 n) (by simp only [hE]; linarith [hx (pmS σ n)])
  have hge : ∑ i, x i * c i ≤ ∑ i, (yf + yg) i * c i := by
    have : 0 ≤ ∑ i, ((yf + yg) i * c i - x i * c i) := by
      calc (0:ℝ) ≤ ∑ k ∈ range n, D k * (E (pmS σ (k + 1)) - E (pmS σ k)) := by linarith
        _ = ∑ i : Fin n, max (c i) 0 * (E (pmS σ (pmPos σ i + 1)) - E (pmS σ (pmPos σ i))) := hsumE.symm
        _ ≤ _ := sum_le_sum (fun i _ => hterm i)
    rw [sum_sub_distrib] at this; linarith
  rw [hφ] at hlt hux
  linarith


lemma pm_r_nonneg {n : ℕ} {r : Finset (Fin n) → ℝ} (hr : IsPolymatroidRankFunction r)
    (A : Finset (Fin n)) : 0 ≤ r A := by
  have := hr.2.1 ∅ A (empty_subset A); rw [hr.1] at this; exact this

lemma pm_coef (a1 a2 b1 b2 : ℝ) (h : (a1 - a2) * (b1 - b2) < 0) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) :
    0 ≤ (b2 - b1) / (a1 * b2 - b1 * a2) ∧ 0 ≤ (a1 - a2) / (a1 * b2 - b1 * a2) ∧
      (b2 - b1) / (a1 * b2 - b1 * a2) * a1 + (a1 - a2) / (a1 * b2 - b1 * a2) * b1 = 1 ∧
      (b2 - b1) / (a1 * b2 - b1 * a2) * a2 + (a1 - a2) / (a1 * b2 - b1 * a2) * b2 = 1 := by
  rcases lt_or_gt_of_ne (show a1 - a2 ≠ 0 by intro h0; rw [h0, zero_mul] at h; exact lt_irrefl _ h)
    with h1 | h1
  · have h2 : 0 < b1 - b2 := by
      by_contra hc; push_neg at hc; nlinarith
    have hD : a1 * b2 - b1 * a2 < 0 := by nlinarith
    refine ⟨div_nonneg_of_nonpos (by linarith) hD.le, div_nonneg_of_nonpos (by linarith) hD.le,
      ?_, ?_⟩
    · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_one_iff_eq hD.ne]; ring
    · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_one_iff_eq hD.ne]; ring
  · have h2 : b1 - b2 < 0 := by
      by_contra hc; push_neg at hc; nlinarith
    have hD : 0 < a1 * b2 - b1 * a2 := by nlinarith
    refine ⟨div_nonneg (by linarith) hD.le, div_nonneg (by linarith) hD.le, ?_, ?_⟩
    · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_one_iff_eq hD.ne']; ring
    · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_one_iff_eq hD.ne']; ring

lemma pm_scale {n : ℕ} {r : Finset (Fin n) → ℝ} (hr : IsPolymatroidRankFunction r) {t : ℝ}
    (ht : 0 ≤ t) : IsPolymatroidRankFunction (fun A => t * r A) := by
  refine ⟨by simp [hr.1], fun A B h => mul_le_mul_of_nonneg_left (hr.2.1 A B h) ht, fun A B => ?_⟩
  have := mul_le_mul_of_nonneg_left (hr.2.2 A B) ht
  linarith

lemma pm_unscale {n : ℕ} {r : Finset (Fin n) → ℝ} {t : ℝ} (ht : 0 < t) {y : Fin n → ℝ}
    (hy : y ∈ PolymatroidP (fun A => t * r A)) : t⁻¹ • y ∈ PolymatroidP r := by
  refine ⟨fun i => ?_, fun A => ?_⟩
  · have := hy.1 i
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at *
    exact mul_nonneg (inv_nonneg.mpr ht.le) this
  · have h := hy.2 A
    have e : SumOver (t⁻¹ • y) A = t⁻¹ * SumOver y A := by
      simp [SumOver, mul_sum]
    rw [e, inv_mul_le_iff₀ ht]
    exact h

lemma pm_lambda {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ) (hr1 : IsPolymatroidRankFunction r1)
    (hr2 : IsPolymatroidRankFunction r2) (x : Fin n → ℝ)
    (hmax : ∀ A, SumOver x A ≤ max (r1 A) (r2 A))
    (hpair : ∀ A B : Finset (Fin n), (r1 A - r2 A) * (r1 B - r2 B) < 0 →
          (r2 B - r1 B) / (r1 A * r2 B - r1 B * r2 A) * SumOver x A +
            (r1 A - r2 A) / (r1 A * r2 B - r1 B * r2 A) * SumOver x B ≤ 1) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ∀ A, SumOver x A ≤ t * r1 A + (1 - t) * r2 A := by
  by_cases hT : (univ.filter (fun A : Finset (Fin n) => r2 A < r1 A)).Nonempty
  · obtain ⟨As, hAs, hmaxA⟩ := (univ.filter (fun A : Finset (Fin n) => r2 A < r1 A)).exists_max_image
      (fun A => (SumOver x A - r2 A) / (r1 A - r2 A)) hT
    simp only [mem_filter, mem_univ, true_and] at hAs hmaxA
    set L := (SumOver x As - r2 As) / (r1 As - r2 As) with hL
    have hp : 0 < r1 As - r2 As := by linarith
    have hLp : L * (r1 As - r2 As) = SumOver x As - r2 As := by
      rw [hL]; field_simp
    have hL1 : L ≤ 1 := by
      have := hmax As; rw [max_eq_left hAs.le] at this
      rw [hL, div_le_one hp]; linarith
    refine ⟨max 0 L, le_max_left _ _, max_le zero_le_one hL1, fun A => ?_⟩
    rcases lt_trichotomy (r1 A) (r2 A) with h | h | h
    · -- upper constraint
      have hmA := hmax A; rw [max_eq_right h.le] at hmA
      suffices max 0 L * (r2 A - r1 A) ≤ r2 A - SumOver x A by nlinarith
      rcases le_total L 0 with h0 | h0
      · rw [max_eq_left h0]; linarith
      · rw [max_eq_right h0]
        have hpr := hpair As A (by nlinarith)
        have n1 := pm_r_nonneg hr1 A; have n2 := pm_r_nonneg hr2 As
        have hD : 0 < r1 As * r2 A - r1 A * r2 As := by nlinarith
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_le_one hD] at hpr
        have hq : 0 < r2 A - r1 A := by linarith
        have key : L * (r2 A - r1 A) * (r1 As - r2 As) ≤ (r2 A - SumOver x A) * (r1 As - r2 As) := by
          have : L * (r2 A - r1 A) * (r1 As - r2 As) = (r2 A - r1 A) * (SumOver x As - r2 As) := by
            rw [← hLp]; ring
          rw [this]; nlinarith
        exact le_of_mul_le_mul_right key hp
    · have hmA := hmax A; rw [h, max_self] at hmA
      rw [h]; nlinarith
    · have hLA := hmaxA A h
      have hp' : 0 < r1 A - r2 A := by linarith
      have : SumOver x A - r2 A ≤ L * (r1 A - r2 A) := by
        calc SumOver x A - r2 A = (SumOver x A - r2 A) / (r1 A - r2 A) * (r1 A - r2 A) := by
              field_simp
          _ ≤ L * (r1 A - r2 A) := mul_le_mul_of_nonneg_right hLA hp'.le
      have : L * (r1 A - r2 A) ≤ max 0 L * (r1 A - r2 A) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hp'.le
      nlinarith
  · refine ⟨0, le_rfl, zero_le_one, fun A => ?_⟩
    have h : r1 A ≤ r2 A := by
      by_contra hc; push_neg at hc
      exact hT ⟨A, by simp [hc]⟩
    have := hmax A; rw [max_eq_right h] at this
    linarith

theorem gl_core {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ)
    (hr1 : IsPolymatroidRankFunction r1) (hr2 : IsPolymatroidRankFunction r2) :
    convexHull ℝ (PolymatroidP r1 ∪ PolymatroidP r2) =
      {x : Fin n → ℝ | 0 ≤ x ∧ (∀ A : Finset (Fin n), SumOver x A ≤ max (r1 A) (r2 A)) ∧
        ∀ A B : Finset (Fin n), (r1 A - r2 A) * (r1 B - r2 B) < 0 →
          (r2 B - r1 B) / (r1 A * r2 B - r1 B * r2 A) * SumOver x A +
            (r1 A - r2 A) / (r1 A * r2 B - r1 B * r2 A) * SumOver x B ≤ 1} := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro x (hx | hx)
      · refine ⟨hx.1, fun A => le_trans (hx.2 A) (le_max_left _ _), fun A B h => ?_⟩
        obtain ⟨h1, h2, h3, -⟩ := pm_coef (r1 A) (r2 A) (r1 B) (r2 B) h (pm_r_nonneg hr1 A)
          (pm_r_nonneg hr2 A) (pm_r_nonneg hr1 B) (pm_r_nonneg hr2 B)
        have := mul_le_mul_of_nonneg_left (hx.2 A) h1
        have := mul_le_mul_of_nonneg_left (hx.2 B) h2
        linarith
      · refine ⟨hx.1, fun A => le_trans (hx.2 A) (le_max_right _ _), fun A B h => ?_⟩
        obtain ⟨h1, h2, -, h3⟩ := pm_coef (r1 A) (r2 A) (r1 B) (r2 B) h (pm_r_nonneg hr1 A)
          (pm_r_nonneg hr2 A) (pm_r_nonneg hr1 B) (pm_r_nonneg hr2 B)
        have := mul_le_mul_of_nonneg_left (hx.2 A) h1
        have := mul_le_mul_of_nonneg_left (hx.2 B) h2
        linarith
    · intro y hy z hz a b ha hb hab
      have e : ∀ A, SumOver (a • y + b • z) A = a * SumOver y A + b * SumOver z A := by
        intro A; simp [SumOver, sum_add_distrib, mul_sum]
      refine ⟨?_, fun A => ?_, fun A B h => ?_⟩
      · intro i
        have := hy.1 i; have := hz.1 i
        simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
        positivity
      · rw [e]
        have h1 := mul_le_mul_of_nonneg_left (hy.2.1 A) ha
        have h2 := mul_le_mul_of_nonneg_left (hz.2.1 A) hb
        have : a * max (r1 A) (r2 A) + b * max (r1 A) (r2 A) = max (r1 A) (r2 A) := by
          rw [← add_mul, hab, one_mul]
        linarith
      · rw [e, e]
        have h1 := mul_le_mul_of_nonneg_left (hy.2.2 A B h) ha
        have h2 := mul_le_mul_of_nonneg_left (hz.2.2 A B h) hb
        nlinarith
  · rintro x ⟨hx0, hmax, hpair⟩
    obtain ⟨t, ht0, ht1, ht⟩ := pm_lambda r1 r2 hr1 hr2 x hmax hpair
    rcases eq_or_lt_of_le ht0 with h0 | h0
    · subst h0
      apply subset_convexHull
      right
      exact ⟨hx0, fun A => by have := ht A; simp at this; exact this⟩
    rcases eq_or_lt_of_le ht1 with h1 | h1
    · subst h1
      apply subset_convexHull
      left
      exact ⟨hx0, fun A => by have := ht A; simp at this; exact this⟩
    have hs : 0 < 1 - t := by linarith
    have hsum := pm_sum_thm (fun A => t * r1 A) (fun A => (1 - t) * r2 A) (pm_scale hr1 ht0)
      (pm_scale hr2 hs.le) x hx0 ht
    obtain ⟨y, hy, z, hz, hyz⟩ := hsum
    have hy' := pm_unscale h0 hy
    have hz' := pm_unscale hs hz
    have hmem := (convex_convexHull ℝ (PolymatroidP r1 ∪ PolymatroidP r2))
      (subset_convexHull ℝ _ (Or.inl hy')) (subset_convexHull ℝ _ (Or.inr hz'))
      h0.le hs.le (by ring)
    convert hmem using 1
    rw [smul_smul, smul_smul, mul_inv_cancel₀ h0.ne', mul_inv_cancel₀ hs.ne', one_smul, one_smul]
    exact hyz.symm

end Disjunctive.Polymatroids

open Disjunctive.Polymatroids


theorem solution {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ)
    (hr1 : IsPolymatroidRankFunction r1) (hr2 : IsPolymatroidRankFunction r2) :
    convexHull ℝ (PolymatroidP r1 ∪ PolymatroidP r2) =
      {x : Fin n → ℝ | 0 ≤ x ∧ (∀ A : Finset (Fin n), SumOver x A ≤ max (r1 A) (r2 A)) ∧
        ∀ A B : Finset (Fin n), (r1 A - r2 A) * (r1 B - r2 B) < 0 →
          (r2 B - r1 B) / (r1 A * r2 B - r1 B * r2 A) * SumOver x A +
            (r1 A - r2 A) / (r1 A * r2 B - r1 B * r2 A) * SumOver x B ≤ 1} := by
  exact gl_core r1 r2 hr1 hr2
