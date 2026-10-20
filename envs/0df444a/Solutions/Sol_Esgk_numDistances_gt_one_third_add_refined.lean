-- Prove2me | solution 1 for Esgk.numDistances_gt_one_third_add_refined
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-20T05:18:54.900063+00:00
-- url     : https://prove2.me/submissions/23490203-b417-4193-aa83-ecd1d3aff8d9

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Theorems.Thm_Esgk_apex_sq_dist_mem_of_sq_far
import Theorems.Thm_Esgk_scaled_annular_equidistant_triple_close_pair_sharp
import Theorems.Thm_Esgk_scaled_annular_equidistant_triple_close_pair_small_radius
import Theorems.Thm_Esgk_sum_two_sub_witnesses_le
import Theorems.Thm_Esgk_thin_annulus_sq_of_noFourCocircular
import Definitions.Def_Esgk_PlanarGeneralPosition
import Definitions.Def_Esgk_Foundation
import Definitions.Def_Esgk_DistanceDesign
import Definitions.Def_Esgk_Energy
import Definitions.Def_Esgk_AnnularClosePairCounting
import Definitions.Def_Esgk_AnnulusClusterGeometry
import Definitions.Def_Esgk_ClosePairRowStability
import Definitions.Def_Esgk_EquidistantWitnessCounts
import Definitions.Def_Esgk_FarPairApexCount
import Definitions.Def_Esgk_ConfigurationCentroid
import Definitions.Def_Esgk_ThinAnnulus

namespace Esgk

section

open scoped RealInnerProductSpace
variable {n : ℕ}

private lemma mem_configClosedBall {p : Config n} {i j : Fin n} {t : ℝ} :
    j ∈ ConfigClosedBall p i t ↔ dist (p i) (p j) ≤ t := by
  simp [ConfigClosedBall]

private lemma configClosedBall_disjoint {p : Config n} {i j : Fin n} {t : ℝ}
    (h : 2 * t < dist (p i) (p j)) :
    Disjoint (ConfigClosedBall p i t) (ConfigClosedBall p j t) := by
  rw [Finset.disjoint_left]
  intro k hki hkj
  rw [mem_configClosedBall] at hki hkj
  have htri := dist_triangle (p i) (p k) (p j)
  rw [dist_comm (p k) (p j)] at htri
  linarith

private lemma sum_inner_sub_center_eq_zero {p : Config n} {c : Point}
    (hsum : ∑ i, (p i - c) = 0) (a : Fin n) :
    ∑ q, ⟪p q - c, p a - c⟫ = 0 := by
  rw [← sum_inner, hsum, inner_zero_left]

private lemma norm_sub_center_sub (p q c : Point) : ‖(p - c) - (q - c)‖ = dist p q := by
  rw [sub_sub_sub_cancel_right, dist_eq_norm]

private lemma norm_sub_center_le {p c : Point} {ρ : ℝ} (hρ : 0 < ρ)
    (h : dist p c ^ 2 ≤ ρ ^ 2) : ‖p - c‖ ≤ ρ := by
  rw [← dist_eq_norm]
  nlinarith [dist_nonneg (x := p) (y := c)]

private lemma neg_mul_le_inner {u w : Point} {r s : ℝ} (hu : ‖u‖ ≤ r) (hw : ‖w‖ ≤ s) :
    -(r * s) ≤ ⟪u, w⟫ := by
  have h1 := (abs_le.mp (abs_real_inner_le_norm u w)).1
  have h2 := mul_le_mul hu hw (norm_nonneg w) ((norm_nonneg u).trans hu)
  linarith

private lemma inner_sub_center_ge {c u w : Point} {ρ x s : ℝ}
    (hu : ρ ^ 2 * (1 - x) ≤ dist u c ^ 2) (hw : ρ ^ 2 * (1 - x) ≤ dist w c ^ 2)
    (h : dist u w ≤ s) :
    ρ ^ 2 * (1 - x) - s ^ 2 / 2 ≤ ⟪u - c, w - c⟫ := by
  have hsq := norm_sub_sq_real (u - c) (w - c)
  rw [norm_sub_center_sub, ← dist_eq_norm, ← dist_eq_norm] at hsq
  have hs : dist u w ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ dist_nonneg h 2
  linarith

theorem no_isosceles_far_base_of_heavy_balls {p : Config n} {c : Point} {ρ x τ θ m : ℝ}
    (hsum : ∑ i, (p i - c) = 0) (hρ : 0 < ρ)
    (hlo : ∀ i, ρ ^ 2 * (1 - x) ≤ dist (p i) c ^ 2)
    (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2)
    (hball : ∀ i, m ≤ ((ConfigClosedBall p i τ).card : ℝ))
    (hτ : 0 ≤ τ) (hθ : 4 * τ ≤ θ) (hθρ : (θ + τ) ^ 2 ≤ 2 * (2 - x) * ρ ^ 2)
    (hm : (n : ℝ) * ρ ^ 2 <
      m * ((ρ ^ 2 * (2 - x) - τ ^ 2 / 2) + 2 * (ρ ^ 2 * (2 - x) - (θ + τ) ^ 2 / 2))) :
    ∀ z a b : Fin n, dist (p z) (p a) = dist (p z) (p b) → dist (p z) (p a) ≤ θ →
      θ < dist (p a) (p b) → False := by
  intro z a b hzab hza hab
  have hle : ∀ i, ‖p i - c‖ ≤ ρ := fun i ↦ norm_sub_center_le hρ (hhi i)
  have hab2 : dist (p a) (p b) ≤ 2 * dist (p z) (p a) := by
    have htri := dist_triangle (p a) (p z) (p b)
    rw [dist_comm (p a) (p z), ← hzab] at htri
    linarith
  set f : Fin n → ℝ := fun q ↦ ⟪p q - c, p z - c⟫ + ρ ^ 2 with hf
  set K₁ : ℝ := ρ ^ 2 * (2 - x) - τ ^ 2 / 2 with hK₁
  set K₂ : ℝ := ρ ^ 2 * (2 - x) - (θ + τ) ^ 2 / 2 with hK₂
  have hf0 : ∀ q, 0 ≤ f q := fun q ↦ by
    have := neg_mul_le_inner (hle q) (hle z)
    simp only [hf]; nlinarith
  have hZ : ∀ q ∈ ConfigClosedBall p z τ, K₁ ≤ f q := by
    intro q hq
    rw [mem_configClosedBall, dist_comm] at hq
    have := inner_sub_center_ge (hlo q) (hlo z) hq
    simp only [hf, hK₁]; linarith
  have hA : ∀ q ∈ ConfigClosedBall p a τ, K₂ ≤ f q := by
    intro q hq
    rw [mem_configClosedBall] at hq
    have hqz : dist (p q) (p z) ≤ θ + τ := by
      have htri := dist_triangle (p q) (p a) (p z)
      rw [dist_comm (p q) (p a), dist_comm (p a) (p z)] at htri
      linarith
    have := inner_sub_center_ge (hlo q) (hlo z) hqz
    simp only [hf, hK₂]; linarith
  have hB : ∀ q ∈ ConfigClosedBall p b τ, K₂ ≤ f q := by
    intro q hq
    rw [mem_configClosedBall] at hq
    have hqz : dist (p q) (p z) ≤ θ + τ := by
      have htri := dist_triangle (p q) (p b) (p z)
      rw [dist_comm (p q) (p b), dist_comm (p b) (p z), ← hzab] at htri
      linarith
    have := inner_sub_center_ge (hlo q) (hlo z) hqz
    simp only [hf, hK₂]; linarith
  have hza2 : 2 * τ < dist (p z) (p a) := by linarith
  have hzb2 : 2 * τ < dist (p z) (p b) := by rw [← hzab]; exact hza2
  have hab2' : 2 * τ < dist (p a) (p b) := by linarith
  have hdZA := configClosedBall_disjoint hza2
  have hdZB := configClosedBall_disjoint hzb2
  have hdAB := configClosedBall_disjoint hab2'
  have hsZ := Finset.card_nsmul_le_sum _ f K₁ hZ
  have hsA := Finset.card_nsmul_le_sum _ f K₂ hA
  have hsB := Finset.card_nsmul_le_sum _ f K₂ hB
  rw [nsmul_eq_mul] at hsZ hsA hsB
  have hup := Finset.sum_le_univ_sum_of_nonneg
    (s := ConfigClosedBall p z τ ∪ ConfigClosedBall p a τ ∪ ConfigClosedBall p b τ) hf0
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hdZB, hdAB⟩),
    Finset.sum_union hdZA] at hup
  have htot : ∑ q, f q = n * ρ ^ 2 := by
    simp only [hf, Finset.sum_add_distrib, sum_inner_sub_center_eq_zero hsum z,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, zero_add]
  have hK₂0 : 0 ≤ K₂ := by simp only [hK₂]; linarith
  have hττ : τ ^ 2 ≤ (θ + τ) ^ 2 := pow_le_pow_left₀ hτ (by linarith) 2
  have hK₁0 : 0 ≤ K₁ := by simp only [hK₁]; linarith
  have hmZ := mul_le_mul_of_nonneg_right (hball z) hK₁0
  have hmA := mul_le_mul_of_nonneg_right (hball a) hK₂0
  have hmB := mul_le_mul_of_nonneg_right (hball b) hK₂0
  have hK : m * (K₁ + 2 * K₂) = m * K₁ + m * K₂ + m * K₂ := by ring
  linarith

theorem configClosedBall_card_mul_le {p : Config n} {c : Point} {ρ x θ : ℝ}
    (hsum : ∑ i, (p i - c) = 0) (hρ : 0 < ρ)
    (hlo : ∀ i, ρ ^ 2 * (1 - x) ≤ dist (p i) c ^ 2)
    (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2) (z : Fin n) :
    ((ConfigClosedBall p z θ).card : ℝ) * (ρ ^ 2 * (2 - x) - θ ^ 2 / 2) ≤ (n : ℝ) * ρ ^ 2 := by
  have hle : ∀ i, ‖p i - c‖ ≤ ρ := fun i ↦ norm_sub_center_le hρ (hhi i)
  set f : Fin n → ℝ := fun q ↦ ⟪p q - c, p z - c⟫ + ρ ^ 2 with hf
  have hf0 : ∀ q, 0 ≤ f q := fun q ↦ by
    have := neg_mul_le_inner (hle q) (hle z)
    simp only [hf]; nlinarith
  have hZ : ∀ q ∈ ConfigClosedBall p z θ, ρ ^ 2 * (2 - x) - θ ^ 2 / 2 ≤ f q := by
    intro q hq
    rw [mem_configClosedBall, dist_comm] at hq
    have := inner_sub_center_ge (hlo q) (hlo z) hq
    simp only [hf]; linarith
  have hsZ := Finset.card_nsmul_le_sum _ f _ hZ
  rw [nsmul_eq_mul] at hsZ
  have hup := Finset.sum_le_univ_sum_of_nonneg (s := ConfigClosedBall p z θ) hf0
  have htot : ∑ q, f q = n * ρ ^ 2 := by
    simp only [hf, Finset.sum_add_distrib, sum_inner_sub_center_eq_zero hsum z,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, zero_add]
  linarith

end

section

open EuclideanGeometry

theorem numDistances_eq_numDistancesOrdered_of_injective {n : ℕ} {p : Config n}
    (hp : Function.Injective p) :
    NumDistances p = NumDistancesOrdered p := by
  unfold NumDistances NumDistancesOrdered OrderedDistanceValues distinctDistances Config.toFinset
  congr 1
  apply Finset.Subset.antisymm
  · intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨pair, hpair_mem, hpair_dist⟩ := hr
    rw [Finset.mem_offDiag] at hpair_mem
    obtain ⟨hx_mem, hy_mem, hxy_ne⟩ := hpair_mem
    rw [Finset.mem_image] at hx_mem hy_mem
    obtain ⟨i, _, hpi⟩ := hx_mem
    obtain ⟨j, _, hpj⟩ := hy_mem
    rw [Finset.mem_image]
    refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
      intro (hij : i = j)
      apply hxy_ne
      rw [← hpi, ← hpj, hij]
    · simp only
      rw [hpi, hpj]
      exact hpair_dist
  · intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨ij, hij_mem, hij_dist⟩ := hr
    rw [Finset.mem_filter] at hij_mem
    obtain ⟨_, hij_ne⟩ := hij_mem
    rw [Finset.mem_image]
    refine ⟨(p ij.1, p ij.2), ?_, hij_dist⟩
    rw [Finset.mem_offDiag]
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.mem_image]; exact ⟨ij.1, Finset.mem_univ _, rfl⟩
    · rw [Finset.mem_image]; exact ⟨ij.2, Finset.mem_univ _, rfl⟩
    · intro h; exact hij_ne (hp h)

end

section

open EuclideanGeometry
open scoped BigOperators
variable {n : ℕ} {α : Type*}

theorem distanceDegreeProfile_sum_eq_pred (p : Config n) (i : Fin n) :
    ∑ r ∈ OrderedDistanceValues p, (DistanceOutNeighborsAtValue p i r).card = n - 1 := by
  classical
  let s : Finset (Fin n) := (Finset.univ : Finset (Fin n)).erase i
  let f : Fin n → ℝ := fun j ↦ dist (p i) (p j)
  have hmaps : ∀ j ∈ s, f j ∈ OrderedDistanceValues p := by
    intro j hj
    rw [OrderedDistanceValues, Finset.mem_image]
    refine ⟨(i, j), ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
      by simpa [s, Finset.mem_erase, ne_comm] using hj⟩
  have hfiber' :
      ∑ r ∈ OrderedDistanceValues p, (s.filter (fun j ↦ f j = r)).card = s.card := by
    exact (Finset.card_eq_sum_card_fiberwise hmaps).symm
  have hcard : s.card = n - 1 := by
    simp [s, Finset.card_univ, Fintype.card_fin]
  rw [← hcard, ← hfiber']
  apply Finset.sum_congr rfl
  intro r _hr
  have hfilter : s.filter (fun j ↦ f j = r) = DistanceOutNeighborsAtValue p i r := by
    ext j
    simp [s, f, DistanceOutNeighborsAtValue, ne_comm]
  rw [hfilter]

end

section

open EuclideanGeometry
open scoped BigOperators
variable {n : ℕ}

lemma sum_sqDistance_expand (p : Config n) (i : Fin n) :
    ∑ j, dist (p i) (p j) ^ 2 =
      (n : ℝ) * ‖p i‖ ^ 2 + ∑ j, ‖p j‖ ^ 2 -
        2 * @inner ℝ Point _ (p i) (∑ j, p j) := by
  simp_rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, inner_sub_left,
    inner_sub_right]
  simp_rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← inner_sum, ← sum_inner, real_inner_comm (∑ j, p j) (p i)]
  ring

lemma sum_sqDistance_eq_sum_outDegree_mul (p : Config n) (i : Fin n) :
    ∑ j, dist (p i) (p j) ^ 2 =
      ∑ r ∈ OrderedDistanceValues p,
        ((DistanceOutNeighborsAtValue p i r).card : ℝ) * r ^ 2 := by
  classical
  have hdiag : (∑ j, dist (p i) (p j) ^ 2) =
      ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        dist (p i) (p j) ^ 2 := by
    have h := Finset.sum_erase_add
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun j => dist (p i) (p j) ^ 2) (a := i) (by simp)
    simpa only [dist_self, pow_two, zero_mul, add_zero] using h.symm
  have hmaps : ∀ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      dist (p i) (p j) ∈ OrderedDistanceValues p := by
    intro j hj
    rw [OrderedDistanceValues, Finset.mem_image]
    refine ⟨(i, j), ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
      by simpa [Finset.mem_erase, ne_comm] using hj⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset (Fin n)).erase i)
    (t := OrderedDistanceValues p)
    (g := fun j => dist (p i) (p j)) hmaps (fun r : ℝ => r ^ 2)
  rw [hdiag, ← hfiber]
  apply Finset.sum_congr rfl
  intro r _hr
  have hcard :
      (((Finset.univ : Finset (Fin n)).erase i).filter
        (fun j => dist (p i) (p j) = r)).card =
      (DistanceOutNeighborsAtValue p i r).card := by
    congr 1
    ext j
    simp [DistanceOutNeighborsAtValue, ne_comm]
  rw [← hcard]
  simp [mul_comm]

end

section

open EuclideanGeometry
open scoped BigOperators
variable {α : Type*}

theorem collinear_subset_perpBisector {a b : Point} {s : Set Point}
    [Finite s] (hab : a ≠ b) (hs : s ⊆ (AffineSubspace.perpBisector a b : Set Point)) :
    Collinear ℝ s := by
  classical
  haveI : FiniteDimensional ℝ (vectorSpan ℝ s) :=
    finiteDimensional_vectorSpan_of_finite ℝ (Set.toFinite s)
  rw [collinear_iff_finrank_le_one]
  have hspan_le : vectorSpan ℝ s ≤ (AffineSubspace.perpBisector a b).direction := by
    rw [← direction_affineSpan]
    exact AffineSubspace.direction_le (affineSpan_le.mpr hs)
  have hdir : Module.finrank ℝ (AffineSubspace.perpBisector a b).direction ≤ 1 := by
    rw [AffineSubspace.direction_perpBisector]
    have hv : b -ᵥ a ≠ (0 : Point) := vsub_ne_zero.mpr (Ne.symm hab)
    letI : Fact (Module.finrank ℝ Point = 1 + 1) := ⟨by simp [Point]⟩
    have hfin : Module.finrank ℝ (↥(ℝ ∙ (b -ᵥ a))ᗮ) = 1 := by
      simpa using
        (Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (E := Point) (n := 1) hv)
    rw [hfin]
  exact (Submodule.finrank_mono hspan_le).trans hdir

theorem equidistantWitnesses_card_le_two_of_nonTrilinear {P : Finset Point} {a b : Point}
    (hgp3 : NonTrilinear (P : Set Point)) (hab : a ≠ b) :
    (EquidistantWitnesses P a b).card ≤ 2 := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq (s := EquidistantWitnesses P a b) (n := 3) (by omega)
  have hTP : T ⊆ P := hTsub.trans (Finset.filter_subset _ _)
  rw [Finset.card_eq_three] at hTcard
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := hTcard
  have hxT : x ∈ ({x, y, z} : Finset Point) := by simp
  have hyT : y ∈ ({x, y, z} : Finset Point) := by simp
  have hzT : z ∈ ({x, y, z} : Finset Point) := by simp
  have hxP : x ∈ (P : Set Point) := by exact hTP hxT
  have hyP : y ∈ (P : Set Point) := by exact hTP hyT
  have hzP : z ∈ (P : Set Point) := by exact hTP hzT
  have hxw : dist x a = dist x b := by
    have hx := hTsub hxT
    simpa [EquidistantWitnesses] using (Finset.mem_filter.mp hx).2
  have hyw : dist y a = dist y b := by
    have hy := hTsub hyT
    simpa [EquidistantWitnesses] using (Finset.mem_filter.mp hy).2
  have hzw : dist z a = dist z b := by
    have hz := hTsub hzT
    simpa [EquidistantWitnesses] using (Finset.mem_filter.mp hz).2
  have hcol : Collinear ℝ ({x, y, z} : Set Point) := by
    apply collinear_subset_perpBisector (a := a) (b := b) hab
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · exact AffineSubspace.mem_perpBisector_iff_dist_eq.mpr hxw
    · exact AffineSubspace.mem_perpBisector_iff_dist_eq.mpr hyw
    · exact AffineSubspace.mem_perpBisector_iff_dist_eq.mpr hzw
  exact (hgp3 hxP hyP hzP hxy hyz hxz) hcol

lemma indexedEquidistantWitnesses_card_le_pointWitnesses
    {n : ℕ} {p : Config n} (hp : Function.Injective p) (i j : Fin n) :
    (IndexedEquidistantWitnesses p i j).card ≤
      (EquidistantWitnesses (Config.toFinset p) (p i) (p j)).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun x => p x) ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, IndexedEquidistantWitnesses,
      Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_coe, EquidistantWitnesses, Finset.mem_filter]
    exact ⟨Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩, hx⟩
  · intro a _ha b _hb hab
    exact hp hab

theorem indexedEquidistantWitnesses_card_le_two_of_nonTrilinear
    {n : ℕ} {p : Config n} (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point)) {i j : Fin n}
    (hij : i ≠ j) :
    (IndexedEquidistantWitnesses p i j).card ≤ 2 :=
  (indexedEquidistantWitnesses_card_le_pointWitnesses hp i j).trans
    (equidistantWitnesses_card_le_two_of_nonTrilinear hgp3 (hp.ne hij))

end

section

open EuclideanGeometry
variable {n : ℕ}

private theorem card_filter_product_add_two_le_of_nonEdge {α : Type*} [DecidableEq α]
    (S : Finset α) (R : α → α → Prop) [DecidableRel R]
    (hsymm : ∀ a b, R a b → R b a) {u v : α} (hu : u ∈ S) (hv : v ∈ S)
    (huv : u ≠ v) (hR : ¬R u v)
    (hoff : (S ×ˢ S).filter (fun ab ↦ R ab.1 ab.2) ⊆ S.offDiag) :
    ((S ×ˢ S).filter (fun ab ↦ R ab.1 ab.2)).card + 2 ≤ S.offDiag.card := by
  have hmem1 : (u, v) ∈ S.offDiag := Finset.mem_offDiag.mpr ⟨hu, hv, huv⟩
  have hmem2 : (v, u) ∈ S.offDiag.erase (u, v) := by
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_offDiag.mpr ⟨hv, hu, huv.symm⟩⟩
    intro h
    exact huv (Prod.mk.inj h).2
  have hsub : (S ×ˢ S).filter (fun ab ↦ R ab.1 ab.2) ⊆
      (S.offDiag.erase (u, v)).erase (v, u) := by
    intro ab hab
    have hR' : R ab.1 ab.2 := (Finset.mem_filter.mp hab).2
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hoff hab⟩⟩
    · rintro rfl
      exact hR (hsymm _ _ hR')
    · rintro rfl
      exact hR hR'
  have h1 := Finset.card_erase_add_one hmem1
  have h2 := Finset.card_erase_add_one hmem2
  have h3 := Finset.card_le_card hsub
  omega

theorem three_mul_card_filter_product_le_of_triangleFree {α : Type*} [DecidableEq α]
    (S : Finset α) (R : α → α → Prop) [DecidableRel R]
    (hirr : ∀ a, ¬R a a) (hsymm : ∀ a b, R a b → R b a) (hS : S.card ≤ 3)
    (htri : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, R a b → R b c → R a c → False) :
    3 * ((S ×ˢ S).filter (fun ab ↦ R ab.1 ab.2)).card ≤ 4 * S.card := by
  have hoff : (S ×ˢ S).filter (fun ab ↦ R ab.1 ab.2) ⊆ S.offDiag := by
    intro ab hab
    rw [Finset.mem_filter, Finset.mem_product] at hab
    refine Finset.mem_offDiag.mpr ⟨hab.1.1, hab.1.2, fun h ↦ hirr ab.2 ?_⟩
    have hR := hab.2
    rwa [h] at hR
  have hle := Finset.card_le_card hoff
  rw [Finset.offDiag_card] at hle
  rcases (by omega : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ S.card = 3) with h | h | h | h
  · rw [h] at hle ⊢
    omega
  · rw [h] at hle ⊢
    omega
  · rw [h] at hle ⊢
    omega
  · obtain ⟨a, b, c, hab, hac, hbc, hSabc⟩ := Finset.card_eq_three.mp h
    have ha : a ∈ S := by rw [hSabc]; simp
    have hb : b ∈ S := by rw [hSabc]; simp
    have hc : c ∈ S := by rw [hSabc]; simp
    have hkey : ((S ×ˢ S).filter (fun ab ↦ R ab.1 ab.2)).card + 2 ≤ S.offDiag.card := by
      by_cases h1 : R a b
      · by_cases h2 : R b c
        · by_cases h3 : R a c
          · exact (htri a ha b hb c hc h1 h2 h3).elim
          · exact card_filter_product_add_two_le_of_nonEdge S R hsymm ha hc hac h3 hoff
        · exact card_filter_product_add_two_le_of_nonEdge S R hsymm hb hc hbc h2 hoff
      · exact card_filter_product_add_two_le_of_nonEdge S R hsymm ha hb hab h1 hoff
    rw [Finset.offDiag_card, h] at hkey
    rw [h]
    omega

private theorem ne_of_lt_dist {p : Config n} {s : ℝ} (hs : 0 ≤ s) {a b : Fin n}
    (h : s < dist (p a) (p b)) : a ≠ b := by
  rintro rfl
  rw [dist_self] at h
  linarith

theorem farOrderedPairs_card_eq_sum {p : Config n} {s : ℝ} (hs : 0 ≤ s) :
    (FarOrderedPairs p s).card =
      ∑ a, ((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ s < dist (p a) (p q))).card := by
  have heq : FarOrderedPairs p s = (Finset.univ : Finset (Fin n × Fin n)).filter
      (fun ab ↦ s < dist (p ab.1) (p ab.2)) := by
    ext ab
    simp only [FarOrderedPairs, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ,
      true_and]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨ne_of_lt_dist hs h, h⟩⟩
  rw [heq, Finset.card_filter, Fintype.sum_prod_type]
  simp only [Finset.card_filter]

end

section

open EuclideanGeometry
variable {n : ℕ}

private theorem ne_of_radius_pred {p : Config n} {G : ℝ → Prop} (hG0 : ¬G 0)
    {z q : Fin n} (h : G (dist (p z) (p q))) : z ≠ q := by
  rintro rfl
  rw [dist_self] at h
  exact hG0 h

private theorem dist_mem_orderedDistanceValues_of_ne {p : Config n} {a b : Fin n}
    (h : a ≠ b) : dist (p a) (p b) ∈ OrderedDistanceValues p := by
  rw [OrderedDistanceValues, Finset.mem_image]
  exact ⟨(a, b), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, h⟩, rfl⟩

theorem three_mul_apexPairs_card_le {p : Config n}
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    (R : Fin n → Fin n → Prop) [DecidableRel R]
    (hirr : ∀ a, ¬R a a) (hsymm : ∀ a b, R a b → R b a)
    (G : ℝ → Prop) [DecidablePred G] (hG0 : ¬G 0)
    (hrad : ∀ z a b, R a b → dist (p z) (p a) = dist (p z) (p b) → G (dist (p z) (p a)))
    (htri : ∀ z a b c, dist (p z) (p a) = dist (p z) (p b) →
      dist (p z) (p a) = dist (p z) (p c) → G (dist (p z) (p a)) →
      R a b → R b c → R a c → False)
    (z : Fin n) :
    3 * ((Finset.univ : Finset (Fin n)).offDiag.filter
        (fun ab ↦ R ab.1 ab.2 ∧ dist (p z) (p ab.1) = dist (p z) (p ab.2))).card ≤
      4 * ((Finset.univ : Finset (Fin n)).filter (fun q ↦ G (dist (p z) (p q)))).card := by
  set A := (Finset.univ : Finset (Fin n)).offDiag.filter
    (fun ab ↦ R ab.1 ab.2 ∧ dist (p z) (p ab.1) = dist (p z) (p ab.2)) with hA
  set T := (Finset.univ : Finset (Fin n)).filter (fun q ↦ G (dist (p z) (p q))) with hT
  have hmemT : ∀ q, q ∈ T ↔ G (dist (p z) (p q)) := by
    intro q
    rw [hT, Finset.mem_filter]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩
  have hmemA : ∀ ab ∈ A, ab.1 ∈ T ∧ ab.2 ∈ T ∧ R ab.1 ab.2 ∧
      dist (p z) (p ab.1) = dist (p z) (p ab.2) := by
    intro ab hab
    rw [hA, Finset.mem_filter] at hab
    obtain ⟨_, hR, heq⟩ := hab
    have hza : G (dist (p z) (p ab.1)) := hrad z ab.1 ab.2 hR heq
    exact ⟨(hmemT _).mpr hza, (hmemT _).mpr (heq ▸ hza), hR, heq⟩
  have hmapsA : ∀ ab ∈ A, dist (p z) (p ab.1) ∈ OrderedDistanceValues p := fun ab hab ↦
    dist_mem_orderedDistanceValues_of_ne
      (ne_of_radius_pred hG0 ((hmemT _).mp (hmemA ab hab).1))
  have hmapsT : ∀ q ∈ T, dist (p z) (p q) ∈ OrderedDistanceValues p := fun q hq ↦
    dist_mem_orderedDistanceValues_of_ne (ne_of_radius_pred hG0 ((hmemT _).mp hq))
  rw [Finset.card_eq_sum_card_fiberwise hmapsA, Finset.card_eq_sum_card_fiberwise hmapsT,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ ↦ ?_
  set U := T.filter (fun q ↦ dist (p z) (p q) = r) with hU
  have hmemU : ∀ q, q ∈ U ↔ G (dist (p z) (p q)) ∧ dist (p z) (p q) = r := by
    intro q
    rw [hU, Finset.mem_filter, hmemT]
  calc 3 * (A.filter (fun ab ↦ dist (p z) (p ab.1) = r)).card
      ≤ 3 * ((U ×ˢ U).filter (fun ab ↦ R ab.1 ab.2)).card := by
        apply Nat.mul_le_mul_left
        apply Finset.card_le_card
        intro ab hab
        rw [Finset.mem_filter] at hab
        obtain ⟨h1, h2, hR, heq⟩ := hmemA ab hab.1
        rw [Finset.mem_filter, Finset.mem_product, hmemU, hmemU]
        exact ⟨⟨⟨(hmemT _).mp h1, hab.2⟩, (hmemT _).mp h2, heq ▸ hab.2⟩, hR⟩
    _ ≤ 4 * U.card := by
        apply three_mul_card_filter_product_le_of_triangleFree U R hirr hsymm
        · refine (Finset.card_le_card ?_).trans (hcap z r)
          intro q hq
          rw [hmemU] at hq
          rw [DistanceOutNeighborsAtValue, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, ne_of_radius_pred hG0 hq.1, hq.2⟩
        · intro a ha b hb c hc hab hbc hac
          rw [hmemU] at ha hb hc
          exact htri z a b c (ha.2.trans hb.2.symm) (ha.2.trans hc.2.symm) ha.1 hab hbc hac

private theorem sum_witness_card_eq_sum_apex_card (p : Config n)
    (Φ : Finset (Fin n × Fin n)) :
    ∑ ab ∈ Φ, (IndexedEquidistantWitnesses p ab.1 ab.2).card =
      ∑ z, (Φ.filter (fun ab ↦ dist (p z) (p ab.1) = dist (p z) (p ab.2))).card := by
  simp only [IndexedEquidistantWitnesses, Finset.card_filter]
  exact Finset.sum_comm

theorem six_mul_card_pairs_le_of_apex {p : Config n} (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    (R : Fin n → Fin n → Prop) [DecidableRel R]
    (hirr : ∀ a, ¬R a a) (hsymm : ∀ a b, R a b → R b a)
    (G : ℝ → Prop) [DecidablePred G] (hG0 : ¬G 0)
    (hrad : ∀ z a b, R a b → dist (p z) (p a) = dist (p z) (p b) → G (dist (p z) (p a)))
    (htri : ∀ z a b c, dist (p z) (p a) = dist (p z) (p b) →
      dist (p z) (p a) = dist (p z) (p c) → G (dist (p z) (p a)) →
      R a b → R b c → R a c → False) :
    6 * ((((Finset.univ : Finset (Fin n)).offDiag.filter (fun ab ↦ R ab.1 ab.2)).card : ℝ)) ≤
      6 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) +
        4 * ∑ z, (((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ G (dist (p z) (p q)))).card : ℝ) := by
  have hsub : (Finset.univ : Finset (Fin n)).offDiag.filter (fun ab ↦ R ab.1 ab.2) ⊆
      (Finset.univ : Finset (Fin n)).offDiag :=
    Finset.filter_subset _ _
  have hdef := sum_two_sub_witnesses_le hp hgp3 hsub
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hdef
  have hnat : 3 * ∑ ab ∈ (Finset.univ : Finset (Fin n)).offDiag.filter
        (fun ab ↦ R ab.1 ab.2), (IndexedEquidistantWitnesses p ab.1 ab.2).card ≤
      4 * ∑ z, ((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ G (dist (p z) (p q)))).card := by
    rw [sum_witness_card_eq_sum_apex_card, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ ↦ ?_
    rw [Finset.filter_filter]
    exact three_mul_apexPairs_card_le hcap R hirr hsymm G hG0 hrad htri z
  have hreal : 3 * ∑ ab ∈ (Finset.univ : Finset (Fin n)).offDiag.filter
        (fun ab ↦ R ab.1 ab.2), ((IndexedEquidistantWitnesses p ab.1 ab.2).card : ℝ) ≤
      4 * ∑ z, (((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ G (dist (p z) (p q)))).card : ℝ) := by
    exact_mod_cast hnat
  linarith

theorem farOrderedPairs_card_le_of_apex {p : Config n} (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    {s : ℝ} (hs : 0 ≤ s)
    (hapex : ∀ z a b, s < dist (p a) (p b) → dist (p z) (p a) = dist (p z) (p b) →
      s < dist (p z) (p a))
    (hcirc : ∀ z a b c, dist (p z) (p a) = dist (p z) (p b) →
      dist (p z) (p a) = dist (p z) (p c) → s < dist (p z) (p a) →
      s < dist (p a) (p b) → s < dist (p b) (p c) → s < dist (p a) (p c) → False) :
    ((FarOrderedPairs p s).card : ℝ) ≤
      3 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) := by
  have hirr : ∀ a : Fin n, ¬s < dist (p a) (p a) := by
    intro a
    rw [dist_self]
    exact not_lt.mpr hs
  have hsymm : ∀ a b : Fin n, s < dist (p a) (p b) → s < dist (p b) (p a) := by
    intro a b h
    rwa [dist_comm]
  have h : 6 * ((FarOrderedPairs p s).card : ℝ) ≤
      6 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) +
        4 * ∑ z, (((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ s < dist (p z) (p q))).card : ℝ) :=
    six_mul_card_pairs_le_of_apex hp hgp3 hcap (fun a b ↦ s < dist (p a) (p b)) hirr hsymm
      (fun r ↦ s < r) (not_lt.mpr hs) hapex hcirc
  have hrow : ∑ z, (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ s < dist (p z) (p q))).card : ℝ) = ((FarOrderedPairs p s).card : ℝ) := by
    rw [farOrderedPairs_card_eq_sum hs, Nat.cast_sum]
  rw [hrow] at h
  linarith

end

section

open EuclideanGeometry
open scoped BigOperators
variable {n : ℕ}

theorem fixedDistance_card_le_three_of_noFourCocircular {A : Config n}
    (hgp4 : ∀ T ⊆ Config.toFinset A, T.card = 4 → ¬Cospherical (SetLike.coe T))
    (c : Point) (r : ℝ) :
    ((Config.toFinset A).filter (fun x ↦ dist x c = r)).card ≤ 3 := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq
      (s := (Config.toFinset A).filter (fun x ↦ dist x c = r))
      (n := 4) (by omega)
  have hTA : T ⊆ Config.toFinset A := hTsub.trans (Finset.filter_subset _ _)
  have hcos : Cospherical (SetLike.coe T) := by
    refine ⟨c, r, ?_⟩
    intro x hx
    have hxT : x ∈ T := by simpa using hx
    exact (Finset.mem_filter.mp (hTsub hxT)).2
  exact hgp4 T hTA hTcard hcos

theorem distanceOutNeighborsAtValue_card_le_three_of_noFourCocircular
    {A : Config n} (hA : Function.Injective A)
    (hgp4 : ∀ T ⊆ Config.toFinset A, T.card = 4 → ¬Cospherical (SetLike.coe T))
    (i : Fin n) (r : ℝ) :
    (DistanceOutNeighborsAtValue A i r).card ≤ 3 := by
  classical
  let S : Finset Point := (Config.toFinset A).filter (fun x ↦ dist x (A i) = r)
  have hcard_le : (DistanceOutNeighborsAtValue A i r).card ≤ S.card := by
    refine Finset.card_le_card_of_injOn (fun j ↦ A j) ?_ ?_
    · intro j hj
      simp only [Finset.mem_coe, DistanceOutNeighborsAtValue, Finset.mem_filter,
        Finset.mem_univ, true_and] at hj
      obtain ⟨_hne, hdist⟩ := hj
      change A j ∈ (Config.toFinset A).filter (fun x ↦ dist x (A i) = r)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩,
        by simpa [dist_comm] using hdist⟩
    · intro _a _ha _b _hb hab
      exact hA hab
  exact hcard_le.trans (fixedDistance_card_le_three_of_noFourCocircular hgp4 (A i) r)

end

section

open EuclideanGeometry
open scoped BigOperators
variable {n : ℕ}

lemma sum_sub_configCentroid (p : Config n) (hn : 0 < n) :
    ∑ i, (p i - configCentroid p) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, configCentroid, smul_smul,
    mul_inv_cancel₀ hn0, one_smul, sub_self]

lemma sum_sqDistance_eq_centroid (p : Config n) (hn : 0 < n) (i : Fin n) :
    ∑ j, dist (p i) (p j) ^ 2 =
      (n : ℝ) * dist (p i) (configCentroid p) ^ 2 + centroidSquaredMass p := by
  have h := sum_sqDistance_expand (fun j ↦ p j - configCentroid p) i
  rw [sum_sub_configCentroid p hn, inner_zero_right, mul_zero, sub_zero] at h
  simpa only [dist_sub_right, ← dist_eq_norm, centroidSquaredMass] using h

lemma sum_distanceDegreeDeficit (p : Config n) (hn : 0 < n) (i : Fin n) :
    ∑ r ∈ OrderedDistanceValues p,
      (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) =
        3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1 := by
  have hdeg := distanceDegreeProfile_sum_eq_pred p i
  have hdegR :
      (∑ r ∈ OrderedDistanceValues p,
        ((DistanceOutNeighborsAtValue p i r).card : ℝ)) = (n : ℝ) - 1 := by
    rw [← Nat.cast_sum, hdeg, Nat.cast_sub (by omega)]
    norm_num
  rw [Finset.sum_sub_distrib, hdegR]
  simp only [Finset.sum_const, nsmul_eq_mul, NumDistancesOrdered]
  ring

lemma sum_weighted_distanceDegreeDeficit (p : Config n) (i : Fin n) :
    ∑ r ∈ OrderedDistanceValues p,
      (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) * r ^ 2 =
        3 * (∑ r ∈ OrderedDistanceValues p, r ^ 2) -
          ∑ j, dist (p i) (p j) ^ 2 := by
  rw [sum_sqDistance_eq_sum_outDegree_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  ring

lemma distanceAnnulusRadiusSq_bounds {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) :
    0 ≤ distanceAnnulusRadiusSq p ∧
      ∀ i, dist (p i) (configCentroid p) ^ 2 ≤ distanceAnnulusRadiusSq p := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hupper (i : Fin n) :
      dist (p i) (configCentroid p) ^ 2 ≤ distanceAnnulusRadiusSq p := by
    have hdef : 0 ≤ ∑ r ∈ OrderedDistanceValues p,
        (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) * r ^ 2 := by
      apply Finset.sum_nonneg
      intro r _hr
      have hc : ((DistanceOutNeighborsAtValue p i r).card : ℝ) ≤ 3 :=
        by exact_mod_cast hcap i r
      exact mul_nonneg (by linarith) (sq_nonneg r)
    rw [sum_weighted_distanceDegreeDeficit, sum_sqDistance_eq_centroid p hn i] at hdef
    unfold distanceAnnulusRadiusSq
    apply (le_div_iff₀ hnR).mpr
    nlinarith
  let i0 : Fin n := ⟨0, hn⟩
  exact ⟨(sq_nonneg _).trans (hupper i0), hupper⟩

lemma distanceAnnulusRadius_bounds {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) :
    0 ≤ distanceAnnulusRadius p ∧
      distanceAnnulusRadius p ^ 2 = distanceAnnulusRadiusSq p ∧
        ∀ i, dist (p i) (configCentroid p) ≤ distanceAnnulusRadius p := by
  obtain ⟨hR, hupper⟩ := distanceAnnulusRadiusSq_bounds hn hcap
  have hρ : 0 ≤ distanceAnnulusRadius p := Real.sqrt_nonneg _
  have hsq : distanceAnnulusRadius p ^ 2 = distanceAnnulusRadiusSq p :=
    Real.sq_sqrt hR
  refine ⟨hρ, hsq, ?_⟩
  intro i
  have hd := dist_nonneg (x := p i) (y := configCentroid p)
  have hi := hupper i
  nlinarith

theorem distanceAnnulusRadius_pos {p : Config n} (hp : Function.Injective p)
    (hn : 2 ≤ n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) :
    0 < distanceAnnulusRadius p := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have hi : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    norm_num [i0, i1] at this
  have hdist : 0 < dist (p i0) (p i1) :=
    dist_pos.mpr (fun h ↦ hi (hp h))
  have hb := (distanceAnnulusRadius_bounds (by omega : 0 < n) hcap).2.2
  have ht := dist_triangle (p i0) (configCentroid p) (p i1)
  rw [dist_comm (configCentroid p) (p i1)] at ht
  have h0 := hb i0
  have h1 := hb i1
  linarith

end

section

open EuclideanGeometry
open scoped BigOperators
variable {n : ℕ}

theorem orderedClosePairs_card (p : Config n) (t : ℝ) :
    (OrderedClosePairs p t).card = 2 * (IncreasingClosePairs p t).card := by
  classical
  let s := OrderedClosePairs p t
  have hs : s.filter (fun ij ↦ ¬ij.1 < ij.2) =
      (IncreasingClosePairs p t).image Prod.swap := by
    ext ij
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hij, hlt⟩
      have hne := (Finset.mem_offDiag.mp (Finset.mem_filter.mp hij).1).2.2
      refine ⟨ij.swap, ?_, Prod.swap_swap ij⟩
      simp only [IncreasingClosePairs, OrderedClosePairs, Finset.mem_filter,
        Finset.mem_offDiag, Finset.mem_univ, true_and, Prod.fst_swap, Prod.snd_swap]
      exact ⟨⟨hne.symm, by simpa [dist_comm] using (Finset.mem_filter.mp hij).2⟩,
        lt_of_le_of_ne (le_of_not_gt hlt) hne.symm⟩
    · rintro ⟨ji, hji, rfl⟩
      have hlt := (Finset.mem_filter.mp hji).2
      have hji' := (Finset.mem_filter.mp hji).1
      constructor
      · simpa [s, OrderedClosePairs, Finset.mem_offDiag, ne_comm, dist_comm] using hji'
      · exact not_lt_of_gt hlt
  have hc := Finset.card_filter_add_card_filter_not (s := s) (p := fun ij ↦ ij.1 < ij.2)
  rw [hs, Finset.card_image_of_injective _ Prod.swap_injective] at hc
  change (IncreasingClosePairs p t).card + (IncreasingClosePairs p t).card =
    (OrderedClosePairs p t).card at hc
  omega

theorem saturatedDistanceIncidences_lower_bound {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) :
    (n : ℝ) * ((n : ℝ) - 1 - 2 * (NumDistancesOrdered p : ℝ)) ≤
      ((SaturatedDistanceIncidences p).card : ℝ) := by
  classical
  have hrow (i : Fin n) :
      (n : ℝ) - 1 - 2 * (NumDistancesOrdered p : ℝ) ≤
        (((OrderedDistanceValues p).filter
          (fun r ↦ (DistanceOutNeighborsAtValue p i r).card = 3)).card : ℝ) := by
    have hd := sum_distanceDegreeDeficit p hn i
    have hcount :
        (∑ r ∈ OrderedDistanceValues p,
          (if (DistanceOutNeighborsAtValue p i r).card = 3 then (0 : ℝ) else 1)) ≤
        ∑ r ∈ OrderedDistanceValues p,
          (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) := by
      apply Finset.sum_le_sum
      intro r _hr
      split_ifs with h
      · rw [h]; norm_num
      · have hc : (DistanceOutNeighborsAtValue p i r).card ≤ 2 := by
          have := hcap i r
          omega
        have hcR : ((DistanceOutNeighborsAtValue p i r).card : ℝ) ≤ 2 := by
          exact_mod_cast hc
        linarith
    have hsum :
        (∑ r ∈ OrderedDistanceValues p,
          (if (DistanceOutNeighborsAtValue p i r).card = 3 then (0 : ℝ) else 1)) =
        (((OrderedDistanceValues p).filter
          (fun r ↦ ¬(DistanceOutNeighborsAtValue p i r).card = 3)).card : ℝ) := by
      simp [Finset.sum_ite, Finset.sum_const]
    rw [hsum, hd] at hcount
    have hc := Finset.card_filter_add_card_filter_not
      (s := OrderedDistanceValues p)
      (p := fun r ↦ (DistanceOutNeighborsAtValue p i r).card = 3)
    have hcR := congrArg (fun k : ℕ ↦ (k : ℝ)) hc
    simp only [Nat.cast_add] at hcR
    change _ + _ = (NumDistancesOrdered p : ℝ) at hcR
    linarith
  have hcard : (SaturatedDistanceIncidences p).card =
      ∑ i, ((OrderedDistanceValues p).filter
        (fun r ↦ (DistanceOutNeighborsAtValue p i r).card = 3)).card := by
    unfold SaturatedDistanceIncidences
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.product_eq_sprod, Finset.sum_product]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) ↦ hrow i)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Nat.cast_sum, ← hcard] using h

end

section

open EuclideanGeometry
variable {n : ℕ}

theorem orderedClosePairs_card_eq_sum_row (p : Config n) (T : ℝ) :
    (OrderedClosePairs p T).card = ∑ i, (ClosePairRow p i T).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (fun _ _ ↦ Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro i _hi
  refine Finset.card_bij (fun ij _ ↦ ij.2) ?_ ?_ ?_
  · intro ij hij
    simp only [OrderedClosePairs, Finset.mem_filter, Finset.mem_offDiag,
      Finset.mem_univ, true_and] at hij
    simp only [ClosePairRow, Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨⟨hne, hd⟩, rfl⟩ := hij
    exact ⟨hne, hd⟩
  · intro a ha b hb hab
    simp only [Finset.mem_filter] at ha hb
    exact Prod.ext (ha.2.trans hb.2.symm) hab
  · intro j hj
    simp only [ClosePairRow, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨(i, j), ?_, rfl⟩
    simpa [OrderedClosePairs, Finset.mem_offDiag] using hj

theorem closePairRow_card_eq_sum (p : Config n) (i : Fin n) (T : ℝ) :
    (ClosePairRow p i T).card =
      ∑ r ∈ (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ T),
        (DistanceOutNeighborsAtValue p i r).card := by
  classical
  have hmaps : ∀ j ∈ ClosePairRow p i T, dist (p i) (p j) ∈
      (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ T) := by
    intro j hj
    simp only [ClosePairRow, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine Finset.mem_filter.mpr ⟨?_, hj.2⟩
    rw [OrderedDistanceValues, Finset.mem_image]
    exact ⟨(i, j), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hj.1⟩, rfl⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro r hr
  have hrT := (Finset.mem_filter.mp hr).2
  congr 1
  ext j
  simp only [ClosePairRow, DistanceOutNeighborsAtValue, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hne, _⟩, hd⟩
    exact ⟨hne, hd⟩
  · rintro ⟨hne, hd⟩
    exact ⟨⟨hne, by rw [hd]; exact hrT⟩, hd⟩

theorem closePairRow_card_stability {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    (i j : Fin n) (T : ℝ) :
    ((ClosePairRow p i T).card : ℝ) -
        (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) ≤
      ((ClosePairRow p j T).card : ℝ) := by
  set RT := (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ T) with hRT
  have hi : ((ClosePairRow p i T).card : ℝ) ≤ 3 * (RT.card : ℝ) := by
    rw [closePairRow_card_eq_sum]
    push_cast
    calc ∑ r ∈ RT, ((DistanceOutNeighborsAtValue p i r).card : ℝ) ≤
          ∑ _r ∈ RT, (3 : ℝ) :=
          Finset.sum_le_sum (fun r _ ↦ by exact_mod_cast hcap i r)
      _ = 3 * (RT.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hdef : ∑ r ∈ RT, (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) ≤
      3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1 := by
    rw [← sum_distanceDegreeDeficit p hn j]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro r _ _
    have hc : ((DistanceOutNeighborsAtValue p j r).card : ℝ) ≤ 3 := by
      exact_mod_cast hcap j r
    linarith
  have hj : ((ClosePairRow p j T).card : ℝ) = 3 * (RT.card : ℝ) -
      ∑ r ∈ RT, (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) := by
    rw [closePairRow_card_eq_sum]
    push_cast
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  linarith

end

section

open EuclideanGeometry
variable {n : ℕ}

theorem card_le_orderedClosePairs_of_pairs {p : Config n} {t : ℝ}
    (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (S : Finset (Fin n × ℝ))
    (hpair : ∀ ir ∈ S, ∃ a b, a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧ a < b ∧ dist (p a) (p b) ^ 2 ≤ t) :
    S.card ≤ (OrderedClosePairs p t).card := by
  classical
  have hex (ir : Fin n × ℝ) (hir : ir ∈ S) :
      ∃ ab : Fin n × Fin n,
        ab.1 ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
        ab.2 ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
        ab ∈ IncreasingClosePairs p t := by
    obtain ⟨a, b, ha, hb, hab, hclose⟩ := hpair ir hir
    exact ⟨(a, b), ha, hb, by
      simp [IncreasingClosePairs, OrderedClosePairs, Finset.mem_offDiag, hab, hab.ne, hclose]⟩
  let f : Fin n × ℝ → Fin n × Fin n := fun ir ↦
    if hir : ir ∈ S then Classical.choose (hex ir hir) else (ir.1, ir.1)
  have hf (ir : Fin n × ℝ) (hir : ir ∈ S) :
      (f ir).1 ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      (f ir).2 ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      f ir ∈ IncreasingClosePairs p t := by
    simpa only [f, dif_pos hir] using Classical.choose_spec (hex ir hir)
  have hbound : S.card ≤ 2 * (IncreasingClosePairs p t).card := by
    apply Finset.card_le_mul_card_image_of_maps_to (fun ir hir ↦ (hf ir hir).2.2) 2
    intro ab hab
    have hne : ab.1 ≠ ab.2 := (Finset.mem_filter.mp hab).2.ne
    apply le_trans _ (indexedEquidistantWitnesses_card_le_two_of_nonTrilinear hp hgp3 hne)
    apply Finset.card_le_card_of_injOn (fun ir : Fin n × ℝ ↦ ir.1)
    · intro ir hir
      obtain ⟨hirS, hirf⟩ := Finset.mem_filter.mp hir
      obtain ⟨ha, hb, _⟩ := hf ir hirS
      rw [hirf] at ha hb
      have hda := (Finset.mem_filter.mp ha).2.2
      have hdb := (Finset.mem_filter.mp hb).2.2
      simp only [Finset.mem_coe, IndexedEquidistantWitnesses, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hda.trans hdb.symm
    · intro ir hir jr hjr heq
      obtain ⟨hirS, hirf⟩ := Finset.mem_filter.mp hir
      obtain ⟨hjrS, hjrf⟩ := Finset.mem_filter.mp hjr
      have ha := (hf ir hirS).1
      have hb := (hf jr hjrS).1
      rw [hirf] at ha
      rw [hjrf] at hb
      have hda := (Finset.mem_filter.mp ha).2.2
      have hdb := (Finset.mem_filter.mp hb).2.2
      change ir.1 = jr.1 at heq
      apply Prod.ext heq
      rw [heq] at hda
      exact hda.symm.trans hdb
  simpa only [orderedClosePairs_card] using hbound

theorem saturatedDistanceIncidences_filter_lower_bound {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) (T : ℝ) :
    (n : ℝ) * ((((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ T)).card : ℝ) -
        (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1)) ≤
      (((SaturatedDistanceIncidences p).filter (fun ir ↦ ir.2 ^ 2 ≤ T)).card : ℝ) := by
  classical
  set RT := (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ T) with hRT
  have hrow (i : Fin n) :
      (RT.card : ℝ) - (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) ≤
        ((RT.filter (fun r ↦ (DistanceOutNeighborsAtValue p i r).card = 3)).card : ℝ) := by
    have hdef : ∑ r ∈ RT, (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) ≤
        3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1 := by
      rw [← sum_distanceDegreeDeficit p hn i]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro r _ _
      have hc : ((DistanceOutNeighborsAtValue p i r).card : ℝ) ≤ 3 := by
        exact_mod_cast hcap i r
      linarith
    have hcount :
        (∑ r ∈ RT,
          (if (DistanceOutNeighborsAtValue p i r).card = 3 then (0 : ℝ) else 1)) ≤
        ∑ r ∈ RT, (3 - ((DistanceOutNeighborsAtValue p i r).card : ℝ)) := by
      apply Finset.sum_le_sum
      intro r _hr
      split_ifs with h
      · rw [h]; norm_num
      · have hc : (DistanceOutNeighborsAtValue p i r).card ≤ 2 := by
          have := hcap i r
          omega
        have hcR : ((DistanceOutNeighborsAtValue p i r).card : ℝ) ≤ 2 := by
          exact_mod_cast hc
        linarith
    have hsum :
        (∑ r ∈ RT,
          (if (DistanceOutNeighborsAtValue p i r).card = 3 then (0 : ℝ) else 1)) =
        ((RT.filter (fun r ↦ ¬(DistanceOutNeighborsAtValue p i r).card = 3)).card : ℝ) := by
      simp [Finset.sum_ite, Finset.sum_const]
    rw [hsum] at hcount
    have hc := Finset.card_filter_add_card_filter_not
      (s := RT) (p := fun r ↦ (DistanceOutNeighborsAtValue p i r).card = 3)
    have hcR := congrArg (fun k : ℕ ↦ (k : ℝ)) hc
    simp only [Nat.cast_add] at hcR
    linarith
  have hcard : ((SaturatedDistanceIncidences p).filter (fun ir ↦ ir.2 ^ 2 ≤ T)).card =
      ∑ i, (RT.filter (fun r ↦ (DistanceOutNeighborsAtValue p i r).card = 3)).card := by
    unfold SaturatedDistanceIncidences
    rw [Finset.filter_filter, hRT]
    simp_rw [Finset.filter_filter, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.product_eq_sprod, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro r _hr
    by_cases h1 : (DistanceOutNeighborsAtValue p i r).card = 3 <;>
      by_cases h2 : r ^ 2 ≤ T <;> simp [h1, h2]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) ↦ hrow i)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Nat.cast_sum, ← hcard] using h

theorem closedBall_sq_card_lower_bound_of_pairs {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) {t K : ℝ} (ht : 0 ≤ t)
    (hL : (n : ℝ) * K ≤ ((OrderedClosePairs p t).card : ℝ)) (j : Fin n) :
    K - (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) + 1 ≤
      (((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) := by
  classical
  rw [orderedClosePairs_card_eq_sum_row] at hL
  push_cast at hL
  obtain ⟨i, -, hi⟩ : ∃ i ∈ (Finset.univ : Finset (Fin n)),
      K ≤ ((ClosePairRow p i t).card : ℝ) := by
    apply Finset.exists_le_of_sum_le ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact hL
  have hstab := closePairRow_card_stability hn hcap i j t
  have hsub : insert j (ClosePairRow p j t) ⊆
      (Finset.univ : Finset (Fin n)).filter (fun q ↦ dist (p j) (p q) ^ 2 ≤ t) := by
    intro q hq
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · rw [dist_self]
      simpa using ht
    · simp only [ClosePairRow, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      exact hq.2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [ClosePairRow])] at hcard
  have hcardR : ((ClosePairRow p j t).card : ℝ) + 1 ≤
      (((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) := by
    exact_mod_cast hcard
  linarith

theorem sub_card_far_le_three_mul_palette {p : Config n}
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) {T : ℝ} (hT : 0 ≤ T)
    (w : Fin n) :
    (n : ℝ) - 1 - (((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ T < dist (p w) (p q) ^ 2)).card : ℝ) ≤
      3 * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ T)).card : ℝ) := by
  classical
  set RT := (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ T) with hRT
  have hrow : ((ClosePairRow p w T).card : ℝ) ≤ 3 * (RT.card : ℝ) := by
    rw [closePairRow_card_eq_sum]
    push_cast
    calc ∑ r ∈ RT, ((DistanceOutNeighborsAtValue p w r).card : ℝ) ≤
          ∑ _r ∈ RT, (3 : ℝ) :=
          Finset.sum_le_sum (fun r _ ↦ by exact_mod_cast hcap w r)
      _ = 3 * (RT.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hnear : (Finset.univ : Finset (Fin n)).filter
      (fun q ↦ ¬T < dist (p w) (p q) ^ 2) = insert w (ClosePairRow p w T) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      ClosePairRow, not_lt]
    constructor
    · intro hq
      by_cases hqw : q = w
      · exact Or.inl hqw
      · exact Or.inr ⟨Ne.symm hqw, hq⟩
    · rintro (rfl | ⟨_, hq⟩)
      · rw [dist_self]
        simpa using hT
      · exact hq
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun q ↦ T < dist (p w) (p q) ^ 2)
  rw [hnear, Finset.card_insert_of_notMem (by simp [ClosePairRow]), Finset.card_univ,
    Fintype.card_fin] at hc
  have hcR := congrArg (fun k : ℕ ↦ (k : ℝ)) hc
  simp only [Nat.cast_add, Nat.cast_one] at hcR
  linarith

theorem closedBall_sq_card_lower_bound_all_radii {p : Config n}
    (hp : Function.Injective p) (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) (hn : 0 < n)
    {t : ℝ} (ht : 0 ≤ t)
    (hpair : ∀ ir ∈ SaturatedDistanceIncidences p, ∃ a b,
      a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧ a < b ∧ dist (p a) (p b) ^ 2 ≤ t)
    (j : Fin n) :
    2 * (n : ℝ) - 5 * (NumDistancesOrdered p : ℝ) - 1 ≤
      (((Finset.univ : Finset (Fin n)).filter (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) := by
  have hCL := card_le_orderedClosePairs_of_pairs hp hgp3 _ hpair
  have hC := saturatedDistanceIncidences_lower_bound hn hcap
  have hL : (n : ℝ) * ((n : ℝ) - 1 - 2 * (NumDistancesOrdered p : ℝ)) ≤
      ((OrderedClosePairs p t).card : ℝ) := hC.trans (by exact_mod_cast hCL)
  have h := closedBall_sq_card_lower_bound_of_pairs hn hcap ht hL j
  linarith

theorem closedBall_sq_card_lower_bound_small_radii {p : Config n}
    (hp : Function.Injective p) (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) (hn : 0 < n)
    {T t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t)
    (hpair : ∀ ir ∈ SaturatedDistanceIncidences p, ir.2 ^ 2 ≤ T → ∃ a b,
      a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧ a < b ∧ dist (p a) (p b) ^ 2 ≤ t)
    (w j : Fin n) :
    ((n : ℝ) - 1 - (((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ T < dist (p w) (p q) ^ 2)).card : ℝ)) / 3 -
        2 * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) + 1 ≤
      (((Finset.univ : Finset (Fin n)).filter (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) := by
  classical
  have hCL := card_le_orderedClosePairs_of_pairs hp hgp3
    ((SaturatedDistanceIncidences p).filter (fun ir ↦ ir.2 ^ 2 ≤ T))
    (fun ir hir ↦ hpair ir (Finset.mem_filter.mp hir).1 (Finset.mem_filter.mp hir).2)
  have hC := saturatedDistanceIncidences_filter_lower_bound hn hcap T
  have hCLR : (((SaturatedDistanceIncidences p).filter (fun ir ↦ ir.2 ^ 2 ≤ T)).card : ℝ) ≤
      ((OrderedClosePairs p t).card : ℝ) := by
    exact_mod_cast hCL
  have h := closedBall_sq_card_lower_bound_of_pairs hn hcap ht (hC.trans hCLR) j
  have hpal := sub_card_far_le_three_mul_palette hcap hT w
  linarith

end

section

open scoped RealInnerProductSpace

theorem not_three_pairwise_sq_far {c u v w : Point} {ρ : ℝ}
    (hu : dist u c ≤ ρ) (hv : dist v c ≤ ρ) (hw : dist w c ≤ ρ)
    (huv : 3 * ρ ^ 2 < dist u v ^ 2) (huw : 3 * ρ ^ 2 < dist u w ^ 2)
    (hvw : 3 * ρ ^ 2 < dist v w ^ 2) : False := by
  have hU : ‖u - c‖ ^ 2 ≤ ρ ^ 2 := by
    rw [← dist_eq_norm]; exact pow_le_pow_left₀ dist_nonneg hu 2
  have hV : ‖v - c‖ ^ 2 ≤ ρ ^ 2 := by
    rw [← dist_eq_norm]; exact pow_le_pow_left₀ dist_nonneg hv 2
  have hW : ‖w - c‖ ^ 2 ≤ ρ ^ 2 := by
    rw [← dist_eq_norm]; exact pow_le_pow_left₀ dist_nonneg hw 2
  rw [dist_eq_norm, ← sub_sub_sub_cancel_right u v c] at huv
  rw [dist_eq_norm, ← sub_sub_sub_cancel_right u w c] at huw
  rw [dist_eq_norm, ← sub_sub_sub_cancel_right v w c] at hvw
  set U := u - c
  set V := v - c
  set W := w - c
  clear_value U V W
  have hid : ‖U - V‖ ^ 2 + ‖U - W‖ ^ 2 + ‖V - W‖ ^ 2 + ‖U + V + W‖ ^ 2 =
      3 * (‖U‖ ^ 2 + ‖V‖ ^ 2 + ‖W‖ ^ 2) := by
    rw [norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real, norm_add_sq_real,
      norm_add_sq_real, inner_add_left]
    ring
  nlinarith [sq_nonneg ‖U + V + W‖]

end

section

open EuclideanGeometry
variable {n : ℕ}

private lemma saturated_incidence_pair_of_triple {p : Config n} {t : ℝ}
    {ir : Fin n × ℝ} (hir : ir ∈ SaturatedDistanceIncidences p)
    (htriple : ∀ f : Fin 3 → Fin n, (∀ i, dist (p ir.1) (p (f i)) = ir.2) →
      ∃ i j : Fin 3, i ≠ j ∧ dist (p (f i)) (p (f j)) ^ 2 ≤ t) :
    ∃ a b, a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      a < b ∧ dist (p a) (p b) ^ 2 ≤ t := by
  classical
  have hc := (Finset.mem_filter.mp hir).2
  obtain ⟨a, b, c, hab, hac, hbc, hs⟩ := Finset.card_eq_three.mp hc
  let f : Fin 3 → Fin n := ![a, b, c]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hmem (i : Fin 3) : f i ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 := by
    rw [hs]; fin_cases i <;> simp [f]
  have hd (i : Fin 3) : dist (p ir.1) (p (f i)) = ir.2 :=
    (Finset.mem_filter.mp (hmem i)).2.2
  obtain ⟨i, j, hij, hclose⟩ := htriple f hd
  rcases lt_or_gt_of_ne (hf.ne hij) with hlt | hgt
  · exact ⟨f i, f j, hmem i, hmem j, hlt, hclose⟩
  · exact ⟨f j, f i, hmem j, hmem i, hgt, by simpa [dist_comm] using hclose⟩

private lemma card_filter_add_add_le (P Q R : Fin n → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (hPQ : ∀ q, P q → ¬Q q) (hPR : ∀ q, P q → ¬R q) (hQR : ∀ q, Q q → ¬R q) :
    ((Finset.univ.filter P).card : ℝ) + (Finset.univ.filter Q).card +
      (Finset.univ.filter R).card ≤ n := by
  have h1 : Disjoint (Finset.univ.filter P) (Finset.univ.filter Q) :=
    Finset.disjoint_filter.mpr fun q _ ↦ hPQ q
  have h2 : Disjoint (Finset.univ.filter P ∪ Finset.univ.filter Q) (Finset.univ.filter R) := by
    rw [Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_filter.mpr fun q _ ↦ hPR q,
      Finset.disjoint_filter.mpr fun q _ ↦ hQR q⟩
  have h := Finset.card_le_univ (Finset.univ.filter P ∪ Finset.univ.filter Q ∪
    Finset.univ.filter R)
  rw [Finset.card_union_of_disjoint h2, Finset.card_union_of_disjoint h1,
    Fintype.card_fin] at h
  exact_mod_cast h

private lemma card_offDiag_filter_eq_sum (R : Fin n → Fin n → Prop) [DecidableRel R]
    (hirr : ∀ a, ¬R a a) :
    ((Finset.univ : Finset (Fin n)).offDiag.filter (fun ab ↦ R ab.1 ab.2)).card =
      ∑ a, ((Finset.univ : Finset (Fin n)).filter (fun q ↦ R a q)).card := by
  have heq : (Finset.univ : Finset (Fin n)).offDiag.filter (fun ab ↦ R ab.1 ab.2) =
      (Finset.univ : Finset (Fin n × Fin n)).filter (fun ab ↦ R ab.1 ab.2) := by
    ext ab
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and]
    refine ⟨fun h ↦ h.2, fun h ↦ ⟨fun he ↦ hirr ab.2 ?_, h⟩⟩
    rw [he] at h
    exact h
  rw [heq, Finset.card_filter, Fintype.sum_prod_type]
  simp only [Finset.card_filter]

private lemma heavy_small_balls {p : Config n} {c : Point} {ρ : ℝ}
    (hp : Function.Injective p) (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) (hn0 : 0 < n)
    (hρ : 0 < ρ) (hlo : ∀ i, ρ ^ 2 * (1 - 3013 / 32500) ≤ dist (p i) c ^ 2)
    (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2) (i : Fin n) :
    8 / 3 * (n : ℝ) - 109 / 15 * (NumDistancesOrdered p : ℝ) - 5 / 3 ≤
      ((ConfigClosedBall p i (117 / 1000 * ρ)).card : ℝ) := by
  classical
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hle : ∀ i, dist (p i) c ≤ ρ := fun i ↦ by
    nlinarith [hhi i, dist_nonneg (x := p i) (y := c)]
  have hpair0 : ∀ ir ∈ SaturatedDistanceIncidences p, ∃ a b,
      a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧ a < b ∧
      dist (p a) (p b) ^ 2 ≤ 1901 / 10000 * ρ ^ 2 := fun ir hir ↦
    saturated_incidence_pair_of_triple hir fun f hf ↦
      scaled_annular_equidistant_triple_close_pair_sharp c (p ir.1) (fun i ↦ p (f i)) hρ
        (σ := 381 / 400) (by norm_num) (by norm_num) (by norm_num) (hlo ir.1)
        (fun i ↦ hlo (f i)) (fun i ↦ hhi (f i)) (fun i j ↦ (hf i).trans (hf j).symm)
  have hm0 := closedBall_sq_card_lower_bound_all_radii hp hgp3 hcap hn0 (by positivity)
    hpair0
  have hpair1 : ∀ ir ∈ SaturatedDistanceIncidences p, ir.2 ^ 2 ≤ 3 * ρ ^ 2 → ∃ a b,
      a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧ a < b ∧
      dist (p a) (p b) ^ 2 ≤ 13689 / 1000000 * ρ ^ 2 := fun ir hir hr ↦
    saturated_incidence_pair_of_triple hir fun f hf ↦
      scaled_annular_equidistant_triple_close_pair_small_radius c (p ir.1) (fun i ↦ p (f i))
        hρ (σ := 381 / 400) (κ := 3 / 5) (γ := 9093 / 10000)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (hlo ir.1) (hhi ir.1) (fun i ↦ hlo (f i)) (fun i ↦ hhi (f i))
        (fun i j ↦ (hf i).trans (hf j).symm) (fun i ↦ by rw [hf i]; exact hr)
  have hm1 := closedBall_sq_card_lower_bound_small_radii hp hgp3 hcap hn0
    (T := 3 * ρ ^ 2) (by positivity) (by positivity) hpair1
  have hant := six_mul_card_pairs_le_of_apex hp hgp3 hcap
    (fun a b ↦ 3 * ρ ^ 2 < dist (p a) (p b) ^ 2)
    (fun a h ↦ by rw [dist_self] at h; nlinarith)
    (fun a b h ↦ by rwa [dist_comm])
    (fun r ↦ ρ ^ 2 * (1 - 2 * (3013 / 32500)) < r ^ 2 ∧ r ^ 2 < 3 * ρ ^ 2)
    (fun h ↦ by nlinarith [h.1])
    (fun z a b hab heq ↦ apex_sq_dist_mem_of_sq_far hρ (hlo z) (hhi z) (hlo a) (hhi a)
      (hlo b) (hhi b) hab heq)
    (fun _ a b c' _ _ _ hab hbc hac ↦ not_three_pairwise_sq_far (hle a) (hle b) (hle c')
      hab hac hbc)
  have hrow := card_offDiag_filter_eq_sum (fun a b ↦ 3 * ρ ^ 2 < dist (p a) (p b) ^ 2)
    (fun a h ↦ by rw [dist_self] at h; nlinarith)
  rw [hrow] at hant
  push_cast at hant
  have hW : ∀ z, (((Finset.univ : Finset (Fin n)).filter (fun q ↦
      ρ ^ 2 * (1 - 2 * (3013 / 32500)) < dist (p z) (p q) ^ 2 ∧
        dist (p z) (p q) ^ 2 < 3 * ρ ^ 2)).card : ℝ) ≤
      (n : ℝ) - (2 * (n : ℝ) - 5 * (NumDistancesOrdered p : ℝ) - 1) -
        (((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ 3 * ρ ^ 2 < dist (p z) (p q) ^ 2)).card : ℝ) := fun z ↦ by
    have h := card_filter_add_add_le
      (fun q ↦ ρ ^ 2 * (1 - 2 * (3013 / 32500)) < dist (p z) (p q) ^ 2 ∧
        dist (p z) (p q) ^ 2 < 3 * ρ ^ 2)
      (fun q ↦ dist (p z) (p q) ^ 2 ≤ 1901 / 10000 * ρ ^ 2)
      (fun q ↦ 3 * ρ ^ 2 < dist (p z) (p q) ^ 2)
      (fun q h1 h2 ↦ by nlinarith [h1.1]) (fun q h1 h2 ↦ by linarith [h1.2])
      (fun q h1 h2 ↦ by nlinarith)
    linarith [hm0 z]
  have hWsum := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset (Fin n))) ↦ hW z)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hWsum
  obtain ⟨w, -, hw⟩ : ∃ w ∈ (Finset.univ : Finset (Fin n)),
      (((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ 3 * ρ ^ 2 < dist (p w) (p q) ^ 2)).card : ℝ) ≤
        (3 * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) +
          2 * ((n : ℝ) - (2 * (n : ℝ) - 5 * (NumDistancesOrdered p : ℝ) - 1))) / 5 := by
    apply Finset.exists_le_of_sum_le ⟨⟨0, hn0⟩, Finset.mem_univ _⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    nlinarith
  have hsub : (Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p i) (p q) ^ 2 ≤ 13689 / 1000000 * ρ ^ 2) ⊆
      ConfigClosedBall p i (117 / 1000 * ρ) := by
    intro q hq
    simp only [ConfigClosedBall, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    nlinarith [dist_nonneg (x := p i) (y := p q)]
  have hcard : (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p i) (p q) ^ 2 ≤ 13689 / 1000000 * ρ ^ 2)).card : ℝ) ≤
      ((ConfigClosedBall p i (117 / 1000 * ρ)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  linarith [hm1 w i]

private lemma no_far_triangle_on_circle {p : Config n} {c : Point} {ρ : ℝ} (hρ : 0 < ρ)
    (hlo : ∀ i, ρ ^ 2 * (1 - 3013 / 32500) ≤ dist (p i) c ^ 2)
    (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2) {z a b c' : Fin n}
    (hab : dist (p z) (p a) = dist (p z) (p b)) (hac : dist (p z) (p a) = dist (p z) (p c'))
    (h1 : 117 / 250 * ρ < dist (p a) (p b)) (h2 : 117 / 250 * ρ < dist (p b) (p c'))
    (h3 : 117 / 250 * ρ < dist (p a) (p c')) : False := by
  have hfar : ∀ u v : Point, 117 / 250 * ρ < dist u v →
      1901 / 10000 * ρ ^ 2 < dist u v ^ 2 := fun u v h ↦ by
    have h1 : (0 : ℝ) < dist u v - 117 / 250 * ρ := by linarith
    have h2 : (0 : ℝ) < dist u v + 117 / 250 * ρ := by linarith
    nlinarith [mul_pos h1 h2]
  obtain ⟨i, j, hij, hclose⟩ := scaled_annular_equidistant_triple_close_pair_sharp c (p z)
    ![p a, p b, p c'] hρ (σ := 381 / 400) (t := 1901 / 10000) (by norm_num) (by norm_num)
    (by norm_num) (hlo z) (fun i ↦ by fin_cases i <;> simp [hlo])
    (fun i ↦ by fin_cases i <;> simp [hhi])
    (fun i j ↦ by fin_cases i <;> fin_cases j <;> simp [← hab, ← hac])
  have hab2 := hfar _ _ h1
  have hbc2 := hfar _ _ h2
  have hac2 := hfar _ _ h3
  have hba2 := hfar _ _ (show 117 / 250 * ρ < dist (p b) (p a) by rwa [dist_comm])
  have hcb2 := hfar _ _ (show 117 / 250 * ρ < dist (p c') (p b) by rwa [dist_comm])
  have hca2 := hfar _ _ (show 117 / 250 * ρ < dist (p c') (p a) by rwa [dist_comm])
  fin_cases i <;> fin_cases j <;> simp at hij hclose <;> linarith

private lemma many_far_points {p : Config n} {c : Point} {ρ : ℝ}
    (hsum : ∑ i, (p i - c) = 0) (hρ : 0 < ρ)
    (hlo : ∀ i, ρ ^ 2 * (1 - 3013 / 32500) ≤ dist (p i) c ^ 2)
    (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2) (z : Fin n) :
    (n : ℝ) * (2921393 / 1625000) - n ≤
      2921393 / 1625000 * (((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ 117 / 250 * ρ < dist (p z) (p q))).card : ℝ) := by
  classical
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hb := configClosedBall_card_mul_le hsum hρ hlo hhi z (θ := 117 / 250 * ρ)
  have hv : ρ ^ 2 * (2 - 3013 / 32500) - (117 / 250 * ρ) ^ 2 / 2 =
      2921393 / 1625000 * ρ ^ 2 := by ring
  rw [hv] at hb
  have hb' : ((ConfigClosedBall p z (117 / 250 * ρ)).card : ℝ) * (2921393 / 1625000) ≤ n := by
    have h' : ((ConfigClosedBall p z (117 / 250 * ρ)).card : ℝ) * (2921393 / 1625000) *
        ρ ^ 2 ≤ (n : ℝ) * ρ ^ 2 := by linarith
    exact le_of_mul_le_mul_right h' hρ2
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun q ↦ dist (p z) (p q) ≤ 117 / 250 * ρ)
  simp only [not_le, Finset.card_univ, Fintype.card_fin] at hsplit
  have hsplitR : ((ConfigClosedBall p z (117 / 250 * ρ)).card : ℝ) +
      (((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ 117 / 250 * ρ < dist (p z) (p q))).card : ℝ) = n := by
    exact_mod_cast hsplit
  linarith

end

end Esgk

section

open EuclideanGeometry Esgk
open EuclideanGeometry

theorem solution {n : ℕ} {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p))
    (hn : 10000 ≤ n) :
    (1 / 3 + 1 / 130) * (n : ℝ) < (NumDistances p : ℝ) := by
  by_contra hnot
  have hD : (NumDistances p : ℝ) ≤ (1 / 3 + 1 / 130) * (n : ℝ) := le_of_not_gt hnot
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have h4n : 4 / (n : ℝ) ≤ 4 / 10000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have hcap := distanceOutNeighborsAtValue_card_le_three_of_noFourCocircular hp hgp.2
  have hρ : 0 < distanceAnnulusRadius p := distanceAnnulusRadius_pos hp hn2 hcap
  have hρsq := (distanceAnnulusRadius_bounds hn0 hcap).2.1
  have hs := thin_annulus_sq_of_noFourCocircular hp hgp.2 hn0 hD
  have hsum := sum_sub_configCentroid p hn0
  have hDo : (NumDistancesOrdered p : ℝ) = (NumDistances p : ℝ) := by
    rw [numDistances_eq_numDistancesOrdered_of_injective hp]
  set ρ := distanceAnnulusRadius p with hρdef
  set c := configCentroid p with hcdef
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hlo : ∀ i, ρ ^ 2 * (1 - 3013 / 32500) ≤ dist (p i) c ^ 2 := by
    intro i
    have h := (hs i).1
    rw [← hρsq] at h
    have hx : 1 - 3013 / 32500 ≤ 1 - 12 * (1 / 130 : ℝ) - 4 / (n : ℝ) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hx hρ2.le]
  have hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2 := by
    intro i
    rw [hρsq]
    exact (hs i).2
  have hball := heavy_small_balls hp hgp.1 hcap hn0 hρ hlo hhi
  have hbr : ρ ^ 2 * (2 - 3013 / 32500) - (117 / 1000 * ρ) ^ 2 / 2 +
      2 * (ρ ^ 2 * (2 - 3013 / 32500) - (117 / 250 * ρ + 117 / 1000 * ρ) ^ 2 / 2) =
      139692993 / 26000000 * ρ ^ 2 := by ring
  have hmn : (n : ℝ) < (8 / 3 * (n : ℝ) - 109 / 15 * (NumDistancesOrdered p : ℝ) - 5 / 3) *
      (139692993 / 26000000) := by rw [hDo]; linarith
  have hmρ := mul_lt_mul_of_pos_right hmn hρ2
  have hθτ : (117 / 250 * ρ + 117 / 1000 * ρ) ^ 2 = 13689 / 40000 * ρ ^ 2 := by ring
  have hiso := no_isosceles_far_base_of_heavy_balls hsum hρ hlo hhi hball (θ := 117 / 250 * ρ)
    (by positivity) (by linarith) (by rw [hθτ]; linarith) (by rw [hbr]; linarith)
  have hθ : 0 ≤ 117 / 250 * ρ := by positivity
  have hcount := farOrderedPairs_card_le_of_apex hp hgp.1 hcap hθ
    (fun z a b hab heq ↦ by
      by_contra h
      exact hiso z a b heq (le_of_not_gt h) hab)
    (fun _ _ _ _ hab hac _ h1 h2 h3 ↦ no_far_triangle_on_circle hρ hlo hhi hab hac h1 h2 h3)
  rw [hDo] at hcount
  have hlow : (n : ℝ) * ((n : ℝ) * (2921393 / 1625000) - n) ≤
      2921393 / 1625000 * ((FarOrderedPairs p (117 / 250 * ρ)).card : ℝ) := by
    rw [farOrderedPairs_card_eq_sum hθ]
    push_cast
    rw [Finset.mul_sum]
    calc (n : ℝ) * ((n : ℝ) * (2921393 / 1625000) - n) =
          ∑ _z : Fin n, ((n : ℝ) * (2921393 / 1625000) - n) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun z _ ↦ many_far_points hsum hρ hlo hhi z)
  have hfin : (n : ℝ) * ((n : ℝ) * (2921393 / 1625000) - n) ≤
      (n : ℝ) * (2921393 / 1625000 *
        (3 * (3 * (NumDistances p : ℝ) - (n : ℝ) + 1))) := by
    nlinarith
  have hfin' := le_of_mul_le_mul_left hfin hnpos
  linarith

end
