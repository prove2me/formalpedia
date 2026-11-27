-- Prove2me | solution 1 for Disjunctive.CutCorrespondence.rank_bound_four_cut_families_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:43:09.620595+00:00
-- url     : https://prove2.me/submissions/c514b889-3e7d-45f6-a735-cf56f1553c87
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Basic
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp_v2
import Definitions.Def_Disjunctive_CutCorrespondence_Tableau_v2
import Definitions.Def_Disjunctive_CutCorrespondence_Rank_v2
import Theorems.Thm_LinearOptimization_polyhedron_projection
import Theorems.Thm_LinearOptimization_farkas_inequality_form_fintype
import Theorems.Thm_LinearOptimization_lp_attains_or_unbounded
import Theorems.Thm_Disjunctive_CutCorrespondence_strengthenedLPClosure_isPoly
import Theorems.Thm_Disjunctive_CutCorrespondence_migClosure_isPoly

namespace Disjunctive.CutCorrespondence

open Set Finset

lemma face_lemma {E : Type} [AddCommGroup E] [Module ℝ E] (L : E →ₗ[ℝ] ℝ) (d : ℝ)
    (T : Set E) (hT : ∀ x ∈ T, d ≤ L x) (y : E) (hy : y ∈ convexHull ℝ T) (hLy : L y = d) :
    y ∈ convexHull ℝ (T ∩ {x | L x = d}) := by
  rw [_root_.convexHull_eq] at hy
  obtain ⟨ι, t, w, z, hw0, hw1, hz, rfl⟩ := hy
  classical
  have hcm : t.centerMass w z = ∑ i ∈ t, w i • z i := Finset.centerMass_eq_of_sum_1 _ _ hw1
  have hsum : ∑ i ∈ t, w i * (L (z i) - d) = 0 := by
    have : L (t.centerMass w z) = ∑ i ∈ t, w i * L (z i) := by
      rw [hcm, map_sum]; simp [map_smul]
    rw [hLy] at this
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
    linarith
  have hnn : ∀ i ∈ t, 0 ≤ w i * (L (z i) - d) := fun i hi =>
    mul_nonneg (hw0 i hi) (sub_nonneg.mpr (hT _ (hz i hi)))
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
  rw [← Finset.centerMass_filter_ne_zero]
  apply Finset.centerMass_mem_convexHull
  · intro i hi; exact hw0 i (Finset.mem_filter.mp hi).1
  · rw [Finset.sum_filter_ne_zero, hw1]; norm_num
  · intro i hi
    obtain ⟨hit, hwi⟩ := Finset.mem_filter.mp hi
    refine ⟨hz i hit, ?_⟩
    have := hzero i hit
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hwi
    · show L (z i) = d; linarith

/-- coordinate functional -/
def coordL {n : ℕ} (k : Fin n) : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj k

lemma split_face {n : ℕ} (T : Set (Fin n → ℝ)) (k : Fin n)
    (hT : ∀ x ∈ T, 0 ≤ x k ∧ x k ≤ 1) :
    convexHull ℝ T ∩ ZeroOneSet k ⊆ convexHull ℝ (T ∩ ZeroOneSet k) := by
  rintro y ⟨hy, hyk⟩
  rcases hyk with h0 | h1
  · have := face_lemma (coordL k) 0 T (fun x hx => (hT x hx).1) y hy h0
    refine convexHull_mono ?_ this
    rintro x ⟨hx, hx'⟩; exact ⟨hx, Or.inl hx'⟩
  · have := face_lemma (-(coordL k)) (-1) T (fun x hx => by
        simp [coordL]; linarith [(hT x hx).2]) y hy (by simp [coordL, h1])
    refine convexHull_mono ?_ this
    rintro x ⟨hx, hx'⟩
    refine ⟨hx, Or.inr ?_⟩
    simp [coordL] at hx'; linarith

lemma splitConvexify_hull {n : ℕ} (T : Set (Fin n → ℝ)) (k : Fin n)
    (hT : ∀ x ∈ T, 0 ≤ x k ∧ x k ≤ 1) :
    SplitConvexify (convexHull ℝ T) k = convexHull ℝ (T ∩ ZeroOneSet k) := by
  unfold SplitConvexify
  apply Set.Subset.antisymm
  · exact convexHull_min (split_face T k hT) (convex_convexHull ℝ _)
  · apply convexHull_mono
    exact Set.inter_subset_inter_left _ (subset_convexHull ℝ T)

/-- Sequential convexification: folding `SplitConvexify` over a list of box coordinates. -/
theorem foldl_splitConvexify {n : ℕ} (S : Set (Fin n → ℝ)) (hS : Convex ℝ S)
    (Nprime : Finset (Fin n)) (hbox : ∀ x ∈ S, ∀ j ∈ Nprime, 0 ≤ x j ∧ x j ≤ 1)
    (l : List (Fin n)) (hl : ∀ j ∈ l, j ∈ Nprime) :
    l.foldl SplitConvexify S = convexHull ℝ (S ∩ {x | ∀ j ∈ l, x j = 0 ∨ x j = 1}) := by
  induction l using List.reverseRecOn with
  | nil => simp [hS.convexHull_eq]
  | append_singleton l k ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil,
      ih (fun j hj => hl j (List.mem_append_left _ hj))]
    have hk : k ∈ Nprime := hl k (by simp)
    rw [splitConvexify_hull _ k (fun x hx => hbox x hx.1 k hk)]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ZeroOneSet, List.mem_append,
      List.mem_singleton]
    constructor
    · rintro ⟨⟨hx, h1⟩, h2⟩
      exact ⟨hx, fun j hj => hj.elim (h1 j) (fun e => e ▸ h2)⟩
    · rintro ⟨hx, h⟩
      exact ⟨⟨hx, fun j hj => h j (Or.inl hj)⟩, h k (Or.inr rfl)⟩

lemma poly_convex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Convex ℝ (Poly A b) := by
  intro x hx y hy a c ha hc hac i
  have h1 := hx i; have h2 := hy i
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have : b i = a * b i + c * b i := by rw [← add_mul, hac, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hc]

lemma mulVec_single {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (ρ : Fin m) (j : Fin n) (c : ℝ)
    (h : A ρ = c • Pi.single j 1) (x : Fin n → ℝ) : (A.mulVec x) ρ = c * x j := by
  simp [Matrix.mulVec, dotProduct, h, Pi.single_apply]

lemma box_of_system {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hsys : IsMixedZeroOneSystem A b Nprime) :
    (∀ x ∈ Poly A b, ∀ j, 0 ≤ x j) ∧ ∀ x ∈ Poly A b, ∀ j ∈ Nprime, x j ≤ 1 := by
  obtain ⟨h0, h1⟩ := hsys
  constructor
  · intro x hx j
    obtain ⟨ρ, hρ, hb⟩ := h0 j
    have := hx ρ
    rw [mulVec_single A ρ j 1 (by simp [hρ]) x, hb] at this
    linarith
  · intro x hx j hj
    obtain ⟨ρ, hρ, hb⟩ := h1 j hj
    have := hx ρ
    rw [mulVec_single A ρ j (-1) (by simp [hρ]) x, hb] at this
    linarith

theorem partA {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hsys : IsMixedZeroOneSystem A b Nprime) :
    HasRankAtMost SplitConvexify (Poly A b) Nprime Nprime.card := by
  obtain ⟨hb0, hb1⟩ := box_of_system A b Nprime hsys
  refine ⟨Nprime.toList, Nprime.nodup_toList, Nprime.toList_toFinset, Nprime.length_toList, ?_⟩
  unfold IterateCutStep
  rw [foldl_splitConvexify (Poly A b) (poly_convex A b) Nprime
    (fun x hx j hj => ⟨hb0 x hx j, hb1 x hx j hj⟩) _ (fun j hj => Finset.mem_toList.mp hj)]
  congr 1
  ext x
  simp [ZeroOneSet]

end Disjunctive.CutCorrespondence


namespace Disjunctive.CutCorrespondence

open Set Finset

/-- Generic rank lemma: if every step of `Phi`, applied to a polyhedron sandwiched between
`P_I` and `P`, stays above `P_I`, stays below `conv(S ∩ {x_k ∈ {0,1}})`, and is again a
polyhedron, then `P` has rank at most `|N'|`. -/
theorem rank_of_sandwich {m0 n : ℕ} (Phi : CutStep n) (A0 : Matrix (Fin m0) (Fin n) ℝ)
    (b0 : Fin m0 → ℝ) (Nprime : Finset (Fin n))
    (hbox : ∀ x ∈ Poly A0 b0, ∀ j ∈ Nprime, 0 ≤ x j ∧ x j ≤ 1)
    (hstep : ∀ k ∈ Nprime, ∀ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
      convexHull ℝ (Poly A0 b0 ∩ ⋂ j ∈ Nprime, ZeroOneSet j) ⊆ Poly A b →
      Poly A b ⊆ Poly A0 b0 →
      convexHull ℝ (Poly A0 b0 ∩ ⋂ j ∈ Nprime, ZeroOneSet j) ⊆ Phi (Poly A b) k ∧
      Phi (Poly A b) k ⊆ convexHull ℝ (Poly A b ∩ ZeroOneSet k) ∧
      ∃ (m' : ℕ) (A' : Matrix (Fin m') (Fin n) ℝ) (b' : Fin m' → ℝ),
        Poly A' b' = Phi (Poly A b) k) :
    HasRankAtMost Phi (Poly A0 b0) Nprime Nprime.card := by
  set P := Poly A0 b0 with hPdef
  set PI := convexHull ℝ (P ∩ ⋂ j ∈ Nprime, ZeroOneSet j) with hPI
  have hPc : Convex ℝ P := poly_convex A0 b0
  have key : ∀ l : List (Fin n), (∀ j ∈ l, j ∈ Nprime) →
      ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
        l.foldl Phi P = Poly A b ∧ PI ⊆ Poly A b ∧
        Poly A b ⊆ convexHull ℝ (P ∩ {x | ∀ j ∈ l, x j = 0 ∨ x j = 1}) := by
    intro l
    induction l using List.reverseRecOn with
    | nil =>
      intro _
      refine ⟨m0, A0, b0, rfl, convexHull_min Set.inter_subset_left hPc, ?_⟩
      intro x hx; apply subset_convexHull; exact ⟨hx, by simp⟩
    | append_singleton l k ih =>
      intro hl
      obtain ⟨m, A, b, hT, hPIT, hTQ⟩ := ih (fun j hj => hl j (List.mem_append_left _ hj))
      have hk : k ∈ Nprime := hl k (by simp)
      have hTP : Poly A b ⊆ P := hTQ.trans (convexHull_min Set.inter_subset_left hPc)
      obtain ⟨h1, h2, m', A', b', h3⟩ := hstep k hk m A b hPIT hTP
      refine ⟨m', A', b', ?_, h3 ▸ h1, ?_⟩
      · have hc : List.foldl Phi P (l ++ [k]) = Phi (List.foldl Phi P l) k :=
          List.foldl_concat ..
        rw [hc, hT, h3]
      · rw [h3]
        refine h2.trans ?_
        have hQ : ∀ x ∈ P ∩ {x | ∀ j ∈ l, x j = 0 ∨ x j = 1}, 0 ≤ x k ∧ x k ≤ 1 :=
          fun x hx => hbox x hx.1 k hk
        calc convexHull ℝ (Poly A b ∩ ZeroOneSet k)
            ⊆ convexHull ℝ (convexHull ℝ (P ∩ {x | ∀ j ∈ l, x j = 0 ∨ x j = 1}) ∩
                ZeroOneSet k) := convexHull_mono (Set.inter_subset_inter_left _ hTQ)
          _ = SplitConvexify (convexHull ℝ (P ∩ {x | ∀ j ∈ l, x j = 0 ∨ x j = 1})) k := rfl
          _ = convexHull ℝ ((P ∩ {x | ∀ j ∈ l, x j = 0 ∨ x j = 1}) ∩ ZeroOneSet k) :=
              splitConvexify_hull _ k hQ
          _ ⊆ _ := by
              apply convexHull_mono
              rintro x ⟨⟨hx, h1⟩, h2⟩
              refine ⟨hx, ?_⟩
              intro j hj
              simp only [List.mem_append, List.mem_singleton] at hj
              rcases hj with hj | rfl
              · exact h1 j hj
              · exact h2
  refine ⟨Nprime.toList, Nprime.nodup_toList, Nprime.toList_toFinset, Nprime.length_toList, ?_⟩
  obtain ⟨m, A, b, hT, hPIT, hTQ⟩ := key Nprime.toList (fun j hj => Finset.mem_toList.mp hj)
  unfold IterateCutStep
  rw [hT]
  apply Set.Subset.antisymm _ hPIT
  refine hTQ.trans (convexHull_mono ?_)
  rintro x ⟨hx, h⟩
  refine ⟨hx, ?_⟩
  simp only [Set.mem_iInter]
  intro j hj
  exact h j (Finset.mem_toList.mpr hj)

/-- The integer-split inequality behind simple disjunctive and mixed integer Gomory cuts. -/
lemma split_ineq {n : ℕ} (f0 : ℝ) (hf0 : 0 < f0) (hf1 : f0 < 1) (d s c : Fin n → ℝ)
    (hs : ∀ i, 0 ≤ s i) (hc : ∀ i, d i * (1 - f0) ≤ c i ∧ -d i * f0 ≤ c i) (z : ℤ)
    (hz : (z : ℝ) = f0 - ∑ i, d i * s i) : f0 * (1 - f0) ≤ ∑ i, c i * s i := by
  rcases le_or_gt z 0 with h | h
  · have hz' : (z : ℝ) ≤ 0 := by exact_mod_cast h
    have h1 : f0 ≤ ∑ i, d i * s i := by linarith
    have h2 : ∑ i, d i * (1 - f0) * s i ≤ ∑ i, c i * s i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc i).1 (hs i)
    have h3 : ∑ i, d i * (1 - f0) * s i = (1 - f0) * ∑ i, d i * s i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    nlinarith
  · have hz' : (1 : ℝ) ≤ z := by exact_mod_cast h
    have h1 : 1 - f0 ≤ -∑ i, d i * s i := by linarith
    have h2 : ∑ i, -d i * f0 * s i ≤ ∑ i, c i * s i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc i).2 (hs i)
    have h3 : ∑ i, -d i * f0 * s i = f0 * -∑ i, d i * s i := by
      rw [← Finset.sum_neg_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    nlinarith

/-- Tableau identity: `x_k = ā_k0 - ∑_i ā_ki s_i`. -/
lemma tableau_identity {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (ι : Fin n → Fin m) (hdet : IsUnit (Ahat A ι).det) (k : Fin n) (x : Fin n → ℝ) :
    x k = Abar0 A b ι k - ∑ i, Abar A ι k i * Surplus A b ι i x := by
  have hs : (Ahat A ι).mulVec x = Bhat b ι + fun i => Surplus A b ι i x := by
    ext i; simp [Surplus, Ahat, Bhat, Matrix.mulVec, dotProduct]
  have hx : x = (Ahat A ι)⁻¹.mulVec ((Ahat A ι).mulVec x) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have : x k = ((Ahat A ι)⁻¹.mulVec (Bhat b ι)) k +
      ((Ahat A ι)⁻¹.mulVec (fun i => Surplus A b ι i x)) k := by
    conv_lhs => rw [hx, hs, Matrix.mulVec_add]
    rfl
  rw [this]
  simp only [Abar0, Abar, Matrix.mulVec, dotProduct, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]

lemma surplus_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (ι : Fin n → Fin m) (x : Fin n → ℝ) (hx : x ∈ Poly A b) (i : Fin n) :
    0 ≤ Surplus A b ι i x := by
  have := hx (ι i)
  simp only [Surplus, Matrix.mulVec] at this ⊢
  linarith

lemma piCoef_bounds {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (ι : Fin n → Fin m) (k i : Fin n) :
    Abar A ι k i * (1 - Abar0 A b ι k) ≤ PiCoef A b ι k i ∧
      -Abar A ι k i * Abar0 A b ι k ≤ PiCoef A b ι k i :=
  ⟨le_max_left _ _, le_max_right _ _⟩

/-- Simple disjunctive cuts are valid on `S ∩ {x_k ∈ {0,1}}`. -/
lemma simpleDisj_valid {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (k : Fin n)
    (ι : Fin n → Fin m) (hdet : IsUnit (Ahat A ι).det) (h0 : 0 < Abar0 A b ι k)
    (h1 : Abar0 A b ι k < 1) (x : Fin n → ℝ) (hx : x ∈ Poly A b) (hxk : x ∈ ZeroOneSet k) :
    x ∈ SimpleDisjCutSet A b ι k := by
  show Pi0 A b ι k ≤ _
  obtain ⟨z, hz⟩ : ∃ z : ℤ, (z : ℝ) = x k := by
    rcases hxk with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  exact split_ineq _ h0 h1 _ _ _ (surplus_nonneg A b ι x hx)
    (fun i => piCoef_bounds A b ι k i) z (hz.trans (tableau_identity A b ι hdet k x))

lemma simpleDisjClosure_convex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (k : Fin n) : Convex ℝ (SimpleDisjClosure A b k) := by
  unfold SimpleDisjClosure
  refine (poly_convex A b).inter ?_
  refine convex_iInter fun ι => convex_iInter fun _ => convex_iInter fun _ =>
    convex_iInter fun _ => convex_iInter fun _ => ?_
  intro x hx y hy a c ha hc hac
  simp only [SimpleDisjCutSet, Set.mem_ofPred_eq, Surplus] at hx hy ⊢
  have e : ∑ i, PiCoef A b ι k i * (A (ι i) ⬝ᵥ (a • x + c • y) - b (ι i)) =
      a * ∑ i, PiCoef A b ι k i * (A (ι i) ⬝ᵥ x - b (ι i)) +
      c * ∑ i, PiCoef A b ι k i * (A (ι i) ⬝ᵥ y - b (ι i)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    linear_combination (PiCoef A b ι k i) * (b (ι i)) * hac
  rw [e]
  have : Pi0 A b ι k = a * Pi0 A b ι k + c * Pi0 A b ι k := by rw [← add_mul, hac, one_mul]
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hc]

/-- Lower bound for (b): `conv(S ∩ {x_k∈{0,1}}) ⊆` the simple disjunctive closure. -/
lemma conv_subset_simpleDisjClosureOfSet {n : ℕ} (S : Set (Fin n → ℝ)) (k : Fin n) :
    convexHull ℝ (S ∩ ZeroOneSet k) ⊆ SimpleDisjClosureOfSet S k := by
  simp only [SimpleDisjClosureOfSet, Set.subset_iInter_iff]
  intro m A b hS
  subst hS
  apply convexHull_min _ (simpleDisjClosure_convex A b k)
  rintro x ⟨hx, hxk⟩
  refine ⟨hx, ?_⟩
  simp only [Set.mem_iInter]
  intro ι _ hdet h0 h1
  exact simpleDisj_valid A b k ι hdet h0 h1 x hx hxk

end Disjunctive.CutCorrespondence


namespace Disjunctive.CutCorrespondence

open Set Finset

lemma poly_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    x ∈ Poly A b ↔ ∀ i, b i ≤ A i ⬝ᵥ x := Iff.rfl

lemma poly_mem {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {x : Fin n → ℝ}
    (h : x ∈ Poly A b) (i : Fin m) : b i ≤ A i ⬝ᵥ x := h i

/-- A set cut out by finitely many (Fintype-indexed) inequalities is a `Poly`. -/
lemma rep_of_fintype {n : ℕ} {ι : Type*} [Fintype ι] (a : ι → Fin n → ℝ) (β : ι → ℝ) :
    ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
      Poly A b = {x | ∀ i, β i ≤ a i ⬝ᵥ x} := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun r => a (e.symm r), fun r => β (e.symm r), ?_⟩
  ext x
  change (∀ r, β (e.symm r) ≤ a (e.symm r) ⬝ᵥ x) ↔ _
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h i; simpa using h (e i)
  · intro h r; exact h _

lemma dotProduct_append {n K : ℕ} (a x : Fin n → ℝ) (c w : Fin K → ℝ) :
    Fin.append a c ⬝ᵥ Fin.append x w = a ⬝ᵥ x + c ⬝ᵥ w := by
  simp [dotProduct, Fin.sum_univ_add]

/-- Projections of finitely-presented sets are `Poly`s. -/
lemma rep_of_proj {n K : ℕ} {ι : Type*} [Fintype ι] (a : ι → Fin n → ℝ) (c : ι → Fin K → ℝ)
    (β : ι → ℝ) :
    ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
      Poly A b = {x | ∃ w : Fin K → ℝ, ∀ i, β i ≤ a i ⬝ᵥ x + c i ⬝ᵥ w} := by
  classical
  let e := Fintype.equivFin ι
  obtain ⟨m', A', b', h⟩ := LinearOptimization.polyhedron_projection
    (n := n) (k := K) (fun r => Fin.append (a (e.symm r)) (c (e.symm r)))
    (fun r => β (e.symm r))
  refine ⟨m', A', b', ?_⟩
  have hP : Poly A' b' = LinearOptimization.polyhedron A' b' := rfl
  rw [hP, ← h]
  ext x
  simp only [Set.mem_ofPred_eq, LinearOptimization.polyhedron]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, fun i => ?_⟩
    have := hw (e i)
    simpa [Matrix.mulVec, dotProduct_append] using this
  · rintro ⟨w, hw⟩
    refine ⟨w, fun r => ?_⟩
    simp only [Matrix.mulVec, dotProduct_append]
    exact hw _

lemma dotProduct_snoc {n : ℕ} (v w : Fin (n + 1) → ℝ) :
    v ⬝ᵥ w = (fun j => v (Fin.castSucc j)) ⬝ᵥ (fun j => w (Fin.castSucc j)) +
      v (Fin.last n) * w (Fin.last n) := by
  simp [dotProduct, Fin.sum_univ_castSucc]

lemma snoc_dotProduct {n : ℕ} (u : Fin n → ℝ) (t : ℝ) (w : Fin (n + 1) → ℝ) :
    (Fin.snoc u t : Fin (n + 1) → ℝ) ⬝ᵥ w = u ⬝ᵥ (fun j => w (Fin.castSucc j)) +
      t * w (Fin.last n) := by
  rw [dotProduct_snoc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- The lifted (Balas) description of `conv(S ∩ {x_k ∈ {0,1}})`. -/
def LiftCons {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (k : Fin n)
    (x y : Fin n → ℝ) (t : ℝ) : Prop :=
  (∀ i, t * b i ≤ A i ⬝ᵥ y) ∧ (∀ i, (1 - t) * b i ≤ A i ⬝ᵥ (x - y)) ∧ y k = 0 ∧
    x k - y k = 1 - t ∧ 0 ≤ t ∧ t ≤ 1

lemma conv_split_eq_lift {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (k : Fin n)
    (hbox : ∀ x ∈ Poly A b, 0 ≤ x k ∧ x k ≤ 1) :
    convexHull ℝ (Poly A b ∩ ZeroOneSet k) = {x | ∃ y t, LiftCons A b k x y t} := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro x ⟨hx, hxk | hxk⟩
      · refine ⟨x, 1, fun i => by simpa using poly_mem hx i, fun i => by simp, hxk, by simp, by norm_num,
          le_rfl⟩
      · refine ⟨0, 0, fun i => by simp, fun i => by simpa using poly_mem hx i, by simp, by simp [hxk],
          le_rfl, by norm_num⟩
    · rintro x1 ⟨y1, t1, h1⟩ x2 ⟨y2, t2, h2⟩ a c ha hc hac
      refine ⟨a • y1 + c • y2, a * t1 + c * t2, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        have e1 := h1.1 i; have e2 := h2.1 i
        simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
        nlinarith [mul_le_mul_of_nonneg_left e1 ha, mul_le_mul_of_nonneg_left e2 hc]
      · intro i
        have e1 := h1.2.1 i; have e2 := h2.2.1 i
        have : a • x1 + c • x2 - (a • y1 + c • y2) = a • (x1 - y1) + c • (x2 - y2) := by
          simp only [smul_sub]; abel
        rw [this]
        simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
        have hb : (1 - (a * t1 + c * t2)) * b i = a * ((1 - t1) * b i) + c * ((1 - t2) * b i) := by
          linear_combination -(b i) * hac
        rw [hb]
        nlinarith [mul_le_mul_of_nonneg_left e1 ha, mul_le_mul_of_nonneg_left e2 hc]
      · simp [h1.2.2.1, h2.2.2.1]
      · have := h1.2.2.2.1; have := h2.2.2.2.1
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination a * h1.2.2.2.1 + c * h2.2.2.2.1 + hac
      · nlinarith [h1.2.2.2.2.1, h2.2.2.2.2.1]
      · nlinarith [h1.2.2.2.2.2, h2.2.2.2.2.2]
  · rintro x ⟨y, t, h1, h2, h3, h4, h5, h6⟩
    rcases eq_or_lt_of_le h5 with ht0 | ht0
    · -- t = 0
      subst ht0
      apply subset_convexHull
      refine ⟨fun i => ?_, Or.inr (by linarith)⟩
      have e1 := h1 i; have e2 := h2 i
      have : A i ⬝ᵥ x = A i ⬝ᵥ (x - y) + A i ⬝ᵥ y := by rw [dotProduct_sub]; ring
      show b i ≤ A i ⬝ᵥ x
      rw [this]; simp at e1 e2; linarith
    rcases eq_or_lt_of_le h6 with ht1 | ht1
    · subst ht1
      apply subset_convexHull
      refine ⟨fun i => ?_, Or.inl (by linarith)⟩
      have e1 := h1 i; have e2 := h2 i
      have : A i ⬝ᵥ x = A i ⬝ᵥ (x - y) + A i ⬝ᵥ y := by rw [dotProduct_sub]; ring
      show b i ≤ A i ⬝ᵥ x
      rw [this]; simp at e1 e2; linarith
    · have hp : t⁻¹ • y ∈ Poly A b ∩ ZeroOneSet k := by
        refine ⟨fun i => ?_, Or.inl (by simp [h3])⟩
        show b i ≤ A i ⬝ᵥ (t⁻¹ • y)
        rw [dotProduct_smul, smul_eq_mul]
        rw [le_inv_mul_iff₀ ht0]; linarith [h1 i]
      have h1t : 0 < 1 - t := by linarith
      have hq : (1 - t)⁻¹ • (x - y) ∈ Poly A b ∩ ZeroOneSet k := by
        refine ⟨fun i => ?_, Or.inr ?_⟩
        · show b i ≤ A i ⬝ᵥ ((1 - t)⁻¹ • (x - y))
          rw [dotProduct_smul, smul_eq_mul]
          rw [le_inv_mul_iff₀ h1t]; linarith [h2 i]
        · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          rw [h4]; field_simp
      have := (convex_convexHull ℝ (Poly A b ∩ ZeroOneSet k)) (subset_convexHull ℝ _ hp)
        (subset_convexHull ℝ _ hq) h5 h1t.le (by ring)
      convert this using 1
      rw [smul_smul, smul_smul, mul_inv_cancel₀ ht0.ne', mul_inv_cancel₀ h1t.ne', one_smul,
        one_smul]
      abel

/-- `conv(S ∩ {x_k ∈ {0,1}})` is a polyhedron when `S` is one and `0 ≤ x_k ≤ 1` on `S`. -/
theorem conv_split_rep {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (k : Fin n)
    (hbox : ∀ x ∈ Poly A b, 0 ≤ x k ∧ x k ≤ 1) :
    ∃ (m' : ℕ) (A' : Matrix (Fin m') (Fin n) ℝ) (b' : Fin m' → ℝ),
      Poly A' b' = convexHull ℝ (Poly A b ∩ ZeroOneSet k) := by
  rw [conv_split_eq_lift A b k hbox]
  -- variables w : Fin (n+1) → ℝ encode (y, t)
  let yv : Fin n → (Fin (n + 1) → ℝ) := fun _ => 0
  let a : (Fin m ⊕ Fin m) ⊕ Fin 6 → Fin n → ℝ := fun r =>
    match r with
    | .inl (.inl _) => 0
    | .inl (.inr i) => A i
    | .inr 0 => 0
    | .inr 1 => 0
    | .inr 2 => Pi.single k 1
    | .inr 3 => -Pi.single k 1
    | .inr 4 => 0
    | .inr 5 => 0
  let c : (Fin m ⊕ Fin m) ⊕ Fin 6 → Fin (n + 1) → ℝ := fun r =>
    match r with
    | .inl (.inl i) => Fin.snoc (A i) (-b i)
    | .inl (.inr i) => Fin.snoc (-A i) (b i)
    | .inr 0 => Fin.snoc (Pi.single k 1) 0
    | .inr 1 => Fin.snoc (-Pi.single k 1) 0
    | .inr 2 => Fin.snoc (-Pi.single k 1) 1
    | .inr 3 => Fin.snoc (Pi.single k 1) (-1)
    | .inr 4 => Fin.snoc 0 1
    | .inr 5 => Fin.snoc 0 (-1)
  let β : (Fin m ⊕ Fin m) ⊕ Fin 6 → ℝ := fun r =>
    match r with
    | .inl (.inl _) => 0
    | .inl (.inr i) => b i
    | .inr 0 => 0
    | .inr 1 => 0
    | .inr 2 => 1
    | .inr 3 => -1
    | .inr 4 => 0
    | .inr 5 => -1
  obtain ⟨m', A', b', h⟩ := rep_of_proj a c β
  refine ⟨m', A', b', ?_⟩
  rw [h]
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨fun j => w (Fin.castSucc j), w (Fin.last n), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; have := hw (.inl (.inl i))
      simp only [a, c, β, snoc_dotProduct] at this
      simp at this; linarith
    · intro i; have := hw (.inl (.inr i))
      simp only [a, c, β, snoc_dotProduct] at this
      rw [dotProduct_sub]; simp [neg_dotProduct] at this; linarith
    · have h0 := hw (.inr 0); have h1 := hw (.inr 1)
      simp only [a, c, β, snoc_dotProduct] at h0 h1
      simp [single_dotProduct, neg_dotProduct] at h0 h1; linarith
    · have h0 := hw (.inr 2); have h1 := hw (.inr 3)
      simp only [a, c, β, snoc_dotProduct] at h0 h1
      simp [single_dotProduct, neg_dotProduct] at h0 h1; linarith
    · have h0 := hw (.inr 4)
      simp only [a, c, β, snoc_dotProduct] at h0
      simp at h0; linarith
    · have h0 := hw (.inr 5)
      simp only [a, c, β, snoc_dotProduct] at h0
      simp at h0; linarith
  · rintro ⟨y, t, h1, h2, h3, h4, h5, h6⟩
    refine ⟨Fin.snoc y t, fun r => ?_⟩
    rcases r with (i | i) | r
    · simp only [a, c, β, snoc_dotProduct]
      simp; linarith [h1 i]
    · simp only [a, c, β, snoc_dotProduct]
      have := h2 i; rw [dotProduct_sub] at this
      simp [neg_dotProduct]; linarith
    · fin_cases r <;>
        simp [a, c, β, snoc_dotProduct, single_dotProduct,
          neg_dotProduct] <;> linarith

end Disjunctive.CutCorrespondence


namespace Disjunctive.CutCorrespondence

open Set Finset

lemma inv_row_of_vecMul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsUnit M.det) (k : Fin n)
    (r : Fin n → ℝ) (hr : Matrix.vecMul r M = Pi.single k 1) (p : Fin n) : M⁻¹ k p = r p := by
  have : r = Matrix.vecMul (Pi.single k 1) M⁻¹ := by
    rw [← hr, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hM, Matrix.vecMul_one]
  rw [this, Matrix.single_vecMul]
  simp [Matrix.row]

/-- The simple disjunctive cut of a basis whose `k`-th row of `Â⁻¹` is `r`. -/
lemma simpleDisjCut_of_r {M n : ℕ} (A : Matrix (Fin M) (Fin n) ℝ) (b : Fin M → ℝ) (k : Fin n)
    (ι : Fin n → Fin M) (hdet : IsUnit (Ahat A ι).det) (r : Fin n → ℝ)
    (hr : Matrix.vecMul r (Ahat A ι) = Pi.single k 1) :
    Abar0 A b ι k = r ⬝ᵥ Bhat b ι ∧
      SimpleDisjCutSet A b ι k = {x | (r ⬝ᵥ Bhat b ι) * (1 - r ⬝ᵥ Bhat b ι) ≤
        ∑ p, max (-r p * (1 - r ⬝ᵥ Bhat b ι)) (r p * (r ⬝ᵥ Bhat b ι)) *
          (A (ι p) ⬝ᵥ x - b (ι p))} := by
  have hinv := inv_row_of_vecMul _ hdet k r hr
  have h0 : Abar0 A b ι k = r ⬝ᵥ Bhat b ι := by
    simp only [Abar0, Matrix.mulVec, dotProduct, hinv]
  refine ⟨h0, ?_⟩
  ext x
  simp only [SimpleDisjCutSet, Set.mem_ofPred_eq, Pi0, PiCoef, Pi1, Pi2, Abar, hinv, h0, Surplus]
  constructor <;> intro h <;> convert h using 3 <;> ring_nf

lemma closure_sub_of_basis {M n : ℕ} (A : Matrix (Fin M) (Fin n) ℝ) (b : Fin M → ℝ) (k : Fin n)
    (ι : Fin n → Fin M) (hinj : Function.Injective ι) (hdet : IsUnit (Ahat A ι).det)
    (h0 : 0 < Abar0 A b ι k) (h1 : Abar0 A b ι k < 1) :
    SimpleDisjClosure A b k ⊆ SimpleDisjCutSet A b ι k := by
  intro x hx
  simp only [SimpleDisjClosure, Set.mem_inter_iff, Set.mem_iInter] at hx
  exact hx.2 ι hinj hdet h0 h1

lemma isUnit_det_of_vecMul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ v : Fin n → ℝ, Matrix.vecMul v M = 0 → v = 0) : IsUnit M.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.vecMul_injective_iff_isUnit]
  intro v w hvw
  have hvw' : Matrix.vecMul v M = Matrix.vecMul w M := hvw
  have := h (v - w) (by rw [Matrix.sub_vecMul, hvw', sub_self])
  exact sub_eq_zero.mp this

/-- Rows of the basis used for the nondegenerate construction. -/
noncomputable def ndRows {n : ℕ} (k j0 : Fin n) (a1 a2 : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun p => if p = k then a1 else if p = j0 then a2 else Pi.single p 1

lemma ndRows_vecMul {n : ℕ} (k j0 : Fin n) (hkj : j0 ≠ k) (a1 a2 v : Fin n → ℝ) :
    Matrix.vecMul v (ndRows k j0 a1 a2) =
      v + v k • (a1 - Pi.single k 1) + v j0 • (a2 - Pi.single j0 1) := by
  ext q
  simp only [Matrix.vecMul, dotProduct, ndRows, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.sub_apply]
  have : ∀ p, v p * (if p = k then a1 else if p = j0 then a2 else Pi.single p (1:ℝ)) q =
      v p * (Pi.single p (1:ℝ) : Fin n → ℝ) q +
        (if p = k then v k * (a1 q - (Pi.single k (1:ℝ) : Fin n → ℝ) q) else 0) +
        (if p = j0 then v j0 * (a2 q - (Pi.single j0 (1:ℝ) : Fin n → ℝ) q) else 0) := by
    intro p
    by_cases hp : p = k
    · subst hp; simp [Ne.symm hkj]; ring
    · by_cases hp' : p = j0
      · subst hp'; simp [hp]; ring
      · simp [hp, hp']
  rw [Finset.sum_congr rfl fun p _ => this p, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp [Pi.single_apply]

/-- Nondegenerate construction: rows `g + u0 e_k ≥ h`, `g - v0 e_k ≥ h - v0` and `e_j ≥ 0`
yield the simple disjunctive cut `g x ≥ h`. -/
lemma simpleDisj_nondeg {M n : ℕ} (A : Matrix (Fin M) (Fin n) ℝ) (b : Fin M → ℝ) (k j0 : Fin n)
    (hkj : j0 ≠ k) (g : Fin n → ℝ) (h u0 v0 : ℝ) (hu0 : 0 < u0) (hv0 : 0 < v0) (hg : g j0 ≠ 0)
    (i1 i2 : Fin M) (hi1 : A i1 = g + u0 • Pi.single k 1) (hb1 : b i1 = h)
    (hi2 : A i2 = g - v0 • Pi.single k 1) (hb2 : b i2 = h - v0)
    (hunit : ∀ j, ∃ ρ, A ρ = Pi.single j 1 ∧ b ρ = 0) :
    SimpleDisjClosure A b k ⊆ {x | h ≤ g ⬝ᵥ x} := by
  classical
  choose ρ hρA hρb using hunit
  set a1 := g + u0 • Pi.single k (1:ℝ)
  set a2 := g - v0 • Pi.single k (1:ℝ)
  let ι : Fin n → Fin M := fun p => if p = k then i1 else if p = j0 then i2 else ρ p
  have hA : Ahat A ι = ndRows k j0 a1 a2 := by
    ext p q
    simp only [Ahat, ndRows, ι]
    split_ifs <;> simp [hi1, hi2, hρA, a1, a2]
  have hAk : ∀ p, A (ι p) = ndRows k j0 a1 a2 p := fun p => by
    rw [← hA]; rfl
  have hj0 : a1 j0 = g j0 := by simp [a1, Pi.single_apply, hkj]
  have hj0' : a2 j0 = g j0 := by simp [a2, Pi.single_apply, hkj]
  have hkk : a1 k = g k + u0 := by simp [a1]
  have hkk' : a2 k = g k - v0 := by simp [a2]
  have hnd : ∀ v : Fin n → ℝ, Matrix.vecMul v (ndRows k j0 a1 a2) = 0 → v = 0 := by
    intro v hv
    rw [ndRows_vecMul k j0 hkj] at hv
    have eq := fun q => congrFun hv q
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at eq
    have e1 := eq j0
    have e2 := eq k
    rw [hj0, hj0'] at e1; rw [hkk, hkk'] at e2
    simp [Pi.single_apply, hkj, Ne.symm hkj] at e1 e2
    have hvk : v k = -v j0 := by
      have : (v k + v j0) * g j0 = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · exact absurd h' hg
    have hvj : v j0 = 0 := by
      have : v j0 * (u0 + v0) = 0 := by rw [hvk] at e2; linarith
      rcases mul_eq_zero.mp this with h' | h'
      · exact h'
      · linarith
    have hvk0 : v k = 0 := by rw [hvk, hvj, neg_zero]
    ext q
    have := eq q
    rw [hvk0, hvj] at this
    simpa using this
  have hinj : Function.Injective ι := by
    intro p q e
    have hrow : ndRows k j0 a1 a2 p = ndRows k j0 a1 a2 q := by rw [← hAk, ← hAk, e]
    by_contra hpq
    have := hnd (Pi.single p 1 - Pi.single q 1) (by
      rw [Matrix.sub_vecMul, Matrix.single_vecMul, Matrix.single_vecMul]
      ext c; simp [Matrix.row, hrow])
    have := congrFun this p
    simp [Pi.single_apply, hpq] at this
  have hdet : IsUnit (Ahat A ι).det := by
    rw [hA]; exact isUnit_det_of_vecMul _ hnd
  -- the row vector r
  set U := u0 + v0 with hU
  have hUpos : 0 < U := by linarith
  let r : Fin n → ℝ := U⁻¹ • (Pi.single k 1 - Pi.single j0 1)
  have hr : Matrix.vecMul r (Ahat A ι) = Pi.single k 1 := by
    rw [hA, ndRows_vecMul k j0 hkj]
    ext q
    simp only [r, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    simp [Pi.single_apply, hkj, Ne.symm hkj, a1, a2]
    by_cases hq : q = k
    · subst hq; simp [Ne.symm hkj]; field_simp; ring
    · by_cases hq' : q = j0
      · subst hq'; simp [hq]; field_simp; ring
      · simp [hq, hq']
  obtain ⟨hab0, hcut⟩ := simpleDisjCut_of_r A b k ι hdet r hr
  have hrb : r ⬝ᵥ Bhat b ι = v0 / U := by
    simp only [r, dotProduct, Bhat, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [Finset.sum_eq_add (a := k) (b := j0) (Ne.symm hkj)]
    · simp [ι, hb1, hb2, hkj, Ne.symm hkj]; field_simp; ring
    · intro c _ hc; simp [Pi.single_apply, hc.1, hc.2]
    · simp
    · simp
  have hf0 : 0 < Abar0 A b ι k := by rw [hab0, hrb]; positivity
  have hf1 : Abar0 A b ι k < 1 := by
    rw [hab0, hrb, div_lt_one hUpos]; linarith
  intro x hx
  have hxc := closure_sub_of_basis A b k ι hinj hdet hf0 hf1 hx
  rw [hcut] at hxc
  simp only [Set.mem_ofPred_eq] at hxc ⊢
  rw [hrb] at hxc
  rw [Finset.sum_eq_add (a := k) (b := j0) (Ne.symm hkj)] at hxc
  · have hrk : r k = U⁻¹ := by simp [r, Ne.symm hkj]
    have hrj : r j0 = -U⁻¹ := by simp [r, hkj]
    have hAι1 : A (ι k) = a1 := by simp [ι, hi1]
    have hAι2 : A (ι j0) = a2 := by simp [ι, hkj, hi2]
    have hbι1 : b (ι k) = h := by simp [ι, hb1]
    have hbι2 : b (ι j0) = h - v0 := by simp [ι, hkj, hb2]
    rw [hrk, hrj, hAι1, hAι2, hbι1, hbι2] at hxc
    have hd1 : a1 ⬝ᵥ x = g ⬝ᵥ x + u0 * x k := by
      simp [a1, dotProduct_add, dotProduct_smul, single_dotProduct]
    have hd2 : a2 ⬝ᵥ x = g ⬝ᵥ x - v0 * x k := by
      simp [a2, dotProduct_sub, dotProduct_smul, single_dotProduct]
    rw [hd1, hd2] at hxc
    have hm1 : max (-U⁻¹ * (1 - v0 / U)) (U⁻¹ * (v0 / U)) = v0 / U ^ 2 := by
      rw [max_eq_right]
      · field_simp
      · have : 0 ≤ 1 - v0 / U := by rw [sub_nonneg, div_le_one hUpos]; linarith
        have : 0 < U⁻¹ := inv_pos.mpr hUpos
        nlinarith [div_pos hv0 hUpos]
    have hm2 : max (- -U⁻¹ * (1 - v0 / U)) (-U⁻¹ * (v0 / U)) = u0 / U ^ 2 := by
      rw [max_eq_left]
      · field_simp; ring
      · have : 0 ≤ 1 - v0 / U := by rw [sub_nonneg, div_le_one hUpos]; linarith
        have : 0 < U⁻¹ := inv_pos.mpr hUpos
        nlinarith [div_pos hv0 hUpos]
    rw [hm1, hm2] at hxc
    have hU2 : 0 < U ^ 2 := by positivity
    have key : v0 / U * (1 - v0 / U) * U ^ 2 ≤
        (v0 / U ^ 2 * (g ⬝ᵥ x + u0 * x k - h) + u0 / U ^ 2 * (g ⬝ᵥ x - v0 * x k - (h - v0))) *
          U ^ 2 := by
      have := mul_le_mul_of_nonneg_right hxc hU2.le
      convert this using 2
    have e1 : v0 / U * (1 - v0 / U) * U ^ 2 = v0 * u0 := by field_simp; ring
    have e2 : (v0 / U ^ 2 * (g ⬝ᵥ x + u0 * x k - h) + u0 / U ^ 2 * (g ⬝ᵥ x - v0 * x k - (h - v0))) *
        U ^ 2 = U * (g ⬝ᵥ x - h) + u0 * v0 := by field_simp; ring
    rw [e1, e2] at key
    nlinarith
  · intro c _ hc
    simp [r, Pi.single_apply, hc.1, hc.2]
  · simp
  · simp

end Disjunctive.CutCorrespondence


namespace Disjunctive.CutCorrespondence

open Set Finset

lemma inj_of_rows {M n : ℕ} (A : Matrix (Fin M) (Fin n) ℝ) (ι : Fin n → Fin M)
    (hnd : ∀ v : Fin n → ℝ, Matrix.vecMul v (Ahat A ι) = 0 → v = 0) : Function.Injective ι := by
  intro p q e
  by_contra hpq
  have := hnd (Pi.single p 1 - Pi.single q 1) (by
    rw [Matrix.sub_vecMul, Matrix.single_vecMul, Matrix.single_vecMul]
    ext c; simp [Matrix.row, Ahat, e])
  have := congrFun this p
  simp [Pi.single_apply, hpq] at this

/-- Degenerate construction: the row `x_k ≥ ε` (with `0<ε<1`) and the rows `x_j ≥ 0` yield
the simple disjunctive cut `x_k ≥ 1`. -/
lemma simpleDisj_ge1 {M n : ℕ} (A : Matrix (Fin M) (Fin n) ℝ) (b : Fin M → ℝ) (k : Fin n)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (i0 : Fin M) (hi0 : A i0 = Pi.single k 1)
    (hb0 : b i0 = ε) (hunit : ∀ j, ∃ ρ, A ρ = Pi.single j 1 ∧ b ρ = 0) :
    SimpleDisjClosure A b k ⊆ {x | 1 ≤ x k} := by
  classical
  choose ρ hρA hρb using hunit
  let ι : Fin n → Fin M := fun p => if p = k then i0 else ρ p
  have hA : Ahat A ι = 1 := by
    ext p q
    simp only [Ahat, ι, Matrix.one_apply]
    split_ifs with h1 h2 h2 <;> subst_vars <;> simp [hi0, hρA, Pi.single_apply, *]
    all_goals (rw [Pi.single_apply]; simp [Ne.symm ‹_›])
  have hnd : ∀ v : Fin n → ℝ, Matrix.vecMul v (Ahat A ι) = 0 → v = 0 := by
    intro v hv; rwa [hA, Matrix.vecMul_one] at hv
  have hinj := inj_of_rows A ι hnd
  have hdet : IsUnit (Ahat A ι).det := isUnit_det_of_vecMul _ hnd
  have hr : Matrix.vecMul (Pi.single k 1) (Ahat A ι) = Pi.single k 1 := by
    rw [hA, Matrix.vecMul_one]
  obtain ⟨hab0, hcut⟩ := simpleDisjCut_of_r A b k ι hdet _ hr
  have hrb : (Pi.single k 1 : Fin n → ℝ) ⬝ᵥ Bhat b ι = ε := by
    simp [single_dotProduct, Bhat, ι, hb0]
  intro x hx
  have hxc := closure_sub_of_basis A b k ι hinj hdet (by rw [hab0, hrb]; exact hε0)
    (by rw [hab0, hrb]; exact hε1) hx
  rw [hcut] at hxc
  simp only [Set.mem_ofPred_eq] at hxc ⊢
  rw [hrb, Finset.sum_eq_single k] at hxc
  · simp only [Pi.single_eq_same, ι, if_true, hi0, hb0, single_dotProduct, one_mul] at hxc
    rw [max_eq_right (by nlinarith)] at hxc
    nlinarith
  · intro p _ hp; simp [Pi.single_apply, hp]
  · simp

/-- Degenerate construction: the row `-x_k ≥ -(1-ε)` and the rows `x_j ≥ 0` yield the simple
disjunctive cut `x_k ≤ 0`. -/
lemma simpleDisj_le0 {M n : ℕ} (A : Matrix (Fin M) (Fin n) ℝ) (b : Fin M → ℝ) (k : Fin n)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (i0 : Fin M) (hi0 : A i0 = -Pi.single k 1)
    (hb0 : b i0 = -(1 - ε)) (hunit : ∀ j, ∃ ρ, A ρ = Pi.single j 1 ∧ b ρ = 0) :
    SimpleDisjClosure A b k ⊆ {x | x k ≤ 0} := by
  classical
  choose ρ hρA hρb using hunit
  let ι : Fin n → Fin M := fun p => if p = k then i0 else ρ p
  have hAι : ∀ p, A (ι p) = if p = k then -Pi.single k 1 else Pi.single p 1 := by
    intro p; by_cases hp : p = k <;> simp [ι, hp, hi0, hρA]
  have hvm : ∀ v : Fin n → ℝ, Matrix.vecMul v (Ahat A ι) = v - (2 * v k) • Pi.single k 1 := by
    intro v; ext q
    simp only [Matrix.vecMul, dotProduct, Ahat, hAι, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single q]
    · by_cases hq : q = k
      · subst hq; simp; ring
      · simp [hq, Pi.single_apply]
    · intro p _ hp
      by_cases hpk : p = k
      · subst hpk; simp [Pi.single_apply, Ne.symm hp]
      · simp [hpk, Pi.single_apply, Ne.symm hp]
    · simp
  have hnd : ∀ v : Fin n → ℝ, Matrix.vecMul v (Ahat A ι) = 0 → v = 0 := by
    intro v hv
    rw [hvm] at hv
    have hk := congrFun hv k
    simp at hk
    ext q
    have := congrFun hv q
    by_cases hq : q = k
    · subst hq; simp at this; simp; linarith
    · simp [hq, Pi.single_apply] at this; simpa using this
  have hinj := inj_of_rows A ι hnd
  have hdet : IsUnit (Ahat A ι).det := isUnit_det_of_vecMul _ hnd
  have hr : Matrix.vecMul (-Pi.single k 1) (Ahat A ι) = Pi.single k 1 := by
    rw [hvm]; ext q; by_cases hq : q = k
    · subst hq; simp; ring
    · simp [hq, Pi.single_apply]
  obtain ⟨hab0, hcut⟩ := simpleDisjCut_of_r A b k ι hdet _ hr
  have hrb : (-Pi.single k 1 : Fin n → ℝ) ⬝ᵥ Bhat b ι = 1 - ε := by
    simp [neg_dotProduct, single_dotProduct, Bhat, ι, hb0]
  intro x hx
  have hxc := closure_sub_of_basis A b k ι hinj hdet (by rw [hab0, hrb]; linarith)
    (by rw [hab0, hrb]; linarith) hx
  rw [hcut] at hxc
  simp only [Set.mem_ofPred_eq] at hxc ⊢
  rw [hrb, Finset.sum_eq_single k] at hxc
  · simp only [Pi.neg_apply, Pi.single_eq_same, ι, if_true, hi0, hb0, neg_dotProduct,
      single_dotProduct, one_mul] at hxc
    rw [max_eq_left (by nlinarith)] at hxc
    nlinarith
  · intro p _ hp; simp [Pi.single_apply, hp]
  · simp

open Classical in
lemma sum_split_nonneg {n : ℕ} {M : Type*} [Fintype M] (A : Matrix M (Fin n) ℝ) (b : M → ℝ)
    (u : M → ℝ) (hu : 0 ≤ u) (i : Fin n) :
    Alpha1 A b u i ≤ ∑ ρ, u ρ * A ρ i := by
  unfold Alpha1
  apply Finset.sum_le_sum
  intro ρ _
  split_ifs with h
  · rw [h.1]; simp; exact hu ρ
  · exact le_rfl

lemma alpha2_le {n : ℕ} {M : Type*} [Fintype M] (A : Matrix M (Fin n) ℝ) (b : M → ℝ)
    (v : M → ℝ) (hv : 0 ≤ v) (i : Fin n) :
    Alpha2 A b v i ≤ ∑ ρ, v ρ * A ρ i := sum_split_nonneg A b v hv i

/-- Theorem 6.4's strengthened coefficients never exceed the unstrengthened ones. -/
lemma gamma_le_alpha {n : ℕ} {M : Type*} [Fintype M] (A : Matrix M (Fin n) ℝ) (b : M → ℝ)
    (k : Fin n) (Nprime : Finset (Fin n)) (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ)
    (v0 β : ℝ) (hf : IsCGLPKFeasible A b k α u u0 v v0 β) (hu0 : 0 < u0) (hv0 : 0 < v0)
    (i : Fin n) : Gamma A b u u0 v v0 Nprime α i ≤ α i := by
  obtain ⟨e1, e2, -, -, -, hu, hv, -, -⟩ := hf
  unfold Gamma
  split_ifs with hi
  swap; · exact le_rfl
  set t : ℤ := if i = k then -1 else 0 with ht
  have ha1 : Alpha1 A b u i + u0 * t ≤ α i := by
    have := e1 i; have := sum_split_nonneg A b u hu i
    by_cases hik : i = k <;> simp [ht, hik] at * <;> linarith
  have ha2 : Alpha2 A b v i - v0 * t ≤ α i := by
    have := e2 i; have := alpha2_le A b v hv i
    by_cases hik : i = k <;> simp [ht, hik] at * <;> linarith
  set mm := MBar A b u u0 v v0 i
  rcases le_or_gt (⌈mm⌉) t with h | h
  · refine (min_le_left _ _).trans (le_trans ?_ ha1)
    have : (⌈mm⌉ : ℝ) ≤ t := by exact_mod_cast h
    nlinarith
  · refine (min_le_right _ _).trans (le_trans ?_ ha2)
    have : t ≤ ⌊mm⌋ := by
      have := Int.ceil_le_floor_add_one mm
      omega
    have : (t : ℝ) ≤ ⌊mm⌋ := by exact_mod_cast this
    nlinarith

/-- Strengthened L&P cut realizing `g x ≥ h` from the rows `g + u0 e_k ≥ h`,
`g - v0 e_k ≥ h - v0`. -/
lemma strengthened_cut {M n : ℕ} (A : Matrix (Fin M) (Fin n) ℝ) (b : Fin M → ℝ) (k : Fin n)
    (Nprime : Finset (Fin n)) (g : Fin n → ℝ) (h u0 v0 : ℝ) (hu0 : 0 < u0) (hv0 : 0 < v0)
    (i1 i2 : Fin M) (hi1 : A i1 = g + u0 • Pi.single k 1) (hb1 : b i1 = h)
    (hi2 : A i2 = g - v0 • Pi.single k 1) (hb2 : b i2 = h - v0)
    (hpos : ∀ x ∈ Poly A b, ∀ j, 0 ≤ x j) :
    StrengthenedLPClosure A b k Nprime ⊆ {x | h ≤ g ⬝ᵥ x} := by
  classical
  set N := 2 + u0 + v0 with hN
  have hNpos : 0 < N := by linarith
  have hfeas : IsCGLPKFeasible A b k (N⁻¹ • g) (Pi.single i1 N⁻¹) (u0 / N) (Pi.single i2 N⁻¹)
      (v0 / N) (h / N) := by
    have s1 : ∀ i, ∑ ρ, (Pi.single i1 N⁻¹ : Fin M → ℝ) ρ * A ρ i = N⁻¹ * A i1 i := by
      intro i; rw [Finset.sum_eq_single i1] <;> simp (config := {contextual := true})
    have s2 : ∀ i, ∑ ρ, (Pi.single i2 N⁻¹ : Fin M → ℝ) ρ * A ρ i = N⁻¹ * A i2 i := by
      intro i; rw [Finset.sum_eq_single i2] <;> simp (config := {contextual := true})
    have s3 : ∑ ρ, (Pi.single i1 N⁻¹ : Fin M → ℝ) ρ * b ρ = N⁻¹ * b i1 := by
      rw [Finset.sum_eq_single i1] <;> simp (config := {contextual := true})
    have s4 : ∑ ρ, (Pi.single i2 N⁻¹ : Fin M → ℝ) ρ * b ρ = N⁻¹ * b i2 := by
      rw [Finset.sum_eq_single i2] <;> simp (config := {contextual := true})
    have s5 : ∀ i0 : Fin M, ∑ ρ, (Pi.single i0 N⁻¹ : Fin M → ℝ) ρ = N⁻¹ := by
      intro i0; rw [Finset.sum_eq_single i0] <;> simp (config := {contextual := true})
    refine ⟨fun i => ?_, fun i => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [s1, hi1]; by_cases hik : i = k <;> simp [hik] <;> field_simp <;> ring
    · rw [s2, hi2]; by_cases hik : i = k <;> simp [hik] <;> field_simp <;> ring
    · rw [s3, hb1]; field_simp; ring
    · rw [s4, hb2]; field_simp; ring
    · rw [s5, s5]; field_simp; ring
    · intro ρ; by_cases h' : ρ = i1 <;> simp [Pi.single_apply, h', hNpos.le]
    · intro ρ; by_cases h' : ρ = i2 <;> simp [Pi.single_apply, h', hNpos.le]
    · positivity
    · positivity
  intro x hx
  simp only [StrengthenedLPClosure, Set.mem_inter_iff, Set.mem_iInter] at hx
  have hcut := hx.2 _ _ _ _ _ _ hfeas (by positivity) (by positivity)
  simp only [Set.mem_ofPred_eq] at hcut ⊢
  have hle : Gamma A b (Pi.single i1 N⁻¹) (u0 / N) (Pi.single i2 N⁻¹) (v0 / N) Nprime
      (N⁻¹ • g) ⬝ᵥ x ≤ (N⁻¹ • g) ⬝ᵥ x := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right
      (gamma_le_alpha A b k Nprime _ _ _ _ _ _ hfeas (by positivity) (by positivity) i)
      (hpos x hx.1 i)
  have := hcut.trans hle
  rw [smul_dotProduct, smul_eq_mul, div_eq_inv_mul] at this
  have hNi : 0 < N⁻¹ := inv_pos.mpr hNpos
  nlinarith [mul_le_mul_of_nonneg_left this hNpos.le, mul_inv_cancel₀ hNpos.ne']

end Disjunctive.CutCorrespondence


namespace Disjunctive.CutCorrespondence

open Set Finset

/-- Affine Farkas consequence: an inequality valid on `S ∩ {c x ≤ d}` (nonempty) is implied on
`S` by adding a nonnegative multiple of `d - c x`. -/
lemma farkas_side {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (d : ℝ) (g : Fin n → ℝ) (h : ℝ) (hne : ∃ x ∈ Poly A b, c ⬝ᵥ x ≤ d)
    (hval : ∀ x ∈ Poly A b, c ⬝ᵥ x ≤ d → h ≤ g ⬝ᵥ x) :
    ∃ μ : ℝ, 0 ≤ μ ∧ ∀ x ∈ Poly A b, h + μ * (d - c ⬝ᵥ x) ≤ g ⬝ᵥ x := by
  classical
  let Mt : Matrix (Fin m ⊕ Unit) (Fin n) ℝ := fun r => Sum.elim (fun i => -A i) (fun _ => c) r
  let rhs : Fin m ⊕ Unit → ℝ := Sum.elim (fun i => -b i) (fun _ => d)
  have hMx : ∀ x, Mt.mulVec x ≤ rhs ↔ x ∈ Poly A b ∧ c ⬝ᵥ x ≤ d := by
    intro x
    constructor
    · intro hx
      refine ⟨fun i => ?_, ?_⟩
      · have := hx (Sum.inl i)
        simp only [Mt, rhs, Matrix.mulVec, Sum.elim_inl, neg_dotProduct] at this
        show b i ≤ A i ⬝ᵥ x; linarith
      · have := hx (Sum.inr ())
        simpa [Mt, rhs, Matrix.mulVec] using this
    · rintro ⟨hx, hc⟩ r
      rcases r with i | _
      · have := poly_mem hx i
        simp only [Mt, rhs, Matrix.mulVec, Sum.elim_inl, neg_dotProduct]; linarith
      · simpa [Mt, rhs, Matrix.mulVec] using hc
  obtain ⟨x0, hx0, hcx0⟩ := hne
  have hfeas : ∃ x, Mt.mulVec x ≤ rhs := ⟨x0, (hMx x0).mpr ⟨hx0, hcx0⟩⟩
  have himp : ∀ x, Mt.mulVec x ≤ rhs → (-g) ⬝ᵥ x ≤ -h := by
    intro x hx
    obtain ⟨h1, h2⟩ := (hMx x).mp hx
    have := hval x h1 h2
    rw [neg_dotProduct]; linarith
  obtain ⟨p, hp0, hpM, hpb⟩ :=
    (LinearOptimization.farkas_inequality_form_fintype Mt rhs (-g) (-h) hfeas).mp himp
  refine ⟨p (Sum.inr ()), hp0 (Sum.inr ()), fun x hx => ?_⟩
  have key : (-g) ⬝ᵥ x = p ⬝ᵥ Mt.mulVec x := by
    rw [← hpM, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
  have e1 : p ⬝ᵥ Mt.mulVec x = -∑ i, p (Sum.inl i) * (A i ⬝ᵥ x) + p (Sum.inr ()) * (c ⬝ᵥ x) := by
    simp only [dotProduct, Fintype.sum_sum_type, Mt, Matrix.mulVec, Sum.elim_inl, Sum.elim_inr,
      Finset.univ_unique, Finset.sum_singleton, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib,
      mul_neg]
  have e2 : p ⬝ᵥ rhs = -∑ i, p (Sum.inl i) * b i + p (Sum.inr ()) * d := by
    simp only [dotProduct, Fintype.sum_sum_type, rhs, Sum.elim_inl, Sum.elim_inr,
      Finset.univ_unique, Finset.sum_singleton, mul_neg, Finset.sum_neg_distrib]
  have hsum : ∑ i, p (Sum.inl i) * b i ≤ ∑ i, p (Sum.inl i) * (A i ⬝ᵥ x) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (poly_mem hx i) (hp0 _)
  rw [neg_dotProduct, e1] at key
  rw [e2] at hpb
  nlinarith

lemma lp_min_pos {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (L : ℝ) (hne : (Poly A b).Nonempty) (hlow : ∀ x ∈ Poly A b, L ≤ c ⬝ᵥ x) :
    ∃ xs ∈ Poly A b, ∀ x ∈ Poly A b, c ⬝ᵥ xs ≤ c ⬝ᵥ x := by
  have hP : Poly A b = LinearOptimization.polyhedron A b := rfl
  rw [hP] at hne hlow ⊢
  rcases LinearOptimization.lp_attains_or_unbounded A b c hne with h | ⟨xs, hxs, hopt⟩
  · exfalso
    have : ((L : ℝ) : EReal) ≤ LinearOptimization.lpValue c (LinearOptimization.polyhedron A b) :=
      le_iInf₂ fun x hx => by exact_mod_cast hlow x hx
    rw [h] at this
    exact absurd this (by simp)
  · exact ⟨xs, hxs, hopt⟩

lemma eps_of_pos {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (k : Fin n)
    (hne : (Poly A b).Nonempty) (hpos : ∀ x ∈ Poly A b, 0 < x k) :
    ∃ ε, 0 < ε ∧ ∀ x ∈ Poly A b, ε ≤ x k := by
  obtain ⟨xs, hxs, hopt⟩ := lp_min_pos A b (Pi.single k 1) 0 hne
    (fun x hx => by rw [single_dotProduct, one_mul]; exact (hpos x hx).le)
  refine ⟨xs k, hpos xs hxs, fun x hx => ?_⟩
  have := hopt x hx
  simpa [single_dotProduct] using this

lemma eps_of_lt1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (k : Fin n)
    (hne : (Poly A b).Nonempty) (hlt : ∀ x ∈ Poly A b, x k < 1) :
    ∃ ε, 0 < ε ∧ ∀ x ∈ Poly A b, x k ≤ 1 - ε := by
  obtain ⟨xs, hxs, hopt⟩ := lp_min_pos A b (-Pi.single k 1) (-1) hne
    (fun x hx => by rw [neg_dotProduct, single_dotProduct, one_mul]; linarith [hlt x hx])
  refine ⟨1 - xs k, by linarith [hlt xs hxs], fun x hx => ?_⟩
  have := hopt x hx
  simp [neg_dotProduct, single_dotProduct] at this
  linarith

/-- Adding finitely many valid rows and all rows `x_j ≥ 0` to a representation. -/
lemma build_rep {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) {ι : Type}
    [Fintype ι] (E : ι → (Fin n → ℝ) × ℝ) (hE : ∀ i, ∀ x ∈ Poly A b, (E i).2 ≤ (E i).1 ⬝ᵥ x)
    (hpos : ∀ x ∈ Poly A b, ∀ j, 0 ≤ x j) :
    ∃ (M : ℕ) (A' : Matrix (Fin M) (Fin n) ℝ) (b' : Fin M → ℝ), Poly A' b' = Poly A b ∧
      (∀ i, ∃ ρ, A' ρ = (E i).1 ∧ b' ρ = (E i).2) ∧
      (∀ j, ∃ ρ, A' ρ = Pi.single j 1 ∧ b' ρ = 0) := by
  classical
  let T := Fin m ⊕ (Fin n ⊕ ι)
  let row : T → (Fin n → ℝ) × ℝ := fun t =>
    Sum.elim (fun i => (A i, b i)) (Sum.elim (fun j => (Pi.single j 1, 0)) E) t
  let e := Fintype.equivFin T
  refine ⟨Fintype.card T, fun r => (row (e.symm r)).1, fun r => (row (e.symm r)).2, ?_, ?_, ?_⟩
  · ext x
    change (∀ r, (row (e.symm r)).2 ≤ (row (e.symm r)).1 ⬝ᵥ x) ↔ x ∈ Poly A b
    constructor
    · intro hx i
      have := hx (e (Sum.inl i))
      show b i ≤ A i ⬝ᵥ x
      simpa [row] using this
    · intro hx r
      rcases h : e.symm r with i | j | i
      · simpa [row] using poly_mem hx i
      · simpa [row, single_dotProduct] using hpos x hx j
      · simpa [row] using hE i x hx
  · intro i; exact ⟨e (Sum.inr (Sum.inr i)), by simp [row], by simp [row]⟩
  · intro j; exact ⟨e (Sum.inr (Sum.inl j)), by simp [row], by simp [row]⟩

end Disjunctive.CutCorrespondence


namespace Disjunctive.CutCorrespondence

open Set Finset

lemma simpleDisjClosure_sub_poly {M n : ℕ} (A : Matrix (Fin M) (Fin n) ℝ) (b : Fin M → ℝ)
    (k : Fin n) : SimpleDisjClosure A b k ⊆ Poly A b := Set.inter_subset_left

lemma strengthenedLPClosure_sub_poly {M n : ℕ} (A : Matrix (Fin M) (Fin n) ℝ) (b : Fin M → ℝ)
    (k : Fin n) (Nprime : Finset (Fin n)) : StrengthenedLPClosure A b k Nprime ⊆ Poly A b :=
  Set.inter_subset_left

/-- Upper bound: some representation of `S` has simple disjunctive and strengthened L&P
closures inside `conv(S ∩ {x_k ∈ {0,1}})`. -/
theorem upper_rep {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (k : Fin n)
    (hpos : ∀ x ∈ Poly A b, ∀ j, 0 ≤ x j) (hle1 : ∀ x ∈ Poly A b, x k ≤ 1) :
    ∃ (M : ℕ) (A' : Matrix (Fin M) (Fin n) ℝ) (b' : Fin M → ℝ), Poly A' b' = Poly A b ∧
      SimpleDisjClosure A' b' k ⊆ convexHull ℝ (Poly A b ∩ ZeroOneSet k) ∧
      ∀ Nprime : Finset (Fin n),
        StrengthenedLPClosure A' b' k Nprime ⊆ convexHull ℝ (Poly A b ∩ ZeroOneSet k) := by
  classical
  have hSQ : (Poly A b) ∩ ZeroOneSet k ⊆ (convexHull ℝ (Poly A b ∩ ZeroOneSet k)) := subset_convexHull ℝ _
  rcases Set.eq_empty_or_nonempty (Poly A b) with hemp | hne
  · refine ⟨m, A, b, rfl, ?_, fun N' => ?_⟩
    · exact (simpleDisjClosure_sub_poly A b k).trans (by rw [hemp]; exact empty_subset _)
    · exact (strengthenedLPClosure_sub_poly A b k N').trans
        (by rw [hemp]; exact empty_subset _)
  by_cases h0 : ∃ x ∈ (Poly A b), x k ≤ 0
  · by_cases h1 : ∃ x ∈ (Poly A b), 1 ≤ x k
    · -- main case: both faces nonempty
      obtain ⟨mQ, G, hQ, hGQ⟩ := conv_split_rep A b k (fun x hx => ⟨hpos x hx k, hle1 x hx⟩)
      have hvalQ : ∀ q, ∀ x ∈ (Poly A b) ∩ ZeroOneSet k, hQ q ≤ G q ⬝ᵥ x := by
        intro q x hx
        have : x ∈ Poly G hQ := by rw [hGQ]; exact hSQ hx
        exact poly_mem this q
      have hF0 : ∀ q, ∃ μ : ℝ, 0 ≤ μ ∧ ∀ x ∈ (Poly A b), hQ q + μ * (0 - Pi.single k 1 ⬝ᵥ x) ≤ G q ⬝ᵥ x := by
        intro q
        apply farkas_side A b (Pi.single k 1) 0 (G q) (hQ q)
        · obtain ⟨x, hx, hxk⟩ := h0; exact ⟨x, hx, by simpa [single_dotProduct] using hxk⟩
        · intro x hx hxk
          apply hvalQ q x ⟨hx, Or.inl ?_⟩
          have := hpos x hx k
          simp [single_dotProduct] at hxk; linarith
      have hF1 : ∀ q, ∃ μ : ℝ, 0 ≤ μ ∧
          ∀ x ∈ (Poly A b), hQ q + μ * (-1 - (-Pi.single k 1) ⬝ᵥ x) ≤ G q ⬝ᵥ x := by
        intro q
        apply farkas_side A b (-Pi.single k 1) (-1) (G q) (hQ q)
        · obtain ⟨x, hx, hxk⟩ := h1
          exact ⟨x, hx, by simp [neg_dotProduct, single_dotProduct]; linarith⟩
        · intro x hx hxk
          apply hvalQ q x ⟨hx, Or.inr ?_⟩
          have := hle1 x hx
          simp [neg_dotProduct, single_dotProduct] at hxk; linarith
      choose μ0 hμ0 hF0' using hF0
      choose μ1 hμ1 hF1' using hF1
      let u0 : Fin mQ → ℝ := fun q => μ0 q + 1
      let v0 : Fin mQ → ℝ := fun q => μ1 q + 1
      let E : Fin mQ ⊕ Fin mQ → (Fin n → ℝ) × ℝ := Sum.elim
        (fun q => (G q + u0 q • Pi.single k 1, hQ q))
        (fun q => (G q - v0 q • Pi.single k 1, hQ q - v0 q))
      have hE : ∀ i, ∀ x ∈ (Poly A b), (E i).2 ≤ (E i).1 ⬝ᵥ x := by
        rintro (q | q) x hx
        · have := hF0' q x hx
          have := hpos x hx k
          simp only [E, Sum.elim_inl, add_dotProduct, smul_dotProduct, single_dotProduct,
            smul_eq_mul, one_mul, u0] at *
          nlinarith
        · have := hF1' q x hx
          have := hle1 x hx
          simp only [E, Sum.elim_inr, sub_dotProduct, smul_dotProduct, single_dotProduct,
            smul_eq_mul, one_mul, v0, neg_dotProduct] at *
          nlinarith [hμ1 q]
      obtain ⟨M, A', b', hrep, hrows, hunit⟩ := build_rep A b E hE hpos
      have hposA' : ∀ x ∈ Poly A' b', ∀ j, 0 ≤ x j := by rw [hrep]; exact hpos
      -- each row of (convexHull ℝ (Poly A b ∩ ZeroOneSet k))'s representation is implied by the closures
      have hcutS : ∀ q, SimpleDisjClosure A' b' k ⊆ {x | hQ q ≤ G q ⬝ᵥ x} := by
        intro q
        obtain ⟨i1, hi1, hb1⟩ := hrows (Sum.inl q)
        obtain ⟨i2, hi2, hb2⟩ := hrows (Sum.inr q)
        by_cases hdeg : ∃ j0, j0 ≠ k ∧ G q j0 ≠ 0
        · obtain ⟨j0, hj0k, hj0⟩ := hdeg
          exact simpleDisj_nondeg A' b' k j0 hj0k (G q) (hQ q) (u0 q) (v0 q)
            (by simp [u0]; linarith [hμ0 q]) (by simp [v0]; linarith [hμ1 q]) hj0 i1 i2
            hi1 hb1 hi2 hb2 hunit
        · -- degenerate row: valid on all of (Poly A b)
          push_neg at hdeg
          refine (simpleDisjClosure_sub_poly A' b' k).trans ?_
          rw [hrep]
          intro x hx
          have hG : ∀ y : Fin n → ℝ, G q ⬝ᵥ y = G q k * y k := by
            intro y
            rw [dotProduct, Finset.sum_eq_single k]
            · intro j _ hj; rw [hdeg j hj, zero_mul]
            · simp
          obtain ⟨x0, hx0, hx0k⟩ := h0
          obtain ⟨x1, hx1, hx1k⟩ := h1
          have hx0k' : x0 k = 0 := le_antisymm hx0k (hpos x0 hx0 k)
          have hx1k' : x1 k = 1 := le_antisymm (hle1 x1 hx1) hx1k
          have a0 := hvalQ q x0 ⟨hx0, Or.inl hx0k'⟩
          have a1 := hvalQ q x1 ⟨hx1, Or.inr hx1k'⟩
          rw [hG] at a0 a1
          show hQ q ≤ G q ⬝ᵥ x
          rw [hG]
          rw [hx0k'] at a0; rw [hx1k'] at a1
          have := hpos x hx k; have := hle1 x hx
          nlinarith
      have hcutL : ∀ N' q, StrengthenedLPClosure A' b' k N' ⊆ {x | hQ q ≤ G q ⬝ᵥ x} := by
        intro N' q
        obtain ⟨i1, hi1, hb1⟩ := hrows (Sum.inl q)
        obtain ⟨i2, hi2, hb2⟩ := hrows (Sum.inr q)
        exact strengthened_cut A' b' k N' (G q) (hQ q) (u0 q) (v0 q)
          (by simp [u0]; linarith [hμ0 q]) (by simp [v0]; linarith [hμ1 q]) i1 i2 hi1 hb1 hi2 hb2
          hposA'
      refine ⟨M, A', b', hrep, ?_, fun N' => ?_⟩
      · intro x hx
        rw [← hGQ]
        exact fun q => hcutS q hx
      · intro x hx
        rw [← hGQ]
        exact fun q => hcutL N' q hx
    · -- (Poly A b) ∩ {x_k = 1} empty: cut x_k ≤ 0
      push_neg at h1
      obtain ⟨ε, hε, hεle⟩ := eps_of_lt1 A b k hne h1
      set ε' := min ε (1 / 2) with hε'
      have hε'0 : 0 < ε' := lt_min hε (by norm_num)
      have hε'1 : ε' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hle' : ∀ x ∈ (Poly A b), x k ≤ 1 - ε' := fun x hx => (hεle x hx).trans (by
        have := min_le_left ε (1 / 2); linarith)
      set vv := (1 - ε') / ε' with hvv
      have hvv0 : 0 < vv := div_pos (by linarith) hε'0
      let E : Fin 3 → (Fin n → ℝ) × ℝ := ![(-Pi.single k 1, -(1 - ε')),
        (-Pi.single k 1 + (1:ℝ) • Pi.single k 1, 0), (-Pi.single k 1 - vv • Pi.single k 1, 0 - vv)]
      have hE : ∀ i, ∀ x ∈ (Poly A b), (E i).2 ≤ (E i).1 ⬝ᵥ x := by
        intro i x hx
        have := hle' x hx
        fin_cases i
        · simp [E, neg_dotProduct, single_dotProduct]; linarith
        · simp [E]
        · show (0 - vv : ℝ) ≤ (-Pi.single k 1 - vv • Pi.single k 1) ⬝ᵥ x
          rw [sub_dotProduct, neg_dotProduct, smul_dotProduct, single_dotProduct, smul_eq_mul,
            one_mul]
          have h1' : (1 + vv) * x k ≤ vv := by
            have e : 1 + vv = 1 / ε' := by rw [hvv]; field_simp; ring
            rw [e, one_div_mul_eq_div, hvv]
            exact div_le_div_of_nonneg_right ‹_› hε'0.le
          linarith
      obtain ⟨M, A', b', hrep, hrows, hunit⟩ := build_rep A b E hE hpos
      have hposA' : ∀ x ∈ Poly A' b', ∀ j, 0 ≤ x j := by rw [hrep]; exact hpos
      have hfin : ∀ x ∈ (Poly A b), x k ≤ 0 → x ∈ (convexHull ℝ (Poly A b ∩ ZeroOneSet k)) := fun x hx hxk =>
        hSQ ⟨hx, Or.inl (le_antisymm hxk (hpos x hx k))⟩
      refine ⟨M, A', b', hrep, ?_, fun N' => ?_⟩
      · intro x hx
        obtain ⟨i0, hi0, hb0⟩ := hrows 0
        have := simpleDisj_le0 A' b' k ε' hε'0 hε'1 i0 hi0 hb0 hunit hx
        have hxS : x ∈ (Poly A b) := by rw [← hrep]; exact simpleDisjClosure_sub_poly A' b' k hx
        exact hfin x hxS this
      · intro x hx
        obtain ⟨i1, hi1, hb1⟩ := hrows 1
        obtain ⟨i2, hi2, hb2⟩ := hrows 2
        have := strengthened_cut A' b' k N' (-Pi.single k 1) 0 1 vv one_pos hvv0 i1 i2 hi1 hb1
          hi2 hb2 hposA' hx
        have hxS : x ∈ (Poly A b) := by rw [← hrep]; exact strengthenedLPClosure_sub_poly A' b' k N' hx
        simp [neg_dotProduct, single_dotProduct] at this
        exact hfin x hxS (by linarith)
  · -- (Poly A b) ∩ {x_k = 0} empty: cut x_k ≥ 1
    push_neg at h0
    obtain ⟨ε, hε, hεle⟩ := eps_of_pos A b k hne h0
    set ε' := min ε (1 / 2) with hε'
    have hε'0 : 0 < ε' := lt_min hε (by norm_num)
    have hε'1 : ε' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hge' : ∀ x ∈ (Poly A b), ε' ≤ x k := fun x hx => (min_le_left _ _).trans (hεle x hx)
    set uu := 1 / ε' with huu
    have huu0 : 0 < uu := by positivity
    let E : Fin 3 → (Fin n → ℝ) × ℝ := ![(Pi.single k 1, ε'),
      (Pi.single k 1 + uu • Pi.single k 1, 1), (Pi.single k 1 - (1:ℝ) • Pi.single k 1, 1 - 1)]
    have hE : ∀ i, ∀ x ∈ (Poly A b), (E i).2 ≤ (E i).1 ⬝ᵥ x := by
      intro i x hx
      have := hge' x hx
      have := hpos x hx k
      fin_cases i
      · simp [E, single_dotProduct]; linarith
      · show (1 : ℝ) ≤ (Pi.single k 1 + uu • Pi.single k 1) ⬝ᵥ x
        rw [add_dotProduct, smul_dotProduct, single_dotProduct, smul_eq_mul, one_mul]
        have : 1 ≤ uu * x k := by
          rw [huu, one_div, ← div_eq_inv_mul, le_div_iff₀ hε'0, one_mul]; assumption
        linarith
      · simp [E]
    obtain ⟨M, A', b', hrep, hrows, hunit⟩ := build_rep A b E hE hpos
    have hposA' : ∀ x ∈ Poly A' b', ∀ j, 0 ≤ x j := by rw [hrep]; exact hpos
    have hfin : ∀ x ∈ (Poly A b), 1 ≤ x k → x ∈ (convexHull ℝ (Poly A b ∩ ZeroOneSet k)) := fun x hx hxk =>
      hSQ ⟨hx, Or.inr (le_antisymm (hle1 x hx) hxk)⟩
    refine ⟨M, A', b', hrep, ?_, fun N' => ?_⟩
    · intro x hx
      obtain ⟨i0, hi0, hb0⟩ := hrows 0
      have := simpleDisj_ge1 A' b' k ε' hε'0 hε'1 i0 hi0 hb0 hunit hx
      have hxS : x ∈ (Poly A b) := by rw [← hrep]; exact simpleDisjClosure_sub_poly A' b' k hx
      exact hfin x hxS this
    · intro x hx
      obtain ⟨i1, hi1, hb1⟩ := hrows 1
      obtain ⟨i2, hi2, hb2⟩ := hrows 2
      have := strengthened_cut A' b' k N' (Pi.single k 1) 1 uu 1 huu0 one_pos i1 i2 hi1 hb1
        hi2 hb2 hposA' hx
      have hxS : x ∈ (Poly A b) := by rw [← hrep]; exact strengthenedLPClosure_sub_poly A' b' k N' hx
      simp [single_dotProduct] at this
      exact hfin x hxS this

end Disjunctive.CutCorrespondence


namespace Disjunctive.CutCorrespondence

open Set Finset

lemma exists_int_sum {n : ℕ} (f : Fin n → ℝ) (h : ∀ i, ∃ t : ℤ, f i = t) :
    ∃ z : ℤ, ∑ i, f i = z := by
  choose t ht using h
  exact ⟨∑ i, t i, by push_cast; exact Finset.sum_congr rfl fun i _ => ht i⟩

lemma int_of_zeroOne {x : ℝ} (h : x = 0 ∨ x = 1) : ∃ t : ℤ, x = t := by
  rcases h with h | h
  · exact ⟨0, by simp [h]⟩
  · exact ⟨1, by simp [h]⟩

/-- Mixed integer Gomory cuts are valid for points with all `N'`-coordinates in `{0,1}`. -/
lemma mig_valid {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (k : Fin n)
    (Nprime : Finset (Fin n)) (hk : k ∈ Nprime) (ι : Fin n → Fin m)
    (hdet : IsUnit (Ahat A ι).det) (h0 : 0 < Abar0 A b ι k) (h1 : Abar0 A b ι k < 1)
    (x : Fin n → ℝ) (hx : x ∈ Poly A b) (hint : ∀ j ∈ Nprime, x j = 0 ∨ x j = 1) :
    x ∈ StrengthenedSimpleDisjCutSet A b ι k Nprime := by
  classical
  show Pi0 A b ι k ≤ _
  set f0 := Abar0 A b ι k with hf0
  let str : Fin n → Prop := fun i => ∃ j ∈ Nprime, IsNonnegRow A b (ι i) j
  let fr : Fin n → ℝ := fun i => FracAbar A ι k i
  let c : Fin n → ℤ := fun i =>
    if str i then (if fr i * (1 - f0) ≤ (1 - fr i) * f0 then ⌊Abar A ι k i⌋ else ⌊Abar A ι k i⌋ + 1)
    else 0
  let d : Fin n → ℝ := fun i => Abar A ι k i - c i
  have hs := surplus_nonneg A b ι x hx
  -- integrality of z
  have hzint : ∃ z : ℤ, x k + ∑ i, (c i : ℝ) * Surplus A b ι i x = z := by
    obtain ⟨zk, hzk⟩ := int_of_zeroOne (hint k hk)
    obtain ⟨zs, hzs⟩ := exists_int_sum (fun i => (c i : ℝ) * Surplus A b ι i x) (by
      intro i
      by_cases hi : str i
      · obtain ⟨j, hj, hrow⟩ := hi
        have hsur : Surplus A b ι i x = x j := by
          simp [Surplus, hrow.1, hrow.2, single_dotProduct]
        obtain ⟨tj, htj⟩ := int_of_zeroOne (hint j hj)
        exact ⟨c i * tj, by rw [hsur, htj]; push_cast; ring⟩
      · exact ⟨0, by simp [c, hi]⟩)
    exact ⟨zk + zs, by rw [hzk, hzs]; push_cast; ring⟩
  obtain ⟨z, hz⟩ := hzint
  have hzd : (z : ℝ) = f0 - ∑ i, d i * Surplus A b ι i x := by
    rw [← hz, tableau_identity A b ι hdet k x]
    simp only [d, sub_mul, Finset.sum_sub_distrib]
    ring
  apply split_ineq f0 h0 h1 d _ _ hs _ z hzd
  intro i
  have hfr0 : 0 ≤ fr i := Int.fract_nonneg _
  have hfr1 : fr i < 1 := Int.fract_lt_one _
  have hfr : fr i = Abar A ι k i - ⌊Abar A ι k i⌋ := rfl
  unfold PiBar
  by_cases hi : str i
  · rw [if_pos hi]
    have hmin0 : 0 ≤ min (FracAbar A ι k i * (1 - f0)) ((1 - FracAbar A ι k i) * f0) :=
      le_min (mul_nonneg hfr0 (by linarith)) (mul_nonneg (by linarith) h0.le)
    by_cases hc : fr i * (1 - f0) ≤ (1 - fr i) * f0
    · have hd : d i = fr i := by simp only [d, c, if_pos hi, if_pos hc]; rw [hfr]
      rw [hd]
      refine ⟨le_of_eq (min_eq_left hc).symm, ?_⟩
      nlinarith
    · have hd : d i = fr i - 1 := by
        simp only [d, c, if_pos hi, if_neg hc]; push_cast; rw [hfr]; ring
      rw [hd]
      push_neg at hc
      refine ⟨?_, ?_⟩
      · nlinarith
      · rw [min_eq_right hc.le]; ring_nf; nlinarith
  · rw [if_neg hi]
    have hd : d i = Abar A ι k i := by simp [d, c, hi]
    rw [hd]
    exact piCoef_bounds A b ι k i

lemma piBar_le_piCoef {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (k : Fin n)
    (Nprime : Finset (Fin n)) (ι : Fin n → Fin m) (h0 : 0 < Abar0 A b ι k)
    (h1 : Abar0 A b ι k < 1) (i : Fin n) : PiBar A b ι k Nprime i ≤ PiCoef A b ι k i := by
  unfold PiBar
  split_ifs
  · set a := Abar A ι k i
    set f0 := Abar0 A b ι k
    have hf : FracAbar A ι k i = a - ⌊a⌋ := rfl
    rcases le_or_gt 0 a with ha | ha
    · refine (min_le_left _ _).trans (le_trans ?_ (le_max_left _ _))
      rw [hf]
      have : (0 : ℝ) ≤ ⌊a⌋ := by exact_mod_cast Int.floor_nonneg.mpr ha
      exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    · refine (min_le_right _ _).trans (le_trans ?_ (le_max_right _ _))
      rw [hf]
      have : ⌊a⌋ ≤ -1 := by
        have := Int.floor_lt.mpr (show a < ((0:ℤ):ℝ) by simpa using ha)
        omega
      have : (⌊a⌋ : ℝ) ≤ -1 := by exact_mod_cast this
      show (1 - (a - ⌊a⌋)) * f0 ≤ -a * f0
      exact mul_le_mul_of_nonneg_right (by linarith) h0.le
  · exact le_rfl

lemma migClosure_sub_simple {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (k : Fin n) (Nprime : Finset (Fin n)) : MIGClosure A b k Nprime ⊆ SimpleDisjClosure A b k := by
  intro x hx
  simp only [MIGClosure, SimpleDisjClosure, Set.mem_inter_iff, Set.mem_iInter] at hx ⊢
  refine ⟨hx.1, fun ι hinj hdet h0 h1 => ?_⟩
  have := hx.2 ι hinj hdet h0 h1
  show Pi0 A b ι k ≤ _
  refine le_trans this (Finset.sum_le_sum fun i _ => ?_)
  exact mul_le_mul_of_nonneg_right (piBar_le_piCoef A b k Nprime ι h0 h1 i)
    (surplus_nonneg A b ι x hx.1 i)

/-- Strengthened lift-and-project cuts are valid for nonnegative points of `S` whose
`N'`-coordinates are in `{0,1}`. -/
lemma strengthened_valid {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (k : Fin n)
    (Nprime : Finset (Fin n)) (hk : k ∈ Nprime) (α : Fin n → ℝ) (u : Fin m → ℝ) (u0 : ℝ)
    (v : Fin m → ℝ) (v0 β : ℝ) (hf : IsCGLPKFeasible A b k α u u0 v v0 β) (hu0 : 0 < u0)
    (hv0 : 0 < v0) (x : Fin n → ℝ) (hx : x ∈ Poly A b) (hx0 : ∀ j, 0 ≤ x j)
    (hint : ∀ j ∈ Nprime, x j = 0 ∨ x j = 1) :
    β ≤ Gamma A b u u0 v v0 Nprime α ⬝ᵥ x := by
  classical
  obtain ⟨e1, e2, e3, e4, -, hu, hv, -, -⟩ := hf
  -- α¹ x ≥ β and α² x ≥ β - v0
  have hrow : ∀ ρ, b ρ ≤ ∑ i, (if IsNonnegRow A b ρ i then 0 else A ρ i * x i) := by
    intro ρ
    by_cases hρ : ∃ j, IsNonnegRow A b ρ j
    · obtain ⟨j, hj⟩ := hρ
      rw [hj.2]
      apply le_of_eq
      symm
      apply Finset.sum_eq_zero
      intro i _
      split_ifs with hi
      · rfl
      · have : i ≠ j := fun e => hi (e ▸ hj)
        simp [hj.1, Pi.single_apply, this]
    · push_neg at hρ
      have := poly_mem hx ρ
      simp only [dotProduct] at this
      convert this using 2 with i
      simp [hρ i]
  have hA1 : ∀ w : Fin m → ℝ, 0 ≤ w → ∑ ρ, w ρ * b ρ ≤ Alpha1 A b w ⬝ᵥ x := by
    intro w hw
    calc ∑ ρ, w ρ * b ρ ≤ ∑ ρ, w ρ * ∑ i, (if IsNonnegRow A b ρ i then 0 else A ρ i * x i) :=
          Finset.sum_le_sum fun ρ _ => mul_le_mul_of_nonneg_left (hrow ρ) (hw ρ)
      _ = Alpha1 A b w ⬝ᵥ x := by
          simp only [Alpha1, dotProduct, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ρ _ => ?_
          split_ifs <;> ring
  have hα1 : β ≤ Alpha1 A b u ⬝ᵥ x := by linarith [hA1 u hu]
  have hα2 : β - v0 ≤ Alpha2 A b v ⬝ᵥ x := by
    have := hA1 v hv
    rw [show Alpha2 A b v = Alpha1 A b v from rfl]; linarith
  -- choose integers t
  let mm : Fin n → ℝ := fun i => MBar A b u u0 v v0 i
  let t : Fin n → ℤ := fun i => if i ∈ Nprime then
      (if Alpha1 A b u i + u0 * ⌈mm i⌉ ≤ Alpha2 A b v i - v0 * ⌊mm i⌋ then ⌈mm i⌉ else ⌊mm i⌋)
    else 0
  have hUV : 0 < u0 + v0 := by linarith
  have hm : ∀ i, (Alpha2 A b v i - Alpha1 A b u i) = (u0 + v0) * mm i := by
    intro i; simp only [mm, MBar]; field_simp
  have hcoef : ∀ i, Alpha1 A b u i + u0 * t i ≤ Gamma A b u u0 v v0 Nprime α i ∧
      Alpha2 A b v i - v0 * t i ≤ Gamma A b u u0 v v0 Nprime α i := by
    intro i
    unfold Gamma
    by_cases hi : i ∈ Nprime
    · simp only [if_pos hi, t]
      split_ifs with hc
      · rw [min_eq_left hc]
        refine ⟨le_rfl, ?_⟩
        have := Int.le_ceil (mm i)
        nlinarith [hm i]
      · push_neg at hc
        rw [min_eq_right hc.le]
        refine ⟨?_, le_rfl⟩
        have := Int.floor_le (mm i)
        nlinarith [hm i]
    · simp only [if_neg hi, t, Int.cast_zero, mul_zero, add_zero, sub_zero]
      have hik : i ≠ k := fun e => hi (e ▸ hk)
      have := e1 i; have := e2 i
      have := sum_split_nonneg A b u hu i; have := alpha2_le A b v hv i
      simp only [if_neg hik] at *
      constructor <;> linarith
  -- integrality of z = ∑ t_i x_i
  obtain ⟨z, hz⟩ := exists_int_sum (fun i => (t i : ℝ) * x i) (by
    intro i
    by_cases hi : i ∈ Nprime
    · obtain ⟨s, hs⟩ := int_of_zeroOne (hint i hi)
      exact ⟨t i * s, by rw [hs]; push_cast; ring⟩
    · exact ⟨0, by simp [t, hi]⟩)
  have hG : ∀ c : Fin n → ℝ, (∀ i, c i ≤ Gamma A b u u0 v v0 Nprime α i) →
      c ⬝ᵥ x ≤ Gamma A b u u0 v v0 Nprime α ⬝ᵥ x := fun c hc =>
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc i) (hx0 i)
  rcases le_or_gt 0 z with hz0 | hz0
  · refine le_trans ?_ (hG (fun i => Alpha1 A b u i + u0 * t i) fun i => (hcoef i).1)
    have : (fun i => Alpha1 A b u i + u0 * t i) ⬝ᵥ x = Alpha1 A b u ⬝ᵥ x + u0 * z := by
      rw [← hz]; simp only [dotProduct, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    have : (0 : ℝ) ≤ z := by exact_mod_cast hz0
    nlinarith
  · refine le_trans ?_ (hG (fun i => Alpha2 A b v i - v0 * t i) fun i => (hcoef i).2)
    have : (fun i => Alpha2 A b v i - v0 * t i) ⬝ᵥ x = Alpha2 A b v ⬝ᵥ x - v0 * z := by
      rw [← hz]; simp only [dotProduct, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    have : (z : ℝ) ≤ -1 := by exact_mod_cast (show z ≤ -1 by omega)
    nlinarith

end Disjunctive.CutCorrespondence


namespace Disjunctive.CutCorrespondence

open Set Finset

lemma convex_halfspace_dot {n : ℕ} (g : Fin n → ℝ) (β : ℝ) :
    Convex ℝ {x : Fin n → ℝ | β ≤ g ⬝ᵥ x} := by
  intro x hx y hy a c ha hc hac
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have : β = a * β + c * β := by rw [← add_mul, hac, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hc]

lemma convex_surplus_cut {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (ι : Fin n → Fin m) (w : Fin n → ℝ) (c0 : ℝ) :
    Convex ℝ {x : Fin n → ℝ | c0 ≤ ∑ i, w i * Surplus A b ι i x} := by
  intro x hx y hy a c ha hc hac
  simp only [Set.mem_ofPred_eq, Surplus] at hx hy ⊢
  have e : ∑ i, w i * (A (ι i) ⬝ᵥ (a • x + c • y) - b (ι i)) =
      a * ∑ i, w i * (A (ι i) ⬝ᵥ x - b (ι i)) + c * ∑ i, w i * (A (ι i) ⬝ᵥ y - b (ι i)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    linear_combination (w i) * (b (ι i)) * hac
  rw [e]
  have : c0 = a * c0 + c * c0 := by rw [← add_mul, hac, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hc]

lemma strengthenedLPClosure_convex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (k : Fin n) (Nprime : Finset (Fin n)) : Convex ℝ (StrengthenedLPClosure A b k Nprime) := by
  unfold StrengthenedLPClosure
  refine (poly_convex A b).inter ?_
  refine convex_iInter fun α => convex_iInter fun u => convex_iInter fun u0 =>
    convex_iInter fun v => convex_iInter fun v0 => convex_iInter fun β => convex_iInter fun _ =>
    convex_iInter fun _ => convex_iInter fun _ => convex_halfspace_dot _ _

lemma migClosure_convex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (k : Fin n) (Nprime : Finset (Fin n)) : Convex ℝ (MIGClosure A b k Nprime) := by
  unfold MIGClosure
  refine (poly_convex A b).inter ?_
  exact convex_iInter fun ι => convex_iInter fun _ => convex_iInter fun _ =>
    convex_iInter fun _ => convex_iInter fun _ => convex_surplus_cut A b ι _ _

/-- Add the rows of `P` (valid on `S ⊆ P`) to a representation of `S`. -/
lemma mixed_rep {m1 m n : ℕ} (A1 : Matrix (Fin m1) (Fin n) ℝ) (b1 : Fin m1 → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (Nprime : Finset (Fin n))
    (hsys : IsMixedZeroOneSystem A b Nprime) (hSP : Poly A1 b1 ⊆ Poly A b) :
    ∃ (M : ℕ) (A2 : Matrix (Fin M) (Fin n) ℝ) (b2 : Fin M → ℝ), Poly A2 b2 = Poly A1 b1 ∧
      IsMixedZeroOneSystem A2 b2 Nprime := by
  have hpos : ∀ x ∈ Poly A1 b1, ∀ j, 0 ≤ x j := fun x hx j =>
    (box_of_system A b Nprime hsys).1 x (hSP hx) j
  obtain ⟨M, A2, b2, hrep, hrows, -⟩ := build_rep A1 b1 (fun i : Fin m => (A i, b i))
    (fun i x hx => poly_mem (hSP hx) i) hpos
  refine ⟨M, A2, b2, hrep, ?_, ?_⟩
  · intro j
    obtain ⟨ρ, hρ, hb⟩ := hsys.1 j
    obtain ⟨ρ', h1, h2⟩ := hrows ρ
    exact ⟨ρ', by simp only at h1 h2; rw [h1, hρ], by simp only at h1 h2; rw [h2, hb]⟩
  · intro j hj
    obtain ⟨ρ, hρ, hb⟩ := hsys.2 j hj
    obtain ⟨ρ', h1, h2⟩ := hrows ρ
    exact ⟨ρ', by simp only at h1 h2; rw [h1, hρ], by simp only at h1 h2; rw [h2, hb]⟩

lemma PI_sub_split {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (k : Fin n) (hk : k ∈ Nprime) (S : Set (Fin n → ℝ))
    (hPI : convexHull ℝ (Poly A b ∩ ⋂ j ∈ Nprime, ZeroOneSet j) ⊆ S) :
    convexHull ℝ (Poly A b ∩ ⋂ j ∈ Nprime, ZeroOneSet j) ⊆ convexHull ℝ (S ∩ ZeroOneSet k) := by
  apply convexHull_mono
  intro x hx
  refine ⟨hPI (subset_convexHull ℝ _ hx), ?_⟩
  have := hx.2
  simp only [Set.mem_iInter] at this
  exact this k hk

lemma mem_int_points {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (x : Fin n → ℝ) (hx : x ∈ Poly A b ∩ ⋂ j ∈ Nprime, ZeroOneSet j) :
    ∀ j ∈ Nprime, x j = 0 ∨ x j = 1 := by
  have := hx.2
  simp only [Set.mem_iInter] at this
  exact this

theorem rank_bound_main {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hsys : IsMixedZeroOneSystem A b Nprime) :
    HasRankAtMost SplitConvexify (Poly A b) Nprime Nprime.card ∧
      HasRankAtMost SimpleDisjClosureOfSet (Poly A b) Nprime Nprime.card ∧
      HasRankAtMost (fun S k => StrengthenedLPClosureOfSet S k Nprime) (Poly A b) Nprime
        Nprime.card ∧
      HasRankAtMost (fun S k => MIGClosureOfSet S k Nprime) (Poly A b) Nprime Nprime.card := by
  obtain ⟨hb0, hb1⟩ := box_of_system A b Nprime hsys
  have hbox : ∀ x ∈ Poly A b, ∀ j ∈ Nprime, 0 ≤ x j ∧ x j ≤ 1 :=
    fun x hx j hj => ⟨hb0 x hx j, hb1 x hx j hj⟩
  refine ⟨partA A b Nprime hsys, ?_, ?_, ?_⟩
  · -- (b) simple disjunctive cuts
    apply rank_of_sandwich _ A b Nprime hbox
    intro k hk m1 A1 b1 hPI hSP
    have hpos : ∀ x ∈ Poly A1 b1, ∀ j, 0 ≤ x j := fun x hx j => hb0 x (hSP hx) j
    have hle1 : ∀ x ∈ Poly A1 b1, x k ≤ 1 := fun x hx => hb1 x (hSP hx) k hk
    obtain ⟨M, A', b', hrep, hsub, -⟩ := upper_rep A1 b1 k hpos hle1
    have hup : SimpleDisjClosureOfSet (Poly A1 b1) k ⊆ convexHull ℝ (Poly A1 b1 ∩ ZeroOneSet k) := by
      intro x hx
      simp only [SimpleDisjClosureOfSet, Set.mem_iInter] at hx
      exact hsub (hx M A' b' hrep)
    have heq : SimpleDisjClosureOfSet (Poly A1 b1) k = convexHull ℝ (Poly A1 b1 ∩ ZeroOneSet k) :=
      Set.Subset.antisymm hup (conv_subset_simpleDisjClosureOfSet _ k)
    refine ⟨(PI_sub_split A b Nprime k hk _ hPI).trans (heq ▸ le_rfl), hup, ?_⟩
    rw [heq]
    exact conv_split_rep A1 b1 k (fun x hx => ⟨hpos x hx k, hle1 x hx⟩)
  · -- (c) strengthened lift-and-project cuts
    apply rank_of_sandwich _ A b Nprime hbox
    intro k hk m1 A1 b1 hPI hSP
    have hpos : ∀ x ∈ Poly A1 b1, ∀ j, 0 ≤ x j := fun x hx j => hb0 x (hSP hx) j
    have hle1 : ∀ x ∈ Poly A1 b1, x k ≤ 1 := fun x hx => hb1 x (hSP hx) k hk
    obtain ⟨M, A', b', hrep, -, hsub⟩ := upper_rep A1 b1 k hpos hle1
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp only [StrengthenedLPClosureOfSet, Set.mem_iInter]
      intro m2 A2 b2 h2
      revert x
      apply convexHull_min _ (strengthenedLPClosure_convex A2 b2 k Nprime)
      intro x hx
      have hxS : x ∈ Poly A2 b2 := by rw [h2]; exact hPI (subset_convexHull ℝ _ hx)
      refine ⟨hxS, ?_⟩
      simp only [Set.mem_iInter]
      intro α u u0 v v0 β hf hu0 hv0
      exact strengthened_valid A2 b2 k Nprime hk α u u0 v v0 β hf hu0 hv0 x hxS
        (hb0 x hx.1) (mem_int_points A b Nprime x hx)
    · intro x hx
      simp only [StrengthenedLPClosureOfSet, Set.mem_iInter] at hx
      exact hsub Nprime (hx M A' b' hrep)
    · obtain ⟨M2, A2, b2, hrep2, hsys2⟩ := mixed_rep A1 b1 A b Nprime hsys hSP
      rw [← hrep2]
      exact strengthenedLPClosure_isPoly A2 b2 Nprime hsys2 k hk
  · -- (d) mixed integer Gomory cuts
    apply rank_of_sandwich _ A b Nprime hbox
    intro k hk m1 A1 b1 hPI hSP
    have hpos : ∀ x ∈ Poly A1 b1, ∀ j, 0 ≤ x j := fun x hx j => hb0 x (hSP hx) j
    have hle1 : ∀ x ∈ Poly A1 b1, x k ≤ 1 := fun x hx => hb1 x (hSP hx) k hk
    obtain ⟨M, A', b', hrep, hsub, -⟩ := upper_rep A1 b1 k hpos hle1
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp only [MIGClosureOfSet, Set.mem_iInter]
      intro m2 A2 b2 h2
      revert x
      apply convexHull_min _ (migClosure_convex A2 b2 k Nprime)
      intro x hx
      have hxS : x ∈ Poly A2 b2 := by rw [h2]; exact hPI (subset_convexHull ℝ _ hx)
      refine ⟨hxS, ?_⟩
      simp only [Set.mem_iInter]
      intro ι _ hdet h0 h1
      exact mig_valid A2 b2 k Nprime hk ι hdet h0 h1 x hxS (mem_int_points A b Nprime x hx)
    · intro x hx
      simp only [MIGClosureOfSet, Set.mem_iInter] at hx
      exact hsub (migClosure_sub_simple A' b' k Nprime (hx M A' b' hrep))
    · obtain ⟨M2, A2, b2, hrep2, hsys2⟩ := mixed_rep A1 b1 A b Nprime hsys hSP
      rw [← hrep2]
      exact migClosure_isPoly A2 b2 Nprime hsys2 k hk

end Disjunctive.CutCorrespondence

open Disjunctive.CutCorrespondence in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hsys : IsMixedZeroOneSystem A b Nprime) :
    HasRankAtMost SplitConvexify (Poly A b) Nprime Nprime.card ∧
      HasRankAtMost SimpleDisjClosureOfSet (Poly A b) Nprime Nprime.card ∧
      HasRankAtMost (fun S k => StrengthenedLPClosureOfSet S k Nprime) (Poly A b) Nprime
        Nprime.card ∧
      HasRankAtMost (fun S k => MIGClosureOfSet S k Nprime) (Poly A b) Nprime Nprime.card :=
  rank_bound_main A b Nprime hsys
