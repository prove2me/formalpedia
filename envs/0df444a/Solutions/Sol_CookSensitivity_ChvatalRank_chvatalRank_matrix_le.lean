-- Prove2me | solution 1 for CookSensitivity.ChvatalRank.chvatalRank_matrix_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T09:42:26.014859+00:00
-- url     : https://prove2.me/submissions/aed479ed-76a1-4a40-b649-4d8b7024a901
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CookSensitivity_ChvatalRank_maxSubdet
import Definitions.Def_CookSensitivity_ChvatalRank_IntegerProgram
import Definitions.Def_CookSensitivity_ChvatalRank_ChvatalClosure
import Theorems.Thm_CookSensitivity_ChvatalRank_integerHull_eq_of_bounded_matrix
import Theorems.Thm_CookSensitivity_ChvatalRank_chvatalIter_subset_halfspace
import Theorems.Thm_CookSensitivity_ChvatalRank_chvatalIter_eq_empty_of_no_integer_point
import Theorems.Thm_CookSensitivity_ChvatalRank_lp_ip_value_gap

open CookSensitivity.ChvatalRank
open Matrix

private lemma chvatalClosure_mono {n : ℕ} {S T : Set (Fin n → ℚ)} (hST : S ⊆ T) :
    chvatalClosure S ⊆ chvatalClosure T := by
  intro x hx a β hT
  exact hx a β (fun y hy => hT y (hST hy))

private lemma chvatalIter_mono_set {n : ℕ} (t : ℕ) {S T : Set (Fin n → ℚ)} (hST : S ⊆ T) :
    chvatalIter t S ⊆ chvatalIter t T := by
  induction t with
  | zero => exact hST
  | succ t ih =>
    simp only [chvatalIter, Function.iterate_succ']
    exact chvatalClosure_mono ih

private lemma chvatalClosure_polyhedron_int_subset {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    chvatalClosure (polyhedron A (fun i => (b i : ℚ))) ⊆
      polyhedron A (fun i => (b i : ℚ)) := by
  intro x hx i
  have hrow : ∀ y ∈ polyhedron A (fun i => (b i : ℚ)),
      (fun j => (A i j : ℚ)) ⬝ᵥ y ≤ (b i : ℚ) := by
    intro y hy
    have hi := hy i
    simpa [mulVec, dotProduct] using hi
  have hcut := hx (A i) (b i : ℚ) hrow
  rw [Int.floor_intCast] at hcut
  simpa [mulVec, dotProduct] using hcut

private lemma chvatalIter_anti {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    {t₁ t₂ : ℕ} (hle : t₁ ≤ t₂) :
    chvatalIter t₂ (polyhedron A (fun i => (b i : ℚ))) ⊆
      chvatalIter t₁ (polyhedron A (fun i => (b i : ℚ))) := by
  set P := polyhedron A (fun i => (b i : ℚ))
  have hstep : ∀ k, chvatalIter (k + 1) P ⊆ chvatalIter k P := by
    intro k
    induction k with
    | zero => exact chvatalClosure_polyhedron_int_subset A b
    | succ k ih =>
      simp only [chvatalIter, Function.iterate_succ'] at ih ⊢
      exact chvatalClosure_mono ih
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction d with
  | zero => simp
  | succ d ih =>
    exact (hstep (t₁ + d)).trans (ih (Nat.le_add_right t₁ d))

private lemma int_dot_integral {n : ℕ} (a : Fin n → ℤ) {z : Fin n → ℚ} (hz : IsIntegral z) :
    ∃ k : ℤ, (fun i => (a i : ℚ)) ⬝ᵥ z = (k : ℚ) := by
  choose f hf using hz
  refine ⟨∑ i, a i * f i, ?_⟩
  simp only [dotProduct, hf, Int.cast_sum, Int.cast_mul]

private lemma integral_mem_chvatalIter {n : ℕ} (t : ℕ) (S : Set (Fin n → ℚ))
    {z : Fin n → ℚ} (hzS : z ∈ S) (hzI : IsIntegral z) :
    z ∈ chvatalIter t S := by
  induction t with
  | zero => exact hzS
  | succ t ih =>
    simp only [chvatalIter, Function.iterate_succ', Function.comp_apply]
    intro a β hβ
    have hz_le : (fun i => (a i : ℚ)) ⬝ᵥ z ≤ β := hβ z ih
    obtain ⟨k, hk⟩ := int_dot_integral a hzI
    rw [hk] at hz_le ⊢
    exact Int.cast_le.mpr (Int.le_floor.mpr hz_le)

private lemma convex_chvatalClosure {n : ℕ} (S : Set (Fin n → ℚ)) :
    Convex ℚ (chvatalClosure S) := by
  intro x hx y hy u v hu hv huv a β hβ
  have hx' := hx a β hβ
  have hy' := hy a β hβ
  have hdot : (fun i => (a i : ℚ)) ⬝ᵥ (u • x + v • y) =
      u * ((fun i => (a i : ℚ)) ⬝ᵥ x) + v * ((fun i => (a i : ℚ)) ⬝ᵥ y) := by
    simp [dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [hdot]
  calc
    u * ((fun i => (a i : ℚ)) ⬝ᵥ x) + v * ((fun i => (a i : ℚ)) ⬝ᵥ y)
      ≤ u * (⌊β⌋ : ℚ) + v * (⌊β⌋ : ℚ) := by nlinarith
    _ = (u + v) * (⌊β⌋ : ℚ) := by ring
    _ = (⌊β⌋ : ℚ) := by rw [huv, one_mul]

private lemma convex_polyhedron {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ) :
    Convex ℚ (polyhedron A b) := by
  intro x hx y hy u v hu hv huv i
  have hxi := hx i
  have hyi := hy i
  have hlin : ((A.map (Int.cast : ℤ → ℚ)) *ᵥ (u • x + v • y)) i =
      u * ((A.map (Int.cast : ℤ → ℚ)) *ᵥ x) i + v * ((A.map (Int.cast : ℤ → ℚ)) *ᵥ y) i := by
    simp [mulVec_add, mulVec_smul]
  rw [hlin]
  calc
    u * ((A.map (Int.cast : ℤ → ℚ)) *ᵥ x) i + v * ((A.map (Int.cast : ℤ → ℚ)) *ᵥ y) i
      ≤ u * b i + v * b i := by nlinarith
    _ = (u + v) * b i := by ring
    _ = b i := by rw [huv, one_mul]

private lemma integerHull_subset_chvatalIter {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℚ) (t : ℕ) :
    integerHull (polyhedron A b) ⊆ chvatalIter t (polyhedron A b) := by
  apply convexHull_min
  · rintro z ⟨hzP, hzI⟩
    exact integral_mem_chvatalIter t (polyhedron A b) hzP hzI
  · cases t with
    | zero => exact convex_polyhedron A b
    | succ t =>
      simp only [chvatalIter, Function.iterate_succ', Function.comp_apply]
      exact convex_chvatalClosure _

private lemma chvatalRank_le_of_eq {n : ℕ} (S : Set (Fin n → ℚ)) (t : ℕ)
    (h : chvatalIter t S = integerHull S) :
    chvatalRank S ≤ (t : ℕ∞) := by
  unfold chvatalRank
  exact iInf₂_le t h

private lemma matrix_eq_zero_of_maxSubdet_eq_zero {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (h0 : maxSubdet A = 0) : A = 0 := by
  ext i j
  by_contra hij
  have hm : 0 < m := Nat.pos_of_ne_zero (fun h => Fin.elim0 (h ▸ i))
  have hn : 0 < n := Nat.pos_of_ne_zero (fun h => Fin.elim0 (h ▸ j))
  let k : Fin (min m n) := ⟨0, by omega⟩
  have hk0 : k.val = 0 := rfl
  let f : Fin (k.val + 1) ↪ Fin m := ⟨fun _ => i, fun a b _ => Fin.ext (by have := a.isLt; have := b.isLt; omega)⟩
  let g : Fin (k.val + 1) ↪ Fin n := ⟨fun _ => j, fun a b _ => Fin.ext (by have := a.isLt; have := b.isLt; omega)⟩
  have hle1 : (A.submatrix f g).det.natAbs ≤ maxSubdet A := by
    unfold maxSubdet
    refine le_trans (Finset.le_sup (f := fun g' : Fin (k.val + 1) ↪ Fin n =>
      (A.submatrix f g').det.natAbs) (Finset.mem_univ g)) ?_
    refine le_trans (Finset.le_sup (f := fun f' : Fin (k.val + 1) ↪ Fin m =>
      Finset.univ.sup fun g' : Fin (k.val + 1) ↪ Fin n =>
        (A.submatrix f' g').det.natAbs) (Finset.mem_univ f)) ?_
    exact Finset.le_sup (f := fun k' : Fin (min m n) =>
      Finset.univ.sup fun f' : Fin (k'.val + 1) ↪ Fin m =>
        Finset.univ.sup fun g' : Fin (k'.val + 1) ↪ Fin n =>
          (A.submatrix f' g').det.natAbs) (Finset.mem_univ k)
  have hdet : (A.submatrix f g).det = A i j := Matrix.det_fin_one (A.submatrix f g)
  rw [hdet, h0, Nat.le_zero, Int.natAbs_eq_zero] at hle1
  exact hij hle1

open scoped Classical in
private lemma exists_int_greatest {n : ℕ} (P : Set (Fin n → ℚ))
    (hPZ : ∃ x ∈ P, IsIntegral x) (w : Fin n → ℤ) (d : ℚ)
    (hd : ∀ x ∈ integerHull P, (fun j => (w j : ℚ)) ⬝ᵥ x ≤ d) :
    ∃ (q : ℤ) (z : Fin n → ℚ), z ∈ P ∧ IsIntegral z ∧
      (fun j => (w j : ℚ)) ⬝ᵥ z = (q : ℚ) ∧ (q : ℚ) ≤ d ∧
      IsGreatest ((fun x => (fun j => (w j : ℚ)) ⬝ᵥ x) '' integerHull P) (q : ℚ) := by
  rcases hPZ with ⟨z₀, hz₀P, hz₀I⟩
  obtain ⟨k₀, hk₀⟩ := int_dot_integral w hz₀I
  have hle_floor : ∀ z ∈ P, IsIntegral z → ∀ k : ℤ,
      (fun j => (w j : ℚ)) ⬝ᵥ z = (k : ℚ) → k ≤ ⌊d⌋ := by
    intro z hzP hzI k hk
    have hz_hull : z ∈ integerHull P := subset_convexHull ℚ {x | x ∈ P ∧ IsIntegral x} ⟨hzP, hzI⟩
    have h1 := hd z hz_hull
    rw [hk] at h1
    exact Int.le_floor.mpr h1
  have hbdd : ∃ m : ℕ, ∃ z ∈ P, IsIntegral z ∧
      (fun j => (w j : ℚ)) ⬝ᵥ z = ((⌊d⌋ - (m : ℤ) : ℤ) : ℚ) := by
    have hk₀_le := hle_floor z₀ hz₀P hz₀I k₀ hk₀
    refine ⟨(⌊d⌋ - k₀).toNat, z₀, hz₀P, hz₀I, ?_⟩
    rw [hk₀]
    congr 1
    omega
  let m₀ := Nat.find hbdd
  rcases Nat.find_spec hbdd with ⟨z_max, hz_maxP, hz_maxI, hz_max_eq⟩
  let q : ℤ := ⌊d⌋ - (m₀ : ℤ)
  have hq_le_d : (q : ℚ) ≤ d := by
    have : (q : ℚ) ≤ (⌊d⌋ : ℚ) := by
      unfold q; push_cast; linarith
    exact this.trans (Int.floor_le d)
  have hmax_int : ∀ z ∈ P, IsIntegral z → (fun j => (w j : ℚ)) ⬝ᵥ z ≤ (q : ℚ) := by
    intro z hzP hzI
    obtain ⟨k, hk⟩ := int_dot_integral w hzI
    have hk_le := hle_floor z hzP hzI k hk
    have hnot : ¬ (⌊d⌋ - k).toNat < m₀ := by
      intro hlt
      refine Nat.find_min hbdd hlt ⟨z, hzP, hzI, ?_⟩
      rw [hk]
      congr 1
      omega
    rw [hk, Int.cast_le]
    unfold q
    omega
  have hmax_hull : ∀ x ∈ integerHull P, (fun j => (w j : ℚ)) ⬝ᵥ x ≤ (q : ℚ) := by
    have hsub : integerHull P ⊆ {x | (fun j => (w j : ℚ)) ⬝ᵥ x ≤ (q : ℚ)} := by
      apply convexHull_min
      · rintro z ⟨hzP, hzI⟩
        exact hmax_int z hzP hzI
      · intro x hx y hy u v hu hv huv
        simp only [Set.mem_setOf_eq, dotProduct_add, dotProduct_smul, smul_eq_mul] at hx hy ⊢
        calc
          u * ((fun j => (w j : ℚ)) ⬝ᵥ x) + v * ((fun j => (w j : ℚ)) ⬝ᵥ y)
            ≤ u * (q : ℚ) + v * (q : ℚ) := by nlinarith
          _ = (u + v) * (q : ℚ) := by ring
          _ = (q : ℚ) := by rw [huv, one_mul]
    intro x hx
    exact hsub hx
  refine ⟨q, z_max, hz_maxP, hz_maxI, hz_max_eq, hq_le_d, ?_⟩
  refine ⟨⟨z_max, subset_convexHull ℚ _ ⟨hz_maxP, hz_maxI⟩, hz_max_eq⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hmax_hull x hx

private lemma bound_calc (n Δ k : ℕ) (hn : 1 ≤ n) (hΔ : 1 ≤ Δ)
    (hk : k ≤ n ^ (2 * n + 2) * Δ ^ (n + 1)) :
    (n ^ (2 * n) * 2 ^ (n ^ 3) + 1) * k + 1 ≤
      2 ^ (n ^ 3 + 1) * n ^ (5 * n) * Δ ^ (n + 1) := by
  have hΔ_pos : 1 ≤ Δ ^ (n + 1) := Nat.one_le_pow _ _ hΔ
  rcases eq_or_lt_of_le hn with rfl | hn2
  · simp only [Nat.reduceAdd, Nat.reduceMul, one_pow, one_mul, pow_one] at hk ⊢
    nlinarith
  · have hn_pow : n ^ (2 * n) * n ^ (2 * n + 2) ≤ n ^ (5 * n) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right hn (by omega)
    have h2_pos : 2 ≤ n ^ (2 * n) * 2 ^ (n ^ 3) := by
      have h1 : 1 ≤ n ^ (2 * n) := Nat.one_le_pow _ _ hn
      have h2 : 2 ≤ 2 ^ (n ^ 3) := by
        calc 2 = 2 ^ 1 := by ring
          _ ≤ 2 ^ (n ^ 3) := Nat.pow_le_pow_right (by omega) (Nat.one_le_pow _ _ hn)
      nlinarith
    have hstep1 : (n ^ (2 * n) * 2 ^ (n ^ 3) + 1) * k + 1 ≤
        (n ^ (2 * n) * 2 ^ (n ^ 3) + 1) * (n ^ (2 * n + 2) * Δ ^ (n + 1)) + 1 := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hk) 1
    have hstep2 : (n ^ (2 * n) * 2 ^ (n ^ 3) + 1) * (n ^ (2 * n + 2) * Δ ^ (n + 1)) + 1 ≤
        (2 * (n ^ (2 * n) * 2 ^ (n ^ 3))) * (n ^ (2 * n + 2) * Δ ^ (n + 1)) := by
      have hprod_pos : 1 ≤ n ^ (2 * n + 2) * Δ ^ (n + 1) :=
        Nat.mul_pos (Nat.one_le_pow _ _ hn) hΔ_pos
      nlinarith
    have hstep3 : (2 * (n ^ (2 * n) * 2 ^ (n ^ 3))) * (n ^ (2 * n + 2) * Δ ^ (n + 1)) ≤
        2 ^ (n ^ 3 + 1) * n ^ (5 * n) * Δ ^ (n + 1) := by
      calc
        (2 * (n ^ (2 * n) * 2 ^ (n ^ 3))) * (n ^ (2 * n + 2) * Δ ^ (n + 1))
          = 2 ^ (n ^ 3 + 1) * (n ^ (2 * n) * n ^ (2 * n + 2)) * Δ ^ (n + 1) := by
            rw [pow_succ]; ring
        _ ≤ 2 ^ (n ^ 3 + 1) * n ^ (5 * n) * Δ ^ (n + 1) := by
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hn_pow)
    exact hstep1.trans (hstep2.trans hstep3)

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    chvatalRankMatrix A ≤
      ((2 ^ (n ^ 3 + 1) * n ^ (5 * n) * maxSubdet A ^ (n + 1) : ℕ) : ℕ∞) := by
  unfold chvatalRankMatrix
  refine iSup_le fun b => ?_
  set b_Q : Fin m → ℚ := fun i => (b i : ℚ)
  set P := polyhedron A b_Q
  set T : ℕ := 2 ^ (n ^ 3 + 1) * n ^ (5 * n) * maxSubdet A ^ (n + 1)
  have hP_poly : IsPolyhedron P := ⟨m, A.map Int.cast, b_Q, rfl⟩
  by_cases hP_emp : P = ∅
  · refine le_trans (chvatalRank_le_of_eq P 0 ?_) (by simp)
    rw [hP_emp, chvatalIter, Function.iterate_zero, id_eq, integerHull]
    simp
  · obtain ⟨x₀, hx₀P⟩ := Set.nonempty_iff_ne_empty.mpr hP_emp
    by_cases hn0 : n = 0
    · subst hn0
      refine le_trans (chvatalRank_le_of_eq P 0 ?_) (by simp)
      apply Set.Subset.antisymm _ (integerHull_subset_chvatalIter A b_Q 0)
      intro x _
      have hx₀I : IsIntegral x₀ := fun i => Fin.elim0 i
      have hxeq : x = x₀ := Subsingleton.elim x x₀
      rw [hxeq]
      exact subset_convexHull ℚ {y | y ∈ P ∧ IsIntegral y} ⟨hx₀P, hx₀I⟩
    · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
      by_cases hΔ0 : maxSubdet A = 0
      · have hA0 : A = 0 := matrix_eq_zero_of_maxSubdet_eq_zero A hΔ0
        subst hA0
        refine le_trans (chvatalRank_le_of_eq P 0 ?_) (by simp)
        apply Set.Subset.antisymm _ (integerHull_subset_chvatalIter 0 b_Q 0)
        have hP_univ : P = Set.univ := by
          ext x
          simp only [Set.mem_univ, iff_true]
          intro i
          have h0 := hx₀P i
          simpa [polyhedron, mulVec] using h0
        have h0P : (0 : Fin n → ℚ) ∈ P := by rw [hP_univ]; trivial
        have h0I : IsIntegral (0 : Fin n → ℚ) := fun _ => ⟨0, by simp⟩
        obtain ⟨N, M, hM_bd, hM_hull⟩ := integerHull_eq_of_bounded_matrix (0 : Matrix (Fin m) (Fin n) ℤ)
        obtain ⟨d, hd⟩ := hM_hull b_Q ⟨0, h0P, h0I⟩
        have hM0 : M = 0 := by
          ext i j
          have h := hM_bd i j
          rw [hΔ0, zero_pow hn0, mul_zero] at h
          exact abs_nonpos_iff.mp h
        have h0_hull : (0 : Fin n → ℚ) ∈ integerHull P :=
          subset_convexHull ℚ _ ⟨h0P, h0I⟩
        rw [hd, hM0] at h0_hull ⊢
        intro x _ i
        have hi := h0_hull i
        simpa [mulVec] using hi
      · have hΔ1 : 1 ≤ maxSubdet A := Nat.pos_of_ne_zero hΔ0
        by_cases hPZ : ∃ x ∈ P, IsIntegral x
        · obtain ⟨N, M, hM_bd, hM_hull⟩ := integerHull_eq_of_bounded_matrix A
          obtain ⟨d, hd⟩ := hM_hull b_Q hPZ
          refine chvatalRank_le_of_eq P T ?_
          apply Set.Subset.antisymm _ (integerHull_subset_chvatalIter A b_Q T)
          intro x hxT
          rw [hd]
          intro i
          let w : Fin n → ℤ := M i
          let w_Q : Fin n → ℚ := fun j => (w j : ℚ)
          have hd_i : ∀ y ∈ integerHull P, w_Q ⬝ᵥ y ≤ d i := by
            intro y hy
            rw [hd] at hy
            have hyi := hy i
            simpa [w_Q, w, mulVec, dotProduct] using hyi
          obtain ⟨q, z_i, hz_iP, hz_iI, hz_i_eq, hq_le_d, hq_great⟩ :=
            exists_int_greatest P hPZ w (d i) hd_i
          obtain ⟨μ, hμ_great, hμ_sub⟩ :=
            chvatalIter_subset_halfspace P hP_poly hPZ w q hq_great
          rcases hμ_great.1 with ⟨xbar, hxbarP, hxbar_eq⟩
          change w_Q ⬝ᵥ xbar = μ at hxbar_eq
          have hxbar_opt : IsLPOptimal A b_Q w_Q xbar := by
            refine ⟨hxbarP, fun y hyP => ?_⟩
            rw [hxbar_eq]
            exact hμ_great.2 ⟨y, hyP, rfl⟩
          obtain ⟨zbar, hzbar_opt, hgap⟩ := lp_ip_value_gap A b_Q w_Q hPZ xbar hxbar_opt
          have hzbar_eq : w_Q ⬝ᵥ zbar = (q : ℚ) := by
            apply le_antisymm
            · exact hq_great.2 ⟨zbar, subset_convexHull ℚ _ ⟨hzbar_opt.2.1, hzbar_opt.1⟩, rfl⟩
            · rw [← hz_i_eq]
              exact hzbar_opt.2.2 z_i hz_iP hz_iI
          rw [hxbar_eq, hzbar_eq] at hgap
          have hl1 : l1Norm w_Q ≤ (n : ℚ) * ((n ^ (2 * n) * maxSubdet A ^ n : ℕ) : ℚ) := by
            unfold l1Norm
            have hterm : ∀ j : Fin n, |w_Q j| ≤ ((n ^ (2 * n) * maxSubdet A ^ n : ℕ) : ℚ) := by
              intro j
              change |(M i j : ℚ)| ≤ (((n ^ (2 * n) * maxSubdet A ^ n : ℕ) : ℤ) : ℚ)
              rw [← Int.cast_abs]
              exact Int.cast_le.mpr (hM_bd i j)
            calc
              ∑ j : Fin n, |w_Q j| ≤ ∑ _j : Fin n, ((n ^ (2 * n) * maxSubdet A ^ n : ℕ) : ℚ) :=
                Finset.sum_le_sum fun j _ => hterm j
              _ = (n : ℚ) * ((n ^ (2 * n) * maxSubdet A ^ n : ℕ) : ℚ) := by
                simp
          have hgap_nat : μ - (q : ℚ) ≤ ((n ^ (2 * n + 2) * maxSubdet A ^ (n + 1) : ℕ) : ℚ) := by
            have hpos : (0 : ℚ) ≤ (n : ℚ) * (maxSubdet A : ℚ) := by positivity
            calc
              μ - (q : ℚ) ≤ (n : ℚ) * (maxSubdet A : ℚ) * l1Norm w_Q := hgap
              _ ≤ (n : ℚ) * (maxSubdet A : ℚ) *
                    ((n : ℚ) * ((n ^ (2 * n) * maxSubdet A ^ n : ℕ) : ℚ)) := by
                exact mul_le_mul_of_nonneg_left hl1 hpos
              _ = ((n ^ (2 * n + 2) * maxSubdet A ^ (n + 1) : ℕ) : ℚ) := by
                push_cast; ring
          have hk_le : (⌊μ⌋ - q).toNat ≤ n ^ (2 * n + 2) * maxSubdet A ^ (n + 1) := by
            have hfl : (⌊μ⌋ : ℚ) ≤ μ := Int.floor_le μ
            have hdiff : ((⌊μ⌋ - q : ℤ) : ℚ) ≤ (((n ^ (2 * n + 2) * maxSubdet A ^ (n + 1) : ℕ) : ℤ) : ℚ) := by
              rw [Int.cast_sub, Int.cast_natCast]
              linarith
            have hdiff_int : ⌊μ⌋ - q ≤ ((n ^ (2 * n + 2) * maxSubdet A ^ (n + 1) : ℕ) : ℤ) :=
              Int.cast_le.mp hdiff
            omega
          have ht_le : (n ^ (2 * n) * 2 ^ (n ^ 3) + 1) * (⌊μ⌋ - q).toNat + 1 ≤ T :=
            bound_calc n (maxSubdet A) (⌊μ⌋ - q).toNat hn1 hΔ1 hk_le
          have hx_ti : x ∈ chvatalIter ((n ^ (2 * n) * 2 ^ (n ^ 3) + 1) * (⌊μ⌋ - q).toNat + 1) P :=
            chvatalIter_anti A b ht_le hxT
          have hx_q : w_Q ⬝ᵥ x ≤ (q : ℚ) := hμ_sub hx_ti
          have hx_d : w_Q ⬝ᵥ x ≤ d i := hx_q.trans hq_le_d
          simpa [w_Q, w, mulVec, dotProduct] using hx_d
        · push_neg at hPZ
          have hemp := chvatalIter_eq_empty_of_no_integer_point P hP_poly hPZ
          have ht_le : n ^ (2 * n) * 2 ^ (n ^ 3) ≤ T := by
            have h0 := bound_calc n (maxSubdet A) 1 hn1 hΔ1 (by
              exact Nat.mul_pos (Nat.one_le_pow _ _ hn1) (Nat.one_le_pow _ _ hΔ1))
            omega
          refine chvatalRank_le_of_eq P T ?_
          apply Set.Subset.antisymm _ (integerHull_subset_chvatalIter A b_Q T)
          have hsub := chvatalIter_anti A b ht_le
          rw [hemp] at hsub
          exact hsub.trans (Set.empty_subset _)
