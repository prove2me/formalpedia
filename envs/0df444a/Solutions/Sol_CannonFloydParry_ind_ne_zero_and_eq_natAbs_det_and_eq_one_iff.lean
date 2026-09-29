-- Prove2me | solution 1 for CannonFloydParry.ind_ne_zero_and_eq_natAbs_det_and_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T20:13:45.809481+00:00
-- url     : https://prove2.me/submissions/0299fdbc-4bc8-4fc2-a6da-095bb1036b03

import Definitions.Def_CannonFloydParry_PIP
import Mathlib

namespace CannonFloydParry.S7

open Matrix

variable {n : ℕ}

/-- The real matrix of an integer matrix. -/
noncomputable abbrev rM (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  A.map (Int.cast : ℤ → ℝ)

lemma rM_mul (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) : rM (A * B) = rM A * rM B := by
  simp only [rM]
  exact Matrix.map_mul (f := Int.castRingHom ℝ)

lemma rM_one : rM (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) = 1 := by
  simp only [rM]
  exact Matrix.map_one _ Int.cast_zero Int.cast_one

lemma glAct_eq (A : GL (Fin (n + 1)) ℤ) (x : Fin (n + 1) → ℝ) :
    glAct A x = rM (A : Matrix _ _ ℤ) *ᵥ x := rfl

lemma glAct_inv_glAct (A : GL (Fin (n + 1)) ℤ) (x : Fin (n + 1) → ℝ) :
    glAct A⁻¹ (glAct A x) = x := by
  rw [glAct_eq, glAct_eq, Matrix.mulVec_mulVec, ← rM_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, rM_one, Matrix.one_mulVec]

lemma glAct_smul (A : GL (Fin (n + 1)) ℤ) (c : ℝ) (x : Fin (n + 1) → ℝ) :
    glAct A (c • x) = c • glAct A x := by
  rw [glAct_eq, glAct_eq, Matrix.mulVec_smul]

lemma glAct_ne_zero (A : GL (Fin (n + 1)) ℤ) {x : Fin (n + 1) → ℝ} (hx : x ≠ 0) :
    glAct A x ≠ 0 := by
  intro h
  apply hx
  rw [← glAct_inv_glAct A x, h, glAct_eq, Matrix.mulVec_zero]

lemma sum_abs_pos {x : Fin (n + 1) → ℝ} (hx : x ≠ 0) : 0 < ∑ i, |x i| := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact lt_of_lt_of_le (abs_pos.mpr hi)
    (Finset.single_le_sum (f := fun i => |x i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))

lemma rho_smul {c : ℝ} (hc : 0 < c) (y : Fin (n + 1) → ℝ) : rho (c • y) = rho y := by
  unfold rho
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc, ← Finset.mul_sum, smul_smul]
  congr 1
  by_cases hs : ∑ i, |y i| = 0
  · simp [hs]
  · field_simp

lemma rho_of_mem {x : Fin (n + 1) → ℝ} (hx : x ∈ Simplex n) : rho x = x := by
  unfold rho
  have : ∑ i, |x i| = 1 := by
    rw [← hx.2]; exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (hx.1 i)
  simp [this]

lemma ne_zero_of_mem {x : Fin (n + 1) → ℝ} (hx : x ∈ Simplex n) : x ≠ 0 := by
  rintro rfl
  have := hx.2
  simp at this

lemma rho_mem {y : Fin (n + 1) → ℝ} (hy : ∀ i, 0 ≤ y i) (hy0 : y ≠ 0) : rho y ∈ Simplex n := by
  have hs := sum_abs_pos hy0
  refine ⟨fun i => ?_, ?_⟩
  · unfold rho
    exact mul_nonneg (inv_nonneg.mpr hs.le) (hy i)
  · unfold rho
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => (abs_of_nonneg (hy i)).symm]
    exact inv_mul_cancel₀ hs.ne'

lemma rho_eq_smul (y : Fin (n + 1) → ℝ) : rho y = (∑ i, |y i|)⁻¹ • y := rfl


end CannonFloydParry.S7

namespace CannonFloydParry.S7

open Matrix Set

variable {n : ℕ}

/-! ### Convex hulls of finite families -/

lemma mem_convexHull_range_iff' {E : Type*} [AddCommGroup E] [Module ℝ E]
    (u : Fin (n + 1) → E) (y : E) :
    y ∈ convexHull ℝ (range u) ↔ ∃ t ∈ stdSimplex ℝ (Fin (n + 1)), ∑ j, t j • u j = y := by
  constructor
  · intro hy
    refine convexHull_min (t := {y | ∃ t ∈ stdSimplex ℝ (Fin (n + 1)), ∑ j, t j • u j = y})
      ?_ ?_ hy
    · rintro _ ⟨j, rfl⟩
      refine ⟨Pi.single j 1, single_mem_stdSimplex ℝ j, ?_⟩
      simp [Pi.single_apply]
    · rintro y₁ ⟨t₁, ht₁, rfl⟩ y₂ ⟨t₂, ht₂, rfl⟩ a b ha hb hab
      refine ⟨a • t₁ + b • t₂, convex_stdSimplex ℝ _ ht₁ ht₂ ha hb hab, ?_⟩
      simp [add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
  · rintro ⟨t, ht, rfl⟩
    exact mem_convexHull_of_exists_fintype t u ht.1 ht.2 (fun j => mem_range_self j) rfl

lemma sum_smul_eq_of_single {E : Type*} [AddCommGroup E] [Module ℝ E]
    (u : Fin (n + 1) → E) {t : Fin (n + 1) → ℝ} (ht : t ∈ stdSimplex ℝ (Fin (n + 1)))
    (j : Fin (n + 1)) (h0 : ∀ k, k ≠ j → t k = 0) : ∑ k, t k • u k = u j := by
  have h1 : t j = 1 := by
    rw [← ht.2, Finset.sum_eq_single j (fun k _ hk => h0 k hk) (by simp)]
  rw [Finset.sum_eq_single j (fun k _ hk => by rw [h0 k hk, zero_smul]) (by simp), h1, one_smul]

lemma mem_extremePoints_of_affineIndependent {E : Type*} [AddCommGroup E] [Module ℝ E]
    {v : Fin (n + 1) → E} (hv : AffineIndependent ℝ v) (j : Fin (n + 1)) :
    v j ∈ (convexHull ℝ (range v)).extremePoints ℝ := by
  rw [mem_extremePoints]
  refine ⟨subset_convexHull ℝ _ (mem_range_self j), ?_⟩
  intro x₁ h₁ x₂ h₂ hseg
  obtain ⟨t₁, ht₁, rfl⟩ := (mem_convexHull_range_iff' v x₁).1 h₁
  obtain ⟨t₂, ht₂, rfl⟩ := (mem_convexHull_range_iff' v x₂).1 h₂
  obtain ⟨a, b, ha, hb, hab, h⟩ := hseg
  have hω := affineIndependent_iff.1 hv Finset.univ
    (fun k => a * t₁ k + b * t₂ k - if k = j then 1 else 0) (by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ht₁.2, ht₂.2,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      linarith) (by
      simp only [sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_smul,
        one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← smul_smul,
        ← Finset.smul_sum]
      rw [h, sub_self])
  have hz : ∀ k, k ≠ j → t₁ k = 0 ∧ t₂ k = 0 := by
    intro k hk
    have := hω k (Finset.mem_univ k)
    simp only [hk, if_false, sub_zero] at this
    have e1 := ht₁.1 k
    have e2 := ht₂.1 k
    constructor
    · nlinarith [mul_nonneg ha.le e1, mul_nonneg hb.le e2]
    · nlinarith [mul_nonneg ha.le e1, mul_nonneg hb.le e2]
  exact ⟨sum_smul_eq_of_single v ht₁ j fun k hk => (hz k hk).1,
    sum_smul_eq_of_single v ht₂ j fun k hk => (hz k hk).2⟩

lemma convexHull_subset_simplex {u : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hu : ∀ j, u j ∈ Simplex n) : convexHull ℝ (range u) ⊆ Simplex n :=
  convexHull_min (by rintro _ ⟨j, rfl⟩; exact hu j) (convex_stdSimplex ℝ _)

/-! ### Columns -/

/-- The `j`-th column of an integer matrix, as a real vector. -/
def colR (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (j : Fin (n + 1)) : Fin (n + 1) → ℝ :=
  fun i => (A i j : ℝ)

lemma glAct_eq_sum (A : GL (Fin (n + 1)) ℤ) (x : Fin (n + 1) → ℝ) :
    glAct A x = ∑ j, x j • colR (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) j := by
  ext i
  simp [glAct, Matrix.mulVec, dotProduct, Finset.sum_apply, colR, mul_comm]

lemma colR_eq_glAct (A : GL (Fin (n + 1)) ℤ) (j : Fin (n + 1)) :
    colR (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) j = glAct A (Pi.single j 1) := by
  rw [glAct_eq_sum]
  simp [Pi.single_apply]

lemma colR_ne_zero (A : GL (Fin (n + 1)) ℤ) (j : Fin (n + 1)) :
    colR (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) j ≠ 0 := by
  rw [colR_eq_glAct]
  exact glAct_ne_zero A (ne_zero_of_mem (single_mem_stdSimplex ℝ j))

lemma exists_pos_of_mem {x : Fin (n + 1) → ℝ} (hx : x ∈ Simplex n) : ∃ j, 0 < x j := by
  by_contra h
  push Not at h
  have : ∑ j, x j ≤ 0 := Finset.sum_nonpos fun j _ => h j
  rw [hx.2] at this
  norm_num at this

/-- The image of `Δₙ` under `ρ ∘ A`, for `A` with nonnegative entries, is the convex hull of the
projected columns. -/
lemma range_rho_glAct (A : GL (Fin (n + 1)) ℤ)
    (hA : ∀ i j, 0 ≤ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) i j) :
    range (fun x : Simplex n => rho (glAct A (x : Fin (n + 1) → ℝ))) =
      convexHull ℝ (range fun j => rho (colR (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) j)) := by
  set c := colR (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) with hc
  set u := fun j => rho (c j) with hu
  have hcnn : ∀ j i, 0 ≤ c j i := fun j i => by simp [hc, colR, hA i j]
  have hs : ∀ j, 0 < ∑ i, |c j i| := fun j => sum_abs_pos (colR_ne_zero A j)
  have hcu : ∀ j, c j = (∑ i, |c j i|) • u j := fun j => by
    simp only [hu, rho_eq_smul, smul_smul, mul_inv_cancel₀ (hs j).ne', one_smul]
  have humem : ∀ j, u j ∈ Simplex n := fun j => rho_mem (hcnn j) (colR_ne_zero A j)
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    have hx := x.2
    set T := ∑ j, (x : Fin (n + 1) → ℝ) j * ∑ i, |c j i| with hT
    have hTpos : 0 < T := by
      obtain ⟨j, hj⟩ := exists_pos_of_mem hx
      exact Finset.sum_pos' (fun k _ => mul_nonneg (hx.1 k) (hs k).le)
        ⟨j, Finset.mem_univ _, mul_pos hj (hs j)⟩
    have hAx : glAct A x = T • ∑ j, (T⁻¹ * ((x : Fin (n + 1) → ℝ) j * ∑ i, |c j i|)) • u j := by
      rw [glAct_eq_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, ← mul_assoc, mul_inv_cancel₀ hTpos.ne', one_mul, ← smul_smul, ← hcu]
    have hmem : ∑ j, (T⁻¹ * ((x : Fin (n + 1) → ℝ) j * ∑ i, |c j i|)) • u j ∈
        convexHull ℝ (range u) := by
      refine mem_convexHull_of_exists_fintype _ u (fun j => ?_) ?_ (fun j => mem_range_self j) rfl
      · exact mul_nonneg (inv_nonneg.mpr hTpos.le) (mul_nonneg (hx.1 j) (hs j).le)
      · rw [← Finset.mul_sum, inv_mul_cancel₀ hTpos.ne']
    show rho (glAct A x) ∈ _
    rw [hAx, rho_smul hTpos, rho_of_mem (convexHull_subset_simplex humem hmem)]
    exact hmem
  · intro hy
    obtain ⟨t, ht, rfl⟩ := (mem_convexHull_range_iff' u y).1 hy
    set x' : Fin (n + 1) → ℝ := fun j => t j / ∑ i, |c j i| with hx'
    set N := ∑ j, x' j with hN
    have hNpos : 0 < N := by
      obtain ⟨j, hj⟩ := exists_pos_of_mem ht
      exact Finset.sum_pos' (fun k _ => div_nonneg (ht.1 k) (hs k).le)
        ⟨j, Finset.mem_univ _, div_pos hj (hs j)⟩
    have hxmem : N⁻¹ • x' ∈ Simplex n := by
      refine ⟨fun j => ?_, ?_⟩
      · exact mul_nonneg (inv_nonneg.mpr hNpos.le) (div_nonneg (ht.1 j) (hs j).le)
      · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        exact inv_mul_cancel₀ hNpos.ne'
    refine ⟨⟨_, hxmem⟩, ?_⟩
    have hmem := (mem_convexHull_range_iff' u _).2 ⟨t, ht, rfl⟩
    show rho (glAct A (N⁻¹ • x')) = _
    rw [glAct_smul, rho_smul (inv_pos.mpr hNpos), glAct_eq_sum]
    have : ∑ j, x' j • c j = ∑ j, t j • u j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hcu j, smul_smul, hx', div_mul_cancel₀ _ (hs j).ne']
    rw [this, rho_of_mem (convexHull_subset_simplex humem hmem)]

/-! ### Primitive lifts -/

lemma sum_abs_intCast {w : Fin (n + 1) → ℤ} (hw : ∀ i, 0 ≤ w i) :
    ∑ i, |(w i : ℝ)| = ((∑ i, w i : ℤ) : ℝ) := by
  push_cast
  exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (by exact_mod_cast hw i)

lemma gcd_nonneg' (w : Fin (n + 1) → ℤ) : 0 ≤ Finset.univ.gcd w :=
  Int.nonneg_of_normalize_eq_self Finset.normalize_gcd

lemma ne_zero_of_gcd_eq_one {w : Fin (n + 1) → ℤ} (hg : Finset.univ.gcd w = 1) : w ≠ 0 := by
  rintro rfl
  have : Finset.univ.gcd (0 : Fin (n + 1) → ℤ) = 0 :=
    Finset.gcd_eq_zero_iff.2 fun _ _ => rfl
  rw [this] at hg
  exact zero_ne_one hg

lemma sum_pos_of_prim {w : Fin (n + 1) → ℤ} (hw : ∀ i, 0 ≤ w i) (hg : Finset.univ.gcd w = 1) :
    0 < ∑ i, w i := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (ne_zero_of_gcd_eq_one hg)
  exact Finset.sum_pos' (fun k _ => hw k) ⟨i, Finset.mem_univ _, lt_of_le_of_ne (hw i) (Ne.symm hi)⟩

lemma rho_intCast {w : Fin (n + 1) → ℤ} (hw : ∀ i, 0 ≤ w i) :
    rho (fun i => (w i : ℝ)) = ((∑ i, w i : ℤ) : ℝ)⁻¹ • (fun i => (w i : ℝ)) := by
  rw [rho_eq_smul, sum_abs_intCast hw]

lemma prim_unique {w w' : Fin (n + 1) → ℤ} (hw : ∀ i, 0 ≤ w i) (hw' : ∀ i, 0 ≤ w' i)
    (hg : Finset.univ.gcd w = 1) (hg' : Finset.univ.gcd w' = 1)
    (h : rho (fun i => (w i : ℝ)) = rho (fun i => (w' i : ℝ))) : w = w' := by
  rw [rho_intCast hw, rho_intCast hw'] at h
  set s := ∑ i, w i
  set s' := ∑ i, w' i
  have hs : 0 < s := sum_pos_of_prim hw hg
  have hs' : 0 < s' := sum_pos_of_prim hw' hg'
  have key : ∀ i, s' * w i = s * w' i := by
    intro i
    have := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    have hs0' : (s' : ℝ) ≠ 0 := by exact_mod_cast hs'.ne'
    field_simp at this
    exact_mod_cast (by linarith : (s' : ℝ) * w i = s * w' i)
  have d1 : s' ∣ s := by
    have : s' ∣ Finset.univ.gcd (fun i => s * w' i) :=
      Finset.dvd_gcd fun i _ => ⟨w i, (key i).symm⟩
    rwa [Finset.gcd_mul_left, hg', mul_one, Int.normalize_of_nonneg hs.le] at this
  have d2 : s ∣ s' := by
    have : s ∣ Finset.univ.gcd (fun i => s' * w i) :=
      Finset.dvd_gcd fun i _ => ⟨w' i, key i⟩
    rwa [Finset.gcd_mul_left, hg, mul_one, Int.normalize_of_nonneg hs'.le] at this
  have hss : s = s' := Int.dvd_antisymm hs.le hs'.le d2 d1
  funext i
  have := key i
  rw [hss] at this
  exact mul_left_cancel₀ hs'.ne' this

lemma lift_eq {w : Fin (n + 1) → ℤ} (hw : ∀ i, 0 ≤ w i) (hg : Finset.univ.gcd w = 1) :
    lift (rho (fun i => (w i : ℝ))) = w := by
  have hex : ∃ w' : Fin (n + 1) → ℤ, (∀ i, 0 ≤ w' i) ∧
      rho (fun i => (w' i : ℝ)) = rho (fun i => (w i : ℝ)) ∧ Finset.univ.gcd w' = 1 :=
    ⟨w, hw, rfl, hg⟩
  unfold lift
  rw [dif_pos hex]
  obtain ⟨h1, h2, h3⟩ := hex.choose_spec
  exact prim_unique h1 hw h3 hg h2

lemma exists_prim {x : Fin (n + 1) → ℝ} (hx : IsRationalPoint x) :
    ∃ w : Fin (n + 1) → ℤ, (∀ i, 0 ≤ w i) ∧ rho (fun i => (w i : ℝ)) = x ∧
      Finset.univ.gcd w = 1 := by
  choose q hq using hx.2
  set D : ℕ := ∏ i, (q i).den with hD
  have hDpos : (0 : ℝ) < D := by
    rw [hD]; push_cast
    exact Finset.prod_pos fun i _ => by exact_mod_cast (q i).den_pos
  set w0 : Fin (n + 1) → ℤ := fun i => (q i).num * ∏ j ∈ Finset.univ.erase i, ((q j).den : ℤ)
    with hw0
  have hw0x : ∀ i, (w0 i : ℝ) = D * x i := by
    intro i
    rw [hq i, hw0, hD]
    have hden : ((q i).den : ℝ) ≠ 0 := by exact_mod_cast (q i).den_ne_zero
    rw [← Finset.mul_prod_erase Finset.univ (fun j => (q j).den) (Finset.mem_univ i)]
    push_cast
    rw [Rat.cast_def]
    field_simp
  obtain ⟨g, hg, hgcd⟩ := Finset.extract_gcd w0 Finset.univ_nonempty
  set G := Finset.univ.gcd w0 with hG
  have hw0nn : ∀ i, 0 ≤ w0 i := fun i => by
    have : (0 : ℝ) ≤ w0 i := by rw [hw0x]; exact mul_nonneg hDpos.le (hx.1.1 i)
    exact_mod_cast this
  have hGpos : 0 < G := by
    refine lt_of_le_of_ne (gcd_nonneg' w0) (Ne.symm fun h0 => ?_)
    have hall := Finset.gcd_eq_zero_iff.1 h0
    obtain ⟨j, hj⟩ := exists_pos_of_mem hx.1
    have := hw0x j
    rw [hall j (Finset.mem_univ _)] at this
    push_cast at this
    nlinarith
  have hgnn : ∀ i, 0 ≤ g i := fun i => by
    have := hw0nn i
    rw [hg i (Finset.mem_univ _)] at this
    exact (mul_nonneg_iff_of_pos_left hGpos).mp this
  refine ⟨g, hgnn, ?_, hgcd⟩
  have hvec : (fun i => ((g i : ℤ) : ℝ)) = ((G : ℝ))⁻¹ • ((D : ℝ) • x) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← hw0x, hg i (Finset.mem_univ _)]
    have : (G : ℝ) ≠ 0 := by exact_mod_cast hGpos.ne'
    push_cast
    field_simp
  rw [hvec, rho_smul (inv_pos.mpr (by exact_mod_cast hGpos)), rho_smul hDpos, rho_of_mem hx.1]

lemma lift_spec {x : Fin (n + 1) → ℝ} (hx : IsRationalPoint x) :
    (∀ i, 0 ≤ lift x i) ∧ rho (fun i => (lift x i : ℝ)) = x ∧ Finset.univ.gcd (lift x) = 1 := by
  obtain ⟨w, hw, hrho, hg⟩ := exists_prim hx
  rw [← hrho, lift_eq hw hg]
  exact ⟨hw, rfl, hg⟩

lemma gcd_col_eq_one (A : GL (Fin (n + 1)) ℤ) (k : Fin (n + 1)) :
    Finset.univ.gcd (fun i => (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) i k) = 1 := by
  apply Int.eq_one_of_dvd_one (gcd_nonneg' _)
  have h1 : ((A⁻¹ : GL (Fin (n + 1)) ℤ) * (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)) k k = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
  rw [← h1, Matrix.mul_apply]
  exact Finset.dvd_sum fun i _ => Dvd.dvd.mul_left (Finset.gcd_dvd (Finset.mem_univ i)) _

end CannonFloydParry.S7

namespace CannonFloydParry.S7

open Matrix Set Module

variable {n : ℕ}

lemma lift_col_real {x : Fin (n + 1) → ℝ} (hx : IsRationalPoint x) :
    (fun i => (lift x i : ℝ)) = (∑ i, |(lift x i : ℝ)|) • x := by
  obtain ⟨hnn, hrho, hg⟩ := lift_spec hx
  have hne : (fun i => (lift x i : ℝ)) ≠ 0 := by
    intro h0
    apply ne_zero_of_gcd_eq_one hg
    funext i
    have := congrFun h0 i
    simpa using this
  have hs := sum_abs_pos hne
  have h := hrho
  rw [rho_eq_smul] at h
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
  rw [← hi]
  field_simp

lemma det_lift_ne_zero {v : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hv : ∀ j, IsRationalPoint (v j)) (hind : AffineIndependent ℝ v) :
    (Matrix.of fun i j => lift (v j) i).det ≠ 0 := by
  set W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := Matrix.of fun i j => lift (v j) i
  intro h0
  have hR : (W.map (Int.cast : ℤ → ℝ)).det = 0 := by
    have := (Int.castRingHom ℝ).map_det W
    rw [h0, map_zero] at this
    exact this.symm
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hR
  set s : Fin (n + 1) → ℝ := fun j => ∑ i, |(lift (v j) i : ℝ)|
  have hvec : ∑ j, (c j * s j) • v j = 0 := by
    rw [← hc]
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      Matrix.map_apply, W, Matrix.of_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := congrFun (lift_col_real (hv j)) i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [this]
    ring
  have hsum : ∑ j, c j * s j = 0 := by
    have := congrArg (fun z : Fin (n + 1) → ℝ => ∑ i, z i) hvec
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Finset.sum_const_zero] at this
    rw [Finset.sum_comm] at this
    simpa [← Finset.mul_sum, (hv _).1.2] using this
  have hall := affineIndependent_iff.1 hind Finset.univ _ hsum hvec
  apply hc0
  funext j
  have hsj : 0 < s j := by
    obtain ⟨_, _, hg⟩ := lift_spec (hv j)
    apply sum_abs_pos
    intro h0
    apply ne_zero_of_gcd_eq_one hg
    funext i
    have := congrFun h0 i
    simpa using this
  have := hall j (Finset.mem_univ j)
  simpa [hsj.ne'] using this

lemma ind_eq_natAbs_det {v : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hv : ∀ j, IsRationalPoint (v j)) (hind : AffineIndependent ℝ v) :
    ind v = (Matrix.of fun i j => lift (v j) i).det.natAbs := by
  set W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := Matrix.of fun i j => lift (v j) i with hW
  have hli : LinearIndependent ℤ (fun j => lift (v j)) :=
    Matrix.linearIndependent_cols_of_det_ne_zero (det_lift_ne_zero hv hind)
  set w := fun j => lift (v j)
  have hS : Submodule.span ℤ (range w) =
      (AddSubgroup.closure (range w)).toIntSubmodule := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.toAddSubgroup_toIntSubmodule]
  let bN := (Basis.span hli).map (LinearEquiv.ofEq _ _ hS)
  have := AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin (n + 1)))
    (AddSubgroup.closure (range w)) bN
  unfold ind
  rw [this, Basis.det_apply]
  congr 2
  ext i j
  simp only [Basis.toMatrix_apply, Pi.basisFun_repr, W, Matrix.of_apply]
  show ((bN j : _) : Fin (n + 1) → ℤ) i = _
  simp only [bN, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply, w]

theorem ind_ne_zero_and_eq_natAbs_det_and_eq_one_iff' {n : ℕ}
    {v : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hv : ∀ j, IsRationalPoint (v j)) (hind : AffineIndependent ℝ v) :
    ind v ≠ 0 ∧ ind v = (Matrix.of fun i j => lift (v j) i).det.natAbs ∧
      (ind v = 1 ↔ IsIntegralSubsimplex n (convexHull ℝ (Set.range v))) := by
  have hI := ind_eq_natAbs_det hv hind
  refine ⟨?_, hI, ?_⟩
  · rw [hI]
    exact Int.natAbs_ne_zero.mpr (det_lift_ne_zero hv hind)
  set W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := Matrix.of fun i j => lift (v j) i with hW
  constructor
  · intro h1
    rw [hI] at h1
    have hu : IsUnit W := (Matrix.isUnit_iff_isUnit_det W).2 (Int.isUnit_iff_natAbs_eq.2 h1)
    set U : GL (Fin (n + 1)) ℤ := hu.unit
    have hUW : (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) = W := hu.unit_spec
    have hnn : ∀ i j, 0 ≤ (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) i j := by
      intro i j
      rw [hUW]
      exact (lift_spec (hv j)).1 i
    have hpos : ∀ x : Simplex n, ∀ i, 0 ≤ glAct U (x : Fin (n + 1) → ℝ) i := by
      intro x i
      rw [glAct_eq_sum, Finset.sum_apply]
      exact Finset.sum_nonneg fun j _ =>
        mul_nonneg (x.2.1 j) (by simp only [colR]; exact_mod_cast hnn i j)
    let f : Simplex n → Simplex n := fun x =>
      ⟨rho (glAct U x), rho_mem (hpos x) (glAct_ne_zero U (ne_zero_of_mem x.2))⟩
    refine ⟨f, ⟨U, fun x _ => ⟨hpos x, rfl⟩⟩, ?_⟩
    show range (fun x : Simplex n => rho (glAct U (x : Fin (n + 1) → ℝ))) = _
    rw [range_rho_glAct U hnn]
    congr 2
    funext j
    have : colR (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) j = fun i => (lift (v j) i : ℝ) := by
      funext i; simp [colR, hUW, W]
    rw [this]
    exact (lift_spec (hv j)).2.1
  · rintro ⟨f, ⟨A, hA⟩, hrange⟩
    have hnn : ∀ i j, 0 ≤ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) i j := by
      intro i j
      have := (hA ⟨_, single_mem_stdSimplex ℝ j⟩ (mem_univ _)).1 i
      change 0 ≤ glAct A (Pi.single j 1) i at this
      rw [← colR_eq_glAct] at this
      have h' : (0 : ℝ) ≤ ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) i j : ℝ) := this
      exact_mod_cast h'
    have hf : (fun x => (f x : Fin (n + 1) → ℝ)) =
        fun x : Simplex n => rho (glAct A (x : Fin (n + 1) → ℝ)) := by
      funext x; exact (hA x (mem_univ _)).2
    rw [hf, range_rho_glAct A hnn] at hrange
    set u := fun j => rho (colR (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) j)
    have hmem : ∀ j, ∃ k, u k = v j := by
      intro j
      have := mem_extremePoints_of_affineIndependent hind j
      rw [← hrange] at this
      obtain ⟨k, hk⟩ := (extremePoints_convexHull_subset this : v j ∈ range u)
      exact ⟨k, hk⟩
    choose π hπ using hmem
    have hπinj : Function.Injective π := by
      intro j k h
      apply hind.injective
      rw [← hπ j, ← hπ k, h]
    let σ := Equiv.ofBijective π (Finite.injective_iff_bijective.mp hπinj)
    have hlift : ∀ j, lift (v j) = fun i => (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) i (π j) := by
      intro j
      rw [← hπ j]
      exact lift_eq (fun i => hnn i (π j)) (gcd_col_eq_one A (π j))
    have hWA : W = (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).submatrix id σ := by
      ext i j
      simp [W, hlift j, σ]
    rw [hI, hWA, Matrix.det_permute', Int.natAbs_mul, Int.cast_id, Int.units_natAbs, one_mul]
    exact Int.isUnit_iff_natAbs_eq.1 (Matrix.isUnits_det_units A)

end CannonFloydParry.S7

open CannonFloydParry in
theorem solution {n : ℕ} {v : Fin (n + 1) → Fin (n + 1) → ℝ}
    (hv : ∀ j, IsRationalPoint (v j)) (hind : AffineIndependent ℝ v) :
    ind v ≠ 0 ∧ ind v = (Matrix.of fun i j => lift (v j) i).det.natAbs ∧
      (ind v = 1 ↔ IsIntegralSubsimplex n (convexHull ℝ (Set.range v))) := by
  exact S7.ind_ne_zero_and_eq_natAbs_det_and_eq_one_iff' hv hind
