-- Prove2me | solution 1 for DepthOneQExp.gem_generation_small
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T07:31:20.667793+00:00
-- url     : https://prove2.me/submissions/119cd72a-a3a2-489a-968f-e31f471f9b79

import Mathlib
import Definitions.Def_DepthOneQExp_blockElem

namespace GemSmallAux

open Matrix

variable {R : Type*} [Ring R]

/-- row-0 GEM `E01(r1) E02(r2)` -/
def gC (r1 r2 : R) : Matrix (Fin 3) (Fin 3) R := !![1, r1, r2; 0, 1, 0; 0, 0, 1]
/-- column-0 GEM `E10(r1) E20(r2)` -/
def gB (r1 r2 : R) : Matrix (Fin 3) (Fin 3) R := !![1, 0, 0; r1, 1, 0; r2, 0, 1]
/-- `diag(h, 1, 1)` -/
def dg (h : R) : Matrix (Fin 3) (Fin 3) R := !![h, 0, 0; 0, 1, 0; 0, 0, 1]

@[simp] theorem gC_mul_0 (r1 r2 : R) (X : Matrix (Fin 3) (Fin 3) R) (j : Fin 3) :
    (gC r1 r2 * X) 0 j = X 0 j + r1 * X 1 j + r2 * X 2 j := by
  simp [gC, mul_apply, Fin.sum_univ_three]
@[simp] theorem gC_mul_1 (r1 r2 : R) (X : Matrix (Fin 3) (Fin 3) R) (j : Fin 3) :
    (gC r1 r2 * X) 1 j = X 1 j := by
  simp [gC, mul_apply, Fin.sum_univ_three]
@[simp] theorem gC_mul_2 (r1 r2 : R) (X : Matrix (Fin 3) (Fin 3) R) (j : Fin 3) :
    (gC r1 r2 * X) 2 j = X 2 j := by
  simp [gC, mul_apply, Fin.sum_univ_three]
@[simp] theorem gB_mul_0 (r1 r2 : R) (X : Matrix (Fin 3) (Fin 3) R) (j : Fin 3) :
    (gB r1 r2 * X) 0 j = X 0 j := by
  simp [gB, mul_apply, Fin.sum_univ_three]
@[simp] theorem gB_mul_1 (r1 r2 : R) (X : Matrix (Fin 3) (Fin 3) R) (j : Fin 3) :
    (gB r1 r2 * X) 1 j = X 1 j + r1 * X 0 j := by
  simp [gB, mul_apply, Fin.sum_univ_three]; abel
@[simp] theorem gB_mul_2 (r1 r2 : R) (X : Matrix (Fin 3) (Fin 3) R) (j : Fin 3) :
    (gB r1 r2 * X) 2 j = X 2 j + r2 * X 0 j := by
  simp [gB, mul_apply, Fin.sum_univ_three]; abel

theorem gC_mul_self (h2 : ∀ x : R, x + x = 0) (r1 r2 : R) : gC r1 r2 * gC r1 r2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gC, h2, one_apply]
theorem gB_mul_self (h2 : ∀ x : R, x + x = 0) (r1 r2 : R) : gB r1 r2 * gB r1 r2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gB, h2, one_apply]

theorem isUnit_of_two_sided {M : Type*} [Monoid M] {a b : M} (h1 : a * b = 1) (h2 : b * a = 1) :
    IsUnit a := ⟨⟨a, b, h1, h2⟩, rfl⟩

/-- left stable range one for triples -/
def SR (R : Type*) [Ring R] : Prop :=
  ∀ c0 c1 c2 a0 a1 a2 : R, a0 * c0 + a1 * c1 + a2 * c2 = 1 →
    ∃ y1 y2 : R, IsUnit (c0 + y1 * c1 + y2 * c2)

theorem SR_of_unitIdem (H : ∀ c : R, ∃ u e : R, IsUnit u ∧ e * e = e ∧ c = u * e) : SR R := by
  -- pair version first
  have pair : ∀ c0 c1 a0 a1 : R, a0 * c0 + a1 * c1 = 1 → ∃ y : R, IsUnit (c0 + y * c1) := by
    intro c0 c1 a0 a1 h
    obtain ⟨u, e, hu, he, rfl⟩ := H c0
    have hee : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
    have hfe : (1 - e) = a1 * c1 * (1 - e) := by
      calc (1 - e) = (a0 * (u * e) + a1 * c1) * (1 - e) := by rw [h, one_mul]
        _ = a0 * u * (e * (1 - e)) + a1 * c1 * (1 - e) := by noncomm_ring
        _ = a1 * c1 * (1 - e) := by rw [hee]; simp
    set n := (1 - e) * a1 * c1 * e with hn
    have hnn : n * n = 0 := by
      have : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
      calc n * n = (1 - e) * a1 * c1 * (e * (1 - e)) * a1 * c1 * e := by simp only [hn]; noncomm_ring
        _ = 0 := by rw [this]; simp
    have hw : e + (1 - e) * a1 * c1 = 1 + n := by
      have : (1 - e) * a1 * c1 = (1 - e) * a1 * c1 * e + (1 - e) * (a1 * c1 * (1 - e)) := by
        noncomm_ring
      have h11 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, hee, sub_zero]
      rw [this, ← hfe, h11]; simp only [hn]; noncomm_ring
    refine ⟨u * (1 - e) * a1, ?_⟩
    have : u * e + u * (1 - e) * a1 * c1 = u * (1 + n) := by
      rw [← hw]; noncomm_ring
    rw [this]
    refine hu.mul (isUnit_of_two_sided (b := 1 - n) ?_ ?_)
    · rw [mul_sub, mul_one, add_mul, one_mul, hnn]; abel
    · rw [sub_mul, one_mul, mul_add, mul_one, hnn]; abel
  intro c0 c1 c2 a0 a1 a2 h
  obtain ⟨y, hy⟩ := pair c0 (a1 * c1 + a2 * c2) a0 1 (by rw [one_mul, ← add_assoc, h])
  refine ⟨y * a1, y * a2, ?_⟩
  convert hy using 1
  noncomm_ring


def IsGem (g : Matrix (Fin 3) (Fin 3) R) : Prop := ∃ r1 r2 : R, g = gC r1 r2 ∨ g = gB r1 r2

theorem isGem_gC (r1 r2 : R) : IsGem (gC r1 r2) := ⟨r1, r2, Or.inl rfl⟩
theorem isGem_gB (r1 r2 : R) : IsGem (gB r1 r2) := ⟨r1, r2, Or.inr rfl⟩

theorem IsGem.mul_self (h2 : ∀ x : R, x + x = 0) {g : Matrix (Fin 3) (Fin 3) R} (hg : IsGem g) :
    g * g = 1 := by
  obtain ⟨r1, r2, rfl | rfl⟩ := hg
  · exact gC_mul_self h2 r1 r2
  · exact gB_mul_self h2 r1 r2

theorem IsGem.isUnit (h2 : ∀ x : R, x + x = 0) {g : Matrix (Fin 3) (Fin 3) R} (hg : IsGem g) :
    IsUnit g := isUnit_of_two_sided (hg.mul_self h2) (hg.mul_self h2)

theorem back_step (h2 : ∀ x : R, x + x = 0) {g X : Matrix (Fin 3) (Fin 3) R} (hg : IsGem g) :
    X = g * (g * X) := by rw [← mul_assoc, hg.mul_self h2, one_mul]

theorem entry_of_eq_one {X Y : Matrix (Fin 3) (Fin 3) R} (h : Y * X = 1) (i j : Fin 3) :
    Y i 0 * X 0 j + Y i 1 * X 1 j + Y i 2 * X 2 j = if i = j then 1 else 0 := by
  have := congrFun (congrFun h i) j
  simpa [mul_apply, Fin.sum_univ_three, one_apply, add_assoc] using this

set_option maxHeartbeats 1000000 in
theorem reduce (h2 : ∀ x : R, x + x = 0) (hsr : SR R) (X : Matrix (Fin 3) (Fin 3) R)
    (hX : IsUnit X) :
    ∃ g1 g2 g3 g4 g5 g6 g7 : Matrix (Fin 3) (Fin 3) R, IsGem g1 ∧ IsGem g2 ∧ IsGem g3 ∧
      IsGem g4 ∧ IsGem g5 ∧ IsGem g6 ∧ IsGem g7 ∧
      ∃ h : R, IsUnit h ∧ X = g1 * (g2 * (g3 * (g4 * (g5 * (g6 * (g7 * dg h)))))) := by
  -- step 1
  obtain ⟨Y, hYX⟩ := hX.exists_left_inv
  obtain ⟨y1, y2, hu⟩ := hsr (X 0 2) (X 1 2) (X 2 2) (Y 2 0) (Y 2 1) (Y 2 2)
    (by simpa using entry_of_eq_one hYX 2 2)
  set g1 := gC y1 y2 with hg1
  set X1 := g1 * X with hX1
  have hX1u : IsUnit X1 := ((isGem_gC y1 y2).isUnit h2).mul hX
  have e102 : X1 0 2 = X 0 2 + y1 * X 1 2 + y2 * X 2 2 := gC_mul_0 _ _ _ _
  rw [← e102] at hu
  obtain ⟨⟨a, ai, ha1, ha2⟩, ha⟩ := hu
  change a = X1 0 2 at ha
  -- step 2
  set g2 := gB (-(X1 1 2) * ai) ((1 - X1 2 2) * ai) with hg2
  set X2 := g2 * X1 with hX2
  have hX2u : IsUnit X2 := ((isGem_gB _ _).isUnit h2).mul hX1u
  have e202 : X2 0 2 = X1 0 2 := gB_mul_0 _ _ _ _
  have e212 : X2 1 2 = 0 := by
    rw [hX2, gB_mul_1, ← ha, mul_assoc, ha2]; simp
  have e222 : X2 2 2 = 1 := by
    rw [hX2, gB_mul_2, ← ha, mul_assoc, ha2]; simp
  -- step 3
  set g3 := gC 0 (-(X2 0 2)) with hg3
  set X3 := g3 * X2 with hX3
  have hX3u : IsUnit X3 := ((isGem_gC _ _).isUnit h2).mul hX2u
  have e302 : X3 0 2 = 0 := by rw [hX3, gC_mul_0, e222]; simp
  have e312 : X3 1 2 = 0 := by rw [hX3, gC_mul_1, e212]
  have e322 : X3 2 2 = 1 := by rw [hX3, gC_mul_2, e222]
  -- step 4
  obtain ⟨Y3, hY3⟩ := hX3u.exists_left_inv
  have hY312 : Y3 1 2 = 0 := by
    simpa [e302, e312, e322] using entry_of_eq_one hY3 1 2
  obtain ⟨z1, z2, hv⟩ := hsr (X3 0 1) (X3 1 1) 0 (Y3 1 0) (Y3 1 1) 0
    (by simpa [hY312] using entry_of_eq_one hY3 1 1)
  set g4 := gC z1 0 with hg4
  set X4 := g4 * X3 with hX4
  have hX4u : IsUnit X4 := ((isGem_gC _ _).isUnit h2).mul hX3u
  have e401 : X4 0 1 = X3 0 1 + z1 * X3 1 1 + z2 * 0 := by rw [hX4, gC_mul_0]; simp
  have e402 : X4 0 2 = 0 := by rw [hX4, gC_mul_0, e302, e312]; simp
  have e412 : X4 1 2 = 0 := by rw [hX4, gC_mul_1, e312]
  have e422 : X4 2 2 = 1 := by rw [hX4, gC_mul_2, e322]
  rw [← e401] at hv
  obtain ⟨⟨b, bi, hb1, hb2⟩, hb⟩ := hv
  change b = X4 0 1 at hb
  -- step 5
  set g5 := gB ((1 - X4 1 1) * bi) (-(X4 2 1) * bi) with hg5
  set X5 := g5 * X4 with hX5
  have hX5u : IsUnit X5 := ((isGem_gB _ _).isUnit h2).mul hX4u
  have e501 : X5 0 1 = X4 0 1 := gB_mul_0 _ _ _ _
  have e511 : X5 1 1 = 1 := by rw [hX5, gB_mul_1, ← hb, mul_assoc, hb2]; simp
  have e521 : X5 2 1 = 0 := by rw [hX5, gB_mul_2, ← hb, mul_assoc, hb2]; simp
  have e502 : X5 0 2 = 0 := by rw [hX5, gB_mul_0, e402]
  have e512 : X5 1 2 = 0 := by rw [hX5, gB_mul_1, e412, e402]; simp
  have e522 : X5 2 2 = 1 := by rw [hX5, gB_mul_2, e422, e402]; simp
  -- step 6
  set g6 := gC (-(X5 0 1)) 0 with hg6
  set X6 := g6 * X5 with hX6
  have hX6u : IsUnit X6 := ((isGem_gC _ _).isUnit h2).mul hX5u
  have e601 : X6 0 1 = 0 := by rw [hX6, gC_mul_0, e511, e521]; simp
  have e602 : X6 0 2 = 0 := by rw [hX6, gC_mul_0, e502, e512]; simp
  have e611 : X6 1 1 = 1 := by rw [hX6, gC_mul_1, e511]
  have e621 : X6 2 1 = 0 := by rw [hX6, gC_mul_2, e521]
  have e612 : X6 1 2 = 0 := by rw [hX6, gC_mul_1, e512]
  have e622 : X6 2 2 = 1 := by rw [hX6, gC_mul_2, e522]
  -- step 7
  obtain ⟨⟨X6', Y6, hXY6, hYX6⟩, hX6'⟩ := hX6u
  change X6' = X6 at hX6'
  rw [hX6'] at hXY6 hYX6
  have k1 : X6 0 0 * Y6 0 0 = 1 := by
    simpa [e601, e602] using entry_of_eq_one hXY6 0 0
  have k2 : Y6 0 1 = 0 := by
    simpa [e601, e611, e621] using entry_of_eq_one hYX6 0 1
  have k3 : Y6 0 2 = 0 := by
    simpa [e602, e612, e622] using entry_of_eq_one hYX6 0 2
  have k4 : Y6 0 0 * X6 0 0 = 1 := by
    simpa [k2, k3] using entry_of_eq_one hYX6 0 0
  set g7 := gB (-(X6 1 0) * Y6 0 0) (-(X6 2 0) * Y6 0 0) with hg7
  have e7 : g7 * X6 = dg (X6 0 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hg7, dg, e601, e602, e611, e621, e612, e622, mul_assoc, k4]
  refine ⟨g1, g2, g3, g4, g5, g6, g7, isGem_gC _ _, isGem_gB _ _, isGem_gC _ _, isGem_gC _ _,
    isGem_gB _ _, isGem_gC _ _, isGem_gB _ _, X6 0 0, isUnit_of_two_sided k1 k4, ?_⟩
  rw [← e7, ← back_step h2 (isGem_gB _ _), hX6, ← back_step h2 (isGem_gC _ _), hX5,
    ← back_step h2 (isGem_gB _ _), hX4, ← back_step h2 (isGem_gC _ _), hX3,
    ← back_step h2 (isGem_gC _ _), hX2, ← back_step h2 (isGem_gB _ _), hX1,
    ← back_step h2 (isGem_gC _ _)]

theorem unitIdem_matrix {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [Field 𝕜]
    (M : Matrix n n 𝕜) : ∃ u e : Matrix n n 𝕜, IsUnit u ∧ e * e = e ∧ M = u * e := by
  classical
  obtain ⟨L, L', D, hM⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  set P := (L.map TransvectionStruct.toMatrix).prod
  set Q := (L'.map TransvectionStruct.toMatrix).prod
  have hP : IsUnit P.det := by simp [P, TransvectionStruct.det_toMatrix_prod]
  have hQ : IsUnit Q.det := by simp [Q, TransvectionStruct.det_toMatrix_prod]
  set u0 : n → 𝕜 := fun i => if D i = 0 then 1 else D i
  set e0 : n → 𝕜 := fun i => if D i = 0 then 0 else 1
  have hD : diagonal D = diagonal u0 * diagonal e0 := by
    rw [diagonal_mul_diagonal]; congr 1; funext i; simp only [u0, e0]; split_ifs with h <;> simp [h]
  have hu0 : IsUnit (diagonal u0) := by
    refine isUnit_of_two_sided (b := diagonal fun i => (u0 i)⁻¹) ?_ ?_ <;>
    · rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
      simp only [u0]; split_ifs with h <;> simp [h]
  have he0 : diagonal e0 * diagonal e0 = diagonal e0 := by
    rw [diagonal_mul_diagonal]; congr 1; funext i; simp only [e0]; split_ifs <;> simp
  refine ⟨P * diagonal u0 * Q, Q⁻¹ * diagonal e0 * Q, ?_, ?_, ?_⟩
  · refine ((isUnit_iff_isUnit_det P).2 hP |>.mul hu0).mul ((isUnit_iff_isUnit_det Q).2 hQ)
  · calc Q⁻¹ * diagonal e0 * Q * (Q⁻¹ * diagonal e0 * Q)
          = Q⁻¹ * diagonal e0 * (Q * Q⁻¹) * diagonal e0 * Q := by simp only [mul_assoc]
      _ = Q⁻¹ * diagonal e0 * Q := by rw [mul_nonsing_inv Q hQ, mul_one, mul_assoc (Q⁻¹), he0]
  · calc M = P * diagonal u0 * diagonal e0 * Q := by rw [hM, hD]; simp only [mul_assoc]
      _ = P * diagonal u0 * (Q * Q⁻¹) * diagonal e0 * Q := by rw [mul_nonsing_inv Q hQ, mul_one]
      _ = _ := by simp only [mul_assoc]

theorem dg_mul (h k : R) : dg (h * k) = dg h * dg k := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, mul_apply, Fin.sum_univ_three]

theorem dg_one : dg (1 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, one_apply]

theorem gC_zero : gC (0 : R) 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gC, one_apply]

theorem dg_one_add (h2 : ∀ x : R, x + x = 0) (a b : R) (hba : b * a = 0) :
    dg (1 + a * b) = [gC a 0, gB b 0, gC a 0, gB b 0].prod := by
  have e1 : gC a 0 * gB b 0 = !![1 + a * b, a, 0; b, 1, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gC, gB, mul_apply, Fin.sum_univ_three]
  have e2 : (!![1 + a * b, a, 0; b, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) R) *
      !![1 + a * b, a, 0; b, 1, 0; 0, 0, 1] = dg (1 + a * b) := by
    have hab : a * b * (a * b) = 0 := by rw [mul_assoc, ← mul_assoc b, hba]; simp
    have haba : a * b * a = 0 := by rw [mul_assoc, hba, mul_zero]
    have hbab : b * (a * b) = 0 := by rw [← mul_assoc, hba, zero_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dg, mul_apply, Fin.sum_univ_three, mul_add, add_mul, hab, haba, hbab, hba, h2,
        add_assoc]
  simp only [List.prod_cons, List.prod_nil, mul_one]
  rw [← e2, ← e1]; simp only [mul_assoc]

theorem exists_ofFn {α : Type*} (L : List α) {n : ℕ} (hn : L.length = n) :
    ∃ γ : Fin n → α, List.ofFn γ = L := by
  subst hn; exact ⟨L.get, List.ofFn_get L⟩

theorem pad12 (W : List (Matrix (Fin 3) (Fin 3) R)) (hW : W.length ≤ 12) (hg : ∀ g ∈ W, IsGem g) :
    ∃ L : List (Matrix (Fin 3) (Fin 3) R), L.length = 12 ∧ (∀ g ∈ L, IsGem g) ∧ L.prod = W.prod := by
  refine ⟨W ++ List.replicate (12 - W.length) (gC 0 0), by simp; omega, ?_, ?_⟩
  · intro g hgm
    rcases List.mem_append.1 hgm with h | h
    · exact hg g h
    · rw [List.eq_of_mem_replicate h]; exact isGem_gC _ _
  · simp [gC_zero]

/-- every unit of `Mat_s(𝔽₂)`, `s ∈ {1,2}`, has `diag(h,1,1)` a product of `12` GEMs -/
theorem dg_decomp (s : ℕ) (hs : s = 1 ∨ s = 2) (h : Matrix (Fin s) (Fin s) (ZMod 2))
    (hh : IsUnit h) :
    ∃ L : List (Matrix (Fin 3) (Fin 3) (Matrix (Fin s) (Fin s) (ZMod 2))), L.length = 12 ∧
      (∀ g ∈ L, IsGem g) ∧ dg h = L.prod := by
  have hdet : h.det ≠ 0 := ((isUnit_iff_isUnit_det h).1 hh).ne_zero
  rcases hs with rfl | rfl
  · have : h = 1 := by
      have h00 : h 0 0 = 1 := by
        rw [det_unique] at hdet
        revert hdet; generalize h 0 0 = x; revert x; decide
      ext i j
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0, h00]; rfl
    obtain ⟨L, hL, hg, hp⟩ := pad12 ([] : List (Matrix (Fin 3) (Fin 3) (Matrix (Fin 1) (Fin 1) (ZMod 2))))
      (by simp) (by simp)
    exact ⟨L, hL, hg, by rw [hp, this, dg_one]; rfl⟩
  · have h2 : ∀ x : Matrix (Fin 2) (Fin 2) (ZMod 2), x + x = 0 := by
      intro x; ext i j; simp only [Matrix.add_apply, Matrix.zero_apply]; generalize x i j = c; revert c; decide
    set A1 : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 0, 0]
    set B1 : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 0; 0, 1]
    set A2 : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 0; 1, 0]
    set B2 : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1, 0; 0, 0]
    set W1 := [gC A1 0, gB B1 0, gC A1 0, gB B1 0]
    set W2 := [gC A2 0, gB B2 0, gC A2 0, gB B2 0]
    have hW1 : ∀ g ∈ W1, IsGem g := by
      simp only [W1, List.mem_cons, List.not_mem_nil, or_false]
      rintro g (rfl | rfl | rfl | rfl) <;> first | exact isGem_gC _ _ | exact isGem_gB _ _
    have hW2 : ∀ g ∈ W2, IsGem g := by
      simp only [W2, List.mem_cons, List.not_mem_nil, or_false]
      rintro g (rfl | rfl | rfl | rfl) <;> first | exact isGem_gC _ _ | exact isGem_gB _ _
    have t1 : dg (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod 2)) = W1.prod := by
      rw [← dg_one_add h2 A1 B1 (by decide)]; congr 1; simp only [A1, B1]; decide
    have t2 : dg (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) (ZMod 2)) = W2.prod := by
      rw [← dg_one_add h2 A2 B2 (by decide)]; congr 1; simp only [A2, B2]; decide
    have hcases : h = 1 ∨ h = !![1, 1; 0, 1] ∨ h = !![1, 0; 1, 1] ∨ h = !![0, 1; 1, 1] ∨
        h = !![1, 1; 1, 0] ∨ h = !![0, 1; 1, 0] := by
      rw [det_fin_two] at hdet
      rw [eta_fin_two h]
      revert hdet
      generalize h 0 0 = a; generalize h 0 1 = b; generalize h 1 0 = c; generalize h 1 1 = d
      revert a b c d; decide
    have fin : ∀ W : List (Matrix (Fin 3) (Fin 3) (Matrix (Fin 2) (Fin 2) (ZMod 2))),
        W.length ≤ 12 → (∀ g ∈ W, IsGem g) → dg h = W.prod →
        ∃ L : List (Matrix (Fin 3) (Fin 3) (Matrix (Fin 2) (Fin 2) (ZMod 2))), L.length = 12 ∧
          (∀ g ∈ L, IsGem g) ∧ dg h = L.prod := by
      intro W hl hg hp
      obtain ⟨L, hL, hgL, hpL⟩ := pad12 W hl hg
      exact ⟨L, hL, hgL, by rw [hpL, hp]⟩
    have mem2 : ∀ (U V : List (Matrix (Fin 3) (Fin 3) (Matrix (Fin 2) (Fin 2) (ZMod 2)))),
        (∀ g ∈ U, IsGem g) → (∀ g ∈ V, IsGem g) → ∀ g ∈ U ++ V, IsGem g := by
      intro U V hU hV g hgm
      rcases List.mem_append.1 hgm with h | h
      · exact hU g h
      · exact hV g h
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact fin [] (by simp) (by simp) (by rw [dg_one]; rfl)
    · exact fin W1 (by simp [W1]) hW1 t1
    · exact fin W2 (by simp [W2]) hW2 t2
    · refine fin (W1 ++ W2) (by simp [W1, W2]) (mem2 _ _ hW1 hW2) ?_
      rw [List.prod_append, ← t1, ← t2, ← dg_mul]; congr 1; decide
    · refine fin (W2 ++ W1) (by simp [W1, W2]) (mem2 _ _ hW2 hW1) ?_
      rw [List.prod_append, ← t1, ← t2, ← dg_mul]; congr 1; decide
    · refine fin (W1 ++ W2 ++ W1) (by simp [W1, W2]) (mem2 _ _ (mem2 _ _ hW1 hW2) hW1) ?_
      rw [List.prod_append, List.prod_append, ← t1, ← t2, ← dg_mul, ← dg_mul]; congr 1; decide

/-- the block-level statement: every unit of `M₃(Mat_s(𝔽₂))`, `s ∈ {1,2}`, is a product of
`19` GEMs of row-0 / column-0 type -/
theorem M3_main (s : ℕ) (hs : s = 1 ∨ s = 2)
    (X : Matrix (Fin 3) (Fin 3) (Matrix (Fin s) (Fin s) (ZMod 2))) (hX : IsUnit X) :
    ∃ γ : Fin 19 → Matrix (Fin 3) (Fin 3) (Matrix (Fin s) (Fin s) (ZMod 2)),
      (∀ k, IsGem (γ k)) ∧ X = (List.ofFn γ).prod := by
  have h2 : ∀ x : Matrix (Fin s) (Fin s) (ZMod 2), x + x = 0 := by
    intro x; ext i j; simp only [Matrix.add_apply, Matrix.zero_apply]; generalize x i j = c; revert c; decide
  have hsr : SR (Matrix (Fin s) (Fin s) (ZMod 2)) := SR_of_unitIdem unitIdem_matrix
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, h1, h2', h3, h4, h5, h6, h7, h, hh, hX⟩ :=
    reduce h2 hsr X hX
  obtain ⟨L, hL, hgL, hpL⟩ := dg_decomp s hs h hh
  obtain ⟨γ, hγ⟩ := exists_ofFn ([g1, g2, g3, g4, g5, g6, g7] ++ L) (n := 19) (by simp [hL])
  refine ⟨γ, ?_, ?_⟩
  · intro k
    have hk : γ k ∈ List.ofFn γ := (List.mem_ofFn' γ (γ k)).2 ⟨k, rfl⟩
    rw [hγ] at hk
    rcases List.mem_append.1 hk with hk | hk
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with e | e | e | e | e | e | e <;> rw [e] <;> assumption
    · exact hgL _ hk
  · rw [hγ, List.prod_append, ← hpL, hX]; simp [mul_assoc]

theorem gC_eq_single (r1 r2 : R) :
    gC r1 r2 = (1 + single 0 1 r1) * (1 + single 0 2 r2) := by
  have h0 : (single 0 1 r1 : Matrix (Fin 3) (Fin 3) R) * single 0 2 r2 = 0 :=
    single_mul_single_of_ne _ _ _ _ (by decide) _
  rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, h0, add_zero]
  ext i j : 2
  fin_cases i <;> fin_cases j <;> simp [gC, one_apply]

theorem gB_eq_single (r1 r2 : R) :
    gB r1 r2 = (1 + single 1 0 r1) * (1 + single 2 0 r2) := by
  have h0 : (single 1 0 r1 : Matrix (Fin 3) (Fin 3) R) * single 2 0 r2 = 0 :=
    single_mul_single_of_ne _ _ _ _ (by decide) _
  rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, h0, add_zero]
  ext i j : 2
  fin_cases i <;> fin_cases j <;> simp [gB, one_apply]

/-- block view `M₃(Mat_s(𝔽₂)) ≃+* Mat_{3s}(𝔽₂)` -/
def Φ (s : ℕ) : Matrix (Fin 3) (Fin 3) (Matrix (Fin s) (Fin s) (ZMod 2)) ≃+*
    Matrix (Fin (3 * s)) (Fin (3 * s)) (ZMod 2) :=
  (compRingEquiv (Fin 3) (Fin s) (ZMod 2)).trans (reindexRingEquiv (ZMod 2) finProdFinEquiv)

theorem blockElem_eq_Φ (s : ℕ) (a b : Fin 3) (r : Matrix (Fin s) (Fin s) (ZMod 2)) :
    DepthOneQExp.blockElem s a b r = Φ s (1 + single a b r) := by
  have e : DepthOneQExp.blockElem s a b r = reindexRingEquiv (ZMod 2) finProdFinEquiv
      ((1 : Matrix (Fin 3 × Fin s) (Fin 3 × Fin s) (ZMod 2)) +
        Matrix.of fun p q => if p.1 = a ∧ q.1 = b then r p.2 q.2 else 0) := rfl
  rw [e, Φ, RingEquiv.trans_apply, map_add (compRingEquiv (Fin 3) (Fin s) (ZMod 2)), map_one]
  congr 2
  ext p q
  simp only [compRingEquiv_apply, comp_apply, of_apply, single_apply]
  by_cases h : p.1 = a ∧ q.1 = b
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]; rfl

/-- the row-0 GEM `E01(a) E02(b)` in `SL(3s; 𝔽₂)` -/
def sC (s : ℕ) (a b : Matrix (Fin s) (Fin s) (ZMod 2)) :
    Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) :=
  (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from
    ⟨DepthOneQExp.blockElem s 0 1 a, DepthOneQExp.det_blockElem s (by decide) a⟩) *
  (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from
    ⟨DepthOneQExp.blockElem s 0 2 b, DepthOneQExp.det_blockElem s (by decide) b⟩)

/-- the column-0 GEM `E10(a) E20(b)` in `SL(3s; 𝔽₂)` -/
def sB (s : ℕ) (a b : Matrix (Fin s) (Fin s) (ZMod 2)) :
    Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) :=
  (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from
    ⟨DepthOneQExp.blockElem s 1 0 a, DepthOneQExp.det_blockElem s (by decide) a⟩) *
  (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from
    ⟨DepthOneQExp.blockElem s 2 0 b, DepthOneQExp.det_blockElem s (by decide) b⟩)

theorem coe_sC (s : ℕ) (a b : Matrix (Fin s) (Fin s) (ZMod 2)) :
    ((sC s a b : Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2)) :
      Matrix (Fin (3 * s)) (Fin (3 * s)) (ZMod 2)) = Φ s (gC a b) := by
  rw [gC_eq_single, map_mul, ← blockElem_eq_Φ, ← blockElem_eq_Φ]; rfl

theorem coe_sB (s : ℕ) (a b : Matrix (Fin s) (Fin s) (ZMod 2)) :
    ((sB s a b : Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2)) :
      Matrix (Fin (3 * s)) (Fin (3 * s)) (ZMod 2)) = Φ s (gB a b) := by
  rw [gB_eq_single, map_mul, ← blockElem_eq_Φ, ← blockElem_eq_Φ]; rfl

end GemSmallAux

open GemSmallAux DepthOneQExp in
theorem solution (s : ℕ) (hs1 : 1 ≤ s) (hs2 : s ≤ 2)
    (g : Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2)) :
    ∃ h : Fin 19 → Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2),
      (∀ k, ∃ r₁ r₂ : Matrix (Fin s) (Fin s) (ZMod 2),
        h k = (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 0 2 r₁, det_blockElem s (by decide) r₁⟩) * (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 1 2 r₂, det_blockElem s (by decide) r₂⟩) ∨ h k = (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 1 0 r₁, det_blockElem s (by decide) r₁⟩) * (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 2 0 r₂, det_blockElem s (by decide) r₂⟩) ∨
        h k = (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 0 1 r₁, det_blockElem s (by decide) r₁⟩) * (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 0 2 r₂, det_blockElem s (by decide) r₂⟩) ∨ h k = (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 2 0 r₁, det_blockElem s (by decide) r₁⟩) * (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 2 1 r₂, det_blockElem s (by decide) r₂⟩)) ∧
      g = (List.ofFn h).prod := by
  classical
  have hs : s = 1 ∨ s = 2 := by omega
  set X := (Φ s).symm (g : Matrix (Fin (3 * s)) (Fin (3 * s)) (ZMod 2)) with hXdef
  have hX : IsUnit X := by
    have : IsUnit (g : Matrix (Fin (3 * s)) (Fin (3 * s)) (ZMod 2)) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (by rw [g.2]; exact isUnit_one)
    exact this.map (Φ s).symm
  obtain ⟨γ, hγ, hXγ⟩ := M3_main s hs X hX
  choose r1 r2 hr using hγ
  let h : Fin 19 → Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) := fun k =>
    if γ k = gC (r1 k) (r2 k) then sC s (r1 k) (r2 k) else sB s (r1 k) (r2 k)
  have hh : ∀ k, ((h k : Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2)) :
      Matrix (Fin (3 * s)) (Fin (3 * s)) (ZMod 2)) = Φ s (γ k) := by
    intro k
    simp only [h]
    split_ifs with hk
    · rw [coe_sC, hk]
    · rw [coe_sB, (hr k).resolve_left hk]
  refine ⟨h, fun k => ⟨r1 k, r2 k, ?_⟩, ?_⟩
  · simp only [h]
    split_ifs with hk
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inl rfl)
  · apply Subtype.ext
    have e1 : (g : Matrix (Fin (3 * s)) (Fin (3 * s)) (ZMod 2)) = Φ s X := by
      rw [hXdef, RingEquiv.apply_symm_apply]
    have e2 : ((List.ofFn h).prod : Matrix (Fin (3 * s)) (Fin (3 * s)) (ZMod 2)) =
        (List.ofFn fun k => Φ s (γ k)).prod := by
      rw [← Matrix.SpecialLinearGroup.coeMonoidHom_apply, map_list_prod, List.map_ofFn]
      congr 1
      exact List.ofFn_inj.2 (funext fun k => hh k)
    rw [e1, e2, hXγ, map_list_prod, List.map_ofFn]
    rfl
