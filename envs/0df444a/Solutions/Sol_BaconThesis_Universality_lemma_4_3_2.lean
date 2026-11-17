-- Prove2me | solution 1 for BaconThesis.Universality.lemma_4_3_2
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T19:13:33.056732+00:00
-- url     : https://prove2.me/submissions/9ec47c83-b64c-4d11-b54b-042299ed5b41

import Mathlib
import Definitions.Def_BaconThesis_Universality_denseGen
import Definitions.Def_BaconThesis_Universality_compGraph

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace BaconThesis.Universality.Sol432

open BaconThesis.Universality Matrix

section Lift

variable {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]

/-- The isometry `ℂ^k → ℂ^m` sending `e_s` to `e_{f s}`. -/
def col (f : k → m) : Matrix m k ℂ := fun i s => if i = f s then 1 else 0

lemma colT_mul (f : k → m) {l : Type*} (A : Matrix m l ℂ) (s : k) (j : l) :
    ((col f)ᵀ * A) s j = A (f s) j := by
  simp [col, Matrix.mul_apply]

lemma col_mul_mem (f : k → m) (hf : Function.Injective f) {l : Type*} (B : Matrix k l ℂ)
    (s : k) (j : l) : (col f * B) (f s) j = B s j := by
  simp [col, Matrix.mul_apply, hf.eq_iff]

lemma col_mul_not (f : k → m) {l : Type*} (B : Matrix k l ℂ) (i : m) (hi : ∀ s, i ≠ f s)
    (j : l) : (col f * B) i j = 0 := by
  simp [col, Matrix.mul_apply, hi]

lemma colT_mul_col (f : k → m) (hf : Function.Injective f) : (col f)ᵀ * col f = 1 := by
  ext s t
  rw [colT_mul]
  simp [col, Matrix.one_apply, hf.eq_iff]

lemma col_conjTranspose (f : k → m) : (col f)ᴴ = (col f)ᵀ := by
  ext s i
  simp only [conjTranspose_apply, transpose_apply, col]
  split_ifs <;> simp

/-- `M` acting on the span of the `e_{f s}`, the identity on the other basis vectors. -/
def lift (f : k → m) (M : Matrix k k ℂ) : Matrix m m ℂ := 1 + col f * (M - 1) * (col f)ᵀ

lemma lift_one (f : k → m) : lift f 1 = 1 := by simp [lift]

lemma lift_mul (f : k → m) (hf : Function.Injective f) (M N : Matrix k k ℂ) :
    lift f M * lift f N = lift f (M * N) := by
  unfold lift
  have h := colT_mul_col f hf
  have h2 : col f * (M - 1) * (col f)ᵀ * (col f * (N - 1) * (col f)ᵀ)
      = col f * ((M - 1) * (N - 1)) * (col f)ᵀ := by
    calc _ = col f * (M - 1) * ((col f)ᵀ * col f) * (N - 1) * (col f)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have e : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by noncomm_ring
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, h2, e, Matrix.mul_add,
    Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  abel

lemma lift_conjTranspose (f : k → m) (M : Matrix k k ℂ) : (lift f M)ᴴ = lift f Mᴴ := by
  unfold lift
  rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul, conjTranspose_one,
    col_conjTranspose, conjTranspose_sub, conjTranspose_one]
  have : (col f)ᵀᴴ = col f := by
    rw [← col_conjTranspose, conjTranspose_conjTranspose]
  rw [this, Matrix.mul_assoc]

lemma lift_det (f : k → m) (hf : Function.Injective f) (M : Matrix k k ℂ) :
    (lift f M).det = M.det := by
  unfold lift
  rw [Matrix.mul_assoc, det_one_add_mul_comm, Matrix.mul_assoc, colT_mul_col f hf,
    Matrix.mul_one, add_sub_cancel]

lemma lift_SU (f : k → m) (hf : Function.Injective f) (M : Matrix k k ℂ)
    (hM : M ∈ specialUnitaryGroup k ℂ) : lift f M ∈ specialUnitaryGroup m ℂ := by
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff, star_eq_conjTranspose] at hM ⊢
  rw [lift_conjTranspose, lift_mul f hf, hM.1, lift_one, lift_det f hf]
  exact ⟨rfl, hM.2⟩

lemma lift_unit (f : k → m) (hf : Function.Injective f) (M : Matrix k k ℂ) (hM : M * Mᴴ = 1) :
    lift f M * (lift f M)ᴴ = 1 := by
  rw [lift_conjTranspose, lift_mul f hf, hM, lift_one]

lemma sperm_conj (σ : m → m) (hσ : Function.Involutive σ) (ε : m → ℂ) (B A : Matrix m m ℂ)
    (hB : ∀ z w, B z w = if z = σ w then ε w else 0) (z z' : m) :
    (B * A * Bᴴ) z z' = ε (σ z) * A (σ z) (σ z') * star (ε (σ z')) := by
  simp only [Matrix.mul_apply, conjTranspose_apply, hB]
  rw [Finset.sum_eq_single (σ z')]
  · rw [Finset.sum_eq_single (σ z)]
    · simp [hσ z, hσ z']
    · intro y _ hy; rw [if_neg (fun e => hy (by rw [e, hσ y])), zero_mul]
    · simp
  · intro w _ hw; rw [if_neg (fun e => hw (by rw [e, hσ w])), star_zero, mul_zero]
  · simp

lemma lift_mul_mem (f : k → m) (hf : Function.Injective f) (M : Matrix k k ℂ)
    {l : Type*} (A : Matrix m l ℂ) (s : k) (j : l) :
    (lift f M * A) (f s) j = ∑ t, M s t * A (f t) j := by
  unfold lift
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.add_apply,
    col_mul_mem f hf, Matrix.mul_apply]
  simp [colT_mul, Matrix.sub_apply, Matrix.one_apply, sub_mul, Finset.sum_sub_distrib]

lemma lift_mul_not (f : k → m) (M : Matrix k k ℂ) {l : Type*} (A : Matrix m l ℂ) (i : m)
    (hi : ∀ s, i ≠ f s) (j : l) : (lift f M * A) i j = A i j := by
  unfold lift
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.add_apply,
    col_mul_not f _ i hi, add_zero]

lemma lift_apply (f : k → m) (M : Matrix k k ℂ) (i j : m) :
    lift f M i j = (1 : Matrix m m ℂ) i j
      + ∑ s, ∑ t, (if i = f s then (M - 1) s t * (if j = f t then 1 else 0) else 0) := by
  unfold lift
  rw [Matrix.add_apply, Matrix.mul_assoc, Matrix.mul_apply]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.mul_apply]
  simp only [col, transpose_apply]
  split_ifs <;> simp

lemma lift_J (p q : m) (hpq : p ≠ q) (i j : m) :
    lift ![p, q] !![(0 : ℂ), -1; 1, 0] i j
      = if i = Equiv.swap p q j then (if j = q then -1 else 1) else 0 := by
  rw [lift_apply]
  simp only [Fin.sum_univ_two]
  by_cases hjp : j = p
  · subst hjp
    rw [Equiv.swap_apply_left]
    by_cases hiq : i = q
    · subst hiq; simp [Matrix.one_apply, hpq, hpq.symm]
    · by_cases hij : i = j
      · subst hij; simp [Matrix.one_apply, hpq]
      · simp [Matrix.one_apply, hiq, hij, hpq]
  · by_cases hjq : j = q
    · subst hjq
      rw [Equiv.swap_apply_right]
      by_cases hip : i = p
      · subst hip; simp [Matrix.one_apply, hpq, hjp]
      · by_cases hij : i = j
        · subst hij; simp [Matrix.one_apply, hpq.symm]
        · simp [Matrix.one_apply, hip, hij]
    · rw [Equiv.swap_apply_of_ne_of_ne hjp hjq]
      by_cases hij : i = j
      · subst hij; simp [Matrix.one_apply, hjp, hjq]
      · simp [Matrix.one_apply, hij, hjp, hjq]

end Lift

section Fam

open ComplexConjugate

def Dm (γ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![γ, 0; 0, conj γ]

def Rm (ζ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(ζ.re : ℂ), -(ζ.im : ℂ); (ζ.im : ℂ), (ζ.re : ℂ)]

lemma Dm_mul (γ γ' : ℂ) : Dm γ * Dm γ' = Dm (γ * γ') := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Dm, Matrix.mul_apply, Fin.sum_univ_two]

lemma Rm_mul (ζ ζ' : ℂ) : Rm ζ * Rm ζ' = Rm (ζ * ζ') := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Rm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma Dm_one : Dm 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Dm]

lemma Rm_one : Rm 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Rm]

lemma Dm_star (γ : ℂ) : (Dm γ)ᴴ = Dm (conj γ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Dm, conjTranspose_apply]

lemma Rm_star (ζ : ℂ) : (Rm ζ)ᴴ = Rm (conj ζ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Rm, conjTranspose_apply]

/-- The generating family of `SU(2)`: diagonal phases and real rotations. -/
def Fam : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {M | ∃ γ : ℂ, Complex.normSq γ = 1 ∧ (M = Dm γ ∨ M = Rm γ)}

lemma Dm_mem {γ : ℂ} (h : Complex.normSq γ = 1) : Dm γ ∈ Fam := ⟨γ, h, Or.inl rfl⟩
lemma Rm_mem {γ : ℂ} (h : Complex.normSq γ = 1) : Rm γ ∈ Fam := ⟨γ, h, Or.inr rfl⟩

lemma Fam_mul_star {M : Matrix (Fin 2) (Fin 2) ℂ} (h : M ∈ Fam) : M * Mᴴ = 1 := by
  obtain ⟨γ, hγ, rfl | rfl⟩ := h
  · rw [Dm_star, Dm_mul, Complex.mul_conj, hγ, Complex.ofReal_one, Dm_one]
  · rw [Rm_star, Rm_mul, Complex.mul_conj, hγ, Complex.ofReal_one, Rm_one]

lemma Fam_star {M : Matrix (Fin 2) (Fin 2) ℂ} (h : M ∈ Fam) : Mᴴ ∈ Fam := by
  obtain ⟨γ, hγ, rfl | rfl⟩ := h
  · rw [Dm_star]; exact Dm_mem (by rw [Complex.normSq_conj, hγ])
  · rw [Rm_star]; exact Rm_mem (by rw [Complex.normSq_conj, hγ])

lemma Fam_star_mul {M : Matrix (Fin 2) (Fin 2) ℂ} (h : M ∈ Fam) : Mᴴ * M = 1 := by
  have := Fam_mul_star (Fam_star h)
  rwa [conjTranspose_conjTranspose] at this

lemma Fam_det {M : Matrix (Fin 2) (Fin 2) ℂ} (h : M ∈ Fam) : M.det = 1 := by
  obtain ⟨γ, hγ, rfl | rfl⟩ := h
  · rw [det_fin_two]
    simp [Dm, Complex.mul_conj, hγ]
  · rw [det_fin_two]
    have : (γ.re : ℂ) * γ.re + γ.im * γ.im = 1 := by
      rw [Complex.normSq_apply] at hγ
      exact_mod_cast hγ
    simp [Rm]
    linear_combination this

lemma Fam_SU {M : Matrix (Fin 2) (Fin 2) ℂ} (h : M ∈ Fam) :
    M ∈ specialUnitaryGroup (Fin 2) ℂ := by
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff, star_eq_conjTranspose]
  exact ⟨Fam_mul_star h, Fam_det h⟩

lemma unit_sqrt (w : ℂ) (hw : Complex.normSq w = 1) :
    ∃ z : ℂ, z ^ 2 = w ∧ Complex.normSq z = 1 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq w (n := 2) (by norm_num)
  refine ⟨z, hz, ?_⟩
  have h1 : Complex.normSq z ^ 2 = 1 := by rw [← map_pow, hz, hw]
  have h2 := Complex.normSq_nonneg z
  nlinarith [sq_nonneg (Complex.normSq z - 1)]

lemma Fam_comm {M : Matrix (Fin 2) (Fin 2) ℂ} (h : M ∈ Fam) :
    ∃ M1 ∈ Fam, ∃ M2 ∈ Fam, M = M1 * M2 * M1ᴴ * M2ᴴ := by
  have hI : Complex.normSq Complex.I = 1 := Complex.normSq_I
  obtain ⟨γ, hγ, rfl | rfl⟩ := h
  · obtain ⟨z, rfl, hz⟩ := unit_sqrt γ hγ
    refine ⟨Dm z, Dm_mem hz, Rm Complex.I, Rm_mem hI, ?_⟩
    rw [Dm_star, Rm_star]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Dm, Rm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · obtain ⟨z, rfl, hz⟩ := unit_sqrt γ hγ
    refine ⟨Rm z, Rm_mem hz, Dm Complex.I, Dm_mem hI, ?_⟩
    rw [Dm_star, Rm_star]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Dm, Rm, Matrix.mul_apply, Fin.sum_univ_two, pow_two] <;> ring_nf <;>
      simp [Complex.I_sq] <;> ring

lemma Fam_swap {M : Matrix (Fin 2) (Fin 2) ℂ} (h : M ∈ Fam) :
    M.submatrix (Equiv.swap 0 1) (Equiv.swap 0 1) ∈ Fam := by
  obtain ⟨γ, hγ, rfl | rfl⟩ := h
  · refine ⟨conj γ, by rw [Complex.normSq_conj, hγ], Or.inl ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [Dm]
  · refine ⟨conj γ, by rw [Complex.normSq_conj, hγ], Or.inr ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [Rm]

def Sg : Matrix (Fin 2) (Fin 2) ℂ := !![-1, 0; 0, 1]

lemma Fam_sign {M : Matrix (Fin 2) (Fin 2) ℂ} (h : M ∈ Fam) : Sg * M * Sg ∈ Fam := by
  obtain ⟨γ, hγ, rfl | rfl⟩ := h
  · refine ⟨γ, hγ, Or.inl ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Dm, Sg, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨conj γ, by rw [Complex.normSq_conj, hγ], Or.inr ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Rm, Sg, Matrix.mul_apply, Fin.sum_univ_two]

end Fam

section Gen

open ComplexConjugate

variable {m : Type*} [Fintype m] [DecidableEq m] (H : Submonoid (Matrix m m ℂ))

/-- All generating two-level gates on the basis states `y, y'` lie in `H`. -/
def Rel (y y' : m) : Prop := y ≠ y' ∧ ∀ M ∈ Fam, lift ![y, y'] M ∈ H

lemma inj2 {y y' : m} (h : y ≠ y') : Function.Injective ![y, y'] := by
  intro s t e
  fin_cases s <;> fin_cases t <;> first | rfl | (exfalso; first | exact h e | exact h e.symm)

lemma lift_swap2 (y y' : m) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    lift ![y', y] M = lift ![y, y'] (M.submatrix (Equiv.swap 0 1) (Equiv.swap 0 1)) := by
  ext i j
  rw [lift_apply, lift_apply]
  simp [Fin.sum_univ_two, Matrix.one_apply]
  ring_nf

lemma Rel.symm {y y' : m} (h : Rel H y y') : Rel H y' y :=
  ⟨h.1.symm, fun M hM => by rw [lift_swap2]; exact h.2 _ (Fam_swap hM)⟩

lemma Sg_mul : Sg * Sg = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Sg, Matrix.mul_apply, Fin.sum_univ_two]

lemma Sg_star : Sgᴴ = Sg := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Sg, conjTranspose_apply]

lemma key_col (y1 y2 y3 : m) (h12 : y1 ≠ y2) (h13 : y1 ≠ y3) (h23 : y2 ≠ y3) :
    lift ![y1, y2] (Rm Complex.I) * col ![y2, y3] = col ![y1, y3] * Sg := by
  ext z t
  by_cases h1 : z = y1
  · subst h1
    have := lift_mul_mem ![z, y2] (inj2 h12) (Rm Complex.I) (col ![y2, y3]) 0 t
    simp [Fin.sum_univ_two] at this
    rw [this]
    fin_cases t <;>
      simp [Rm, col, Sg, Matrix.mul_apply, Fin.sum_univ_two, h12, h13, h23, h23.symm]
  · by_cases h2 : z = y2
    · subst h2
      have := lift_mul_mem ![y1, z] (inj2 h12) (Rm Complex.I) (col ![z, y3]) 1 t
      simp [Fin.sum_univ_two] at this
      rw [this]
      fin_cases t <;>
        simp [Rm, col, Sg, Matrix.mul_apply, Fin.sum_univ_two, h12, h13, h23, h1]
    · rw [lift_mul_not _ _ _ _ (Fin.forall_fin_two.2 ⟨h1, h2⟩)]
      fin_cases t <;>
        simp [col, Sg, Matrix.mul_apply, Fin.sum_univ_two, h1, h2]

variable (hH : ∀ U ∈ H, Uᴴ ∈ H)
include hH

lemma Rel.trans {y1 y2 y3 : m} (h12 : Rel H y1 y2) (h23 : Rel H y2 y3) (h13 : y1 ≠ y3) :
    Rel H y1 y3 := by
  refine ⟨h13, fun M hM => ?_⟩
  have hI := Rm_mem Complex.normSq_I
  have hP := h12.2 _ hI
  have hG := h23.2 _ (Fam_sign hM)
  have hmem := H.mul_mem (H.mul_mem hP hG) (hH _ hP)
  have hkey := key_col y1 y2 y3 h12.1 h13 h23.1
  have hPP := lift_unit ![y1, y2] (inj2 h12.1) _ (Fam_mul_star hI)
  obtain ⟨P, hPd⟩ : ∃ P, P = lift ![y1, y2] (Rm Complex.I) := ⟨_, rfl⟩
  rw [← hPd] at hmem hkey hPP
  have hkey' : (col ![y2, y3])ᵀ * Pᴴ = Sg * (col ![y1, y3])ᵀ := by
    have := congrArg conjTranspose hkey
    rw [conjTranspose_mul, conjTranspose_mul, col_conjTranspose, col_conjTranspose, Sg_star]
      at this
    exact this
  have hS : Sg * (Sg * M * Sg - 1) * Sg = M - 1 := by
    have : Sg * (Sg * M * Sg - 1) * Sg = (Sg * Sg) * M * (Sg * Sg) - Sg * Sg := by
      noncomm_ring
    rw [this, Sg_mul, Matrix.one_mul, Matrix.mul_one]
  have e : P * lift ![y2, y3] (Sg * M * Sg) * Pᴴ = lift ![y1, y3] M := by
    calc P * lift ![y2, y3] (Sg * M * Sg) * Pᴴ
        = P * Pᴴ + (P * col ![y2, y3]) * (Sg * M * Sg - 1) * ((col ![y2, y3])ᵀ * Pᴴ) := by
          unfold lift
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 + col ![y1, y3] * (Sg * (Sg * M * Sg - 1) * Sg) * (col ![y1, y3])ᵀ := by
          rw [hPP, hkey, hkey']
          simp only [Matrix.mul_assoc]
      _ = lift ![y1, y3] M := by rw [hS]; rfl
  rw [e] at hmem
  exact hmem

omit hH

def FixOut (S : Finset m) (A : Matrix m m ℂ) : Prop :=
  ∀ x y, (x ∉ S ∨ y ∉ S) → A x y = (1 : Matrix m m ℂ) x y

lemma FixOut.mul {S : Finset m} {A B : Matrix m m ℂ} (hA : FixOut S A) (hB : FixOut S B) :
    FixOut S (A * B) := by
  intro x y h
  rw [Matrix.mul_apply]
  rcases h with h | h
  · have : ∀ k, A x k * B k y = if x = k then B k y else 0 := fun k => by
      rw [hA x k (Or.inl h), Matrix.one_apply]; split_ifs <;> simp
    simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hB x y (Or.inl h)
  · have : ∀ k, A x k * B k y = if k = y then A x k else 0 := fun k => by
      rw [hB k y (Or.inr h), Matrix.one_apply]; split_ifs <;> simp
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hA x y (Or.inr h)

lemma lift_not_left {k : Type*} [Fintype k] [DecidableEq k] (f : k → m) (M : Matrix k k ℂ)
    (i j : m) (hi : ∀ s, i ≠ f s) : lift f M i j = (1 : Matrix m m ℂ) i j := by
  have := lift_mul_not f M (1 : Matrix m m ℂ) i hi j
  rwa [Matrix.mul_one] at this

lemma lift_not_right {k : Type*} [Fintype k] [DecidableEq k] (f : k → m) (M : Matrix k k ℂ)
    (i j : m) (hj : ∀ s, j ≠ f s) : lift f M i j = (1 : Matrix m m ℂ) i j := by
  have := lift_not_left f Mᴴ j i hj
  rw [← lift_conjTranspose, conjTranspose_apply] at this
  have h2 := congrArg star this
  rw [star_star] at h2
  rw [h2, Matrix.one_apply, Matrix.one_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm, star_one]
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

def Good (S : Finset m) (g : Matrix m m ℂ) : Prop :=
  g ∈ H ∧ g ∈ specialUnitaryGroup m ℂ ∧ FixOut S g

lemma Good.mul {S : Finset m} {g h : Matrix m m ℂ} (hg : Good H S g) (hh : Good H S h) :
    Good H S (g * h) :=
  ⟨H.mul_mem hg.1 hh.1, mul_mem hg.2.1 hh.2.1, hg.2.2.mul hh.2.2⟩

lemma Good.one (S : Finset m) : Good H S 1 := ⟨H.one_mem, one_mem _, fun _ _ _ => rfl⟩

variable (hR : ∀ y y', y ≠ y' → Rel H y y')
include hR

lemma Good_lift {S : Finset m} {s t : m} (hs : s ∈ S) (ht : t ∈ S) (hst : s ≠ t)
    {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M ∈ Fam) : Good H S (lift ![s, t] M) := by
  refine ⟨(hR s t hst).2 M hM, lift_SU _ (inj2 hst) _ (Fam_SU hM), ?_⟩
  intro x y h
  rcases h with h | h
  · apply lift_not_left
    exact Fin.forall_fin_two.2
      ⟨fun e => h (by rw [e]; exact hs), fun e => h (by rw [e]; exact ht)⟩
  · apply lift_not_right
    exact Fin.forall_fin_two.2
      ⟨fun e => h (by rw [e]; exact hs), fun e => h (by rw [e]; exact ht)⟩

omit hR

lemma elim2 (a b : ℂ) :
    ∃ M1 ∈ Fam, ∃ M2 ∈ Fam, (M1 * M2) 1 0 * a + (M1 * M2) 1 1 * b = 0 := by
  by_cases h0 : a = 0 ∧ b = 0
  · refine ⟨Dm 1, Dm_mem (by simp), Dm 1, Dm_mem (by simp), ?_⟩
    rw [h0.1, h0.2]; simp
  have hr : 0 < ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    by_contra hneg
    apply h0
    have h1 : ‖a‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖a‖, sq_nonneg ‖b‖]
    have h2 : ‖b‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖a‖, sq_nonneg ‖b‖]
    exact ⟨by simpa using h1, by simpa using h2⟩
  obtain ⟨γ, hγ, hγe⟩ : ∃ γ : ℂ, Complex.normSq γ = 1 ∧ (‖b‖ : ℂ) * γ ^ 2 * a = ‖a‖ * b := by
    by_cases ha : a = 0
    · exact ⟨1, by simp, by simp [ha]⟩
    by_cases hb : b = 0
    · exact ⟨1, by simp, by simp [hb]⟩
    have hpa := norm_pos_iff.2 ha
    have hpb := norm_pos_iff.2 hb
    have hna : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hpa.ne'
    have hnb : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast hpb.ne'
    obtain ⟨γ, hγ2, hγ⟩ := unit_sqrt (conj a * b / (‖a‖ * ‖b‖)) (by
      rw [map_div₀, map_mul, map_mul, Complex.normSq_conj, Complex.normSq_ofReal,
        Complex.normSq_ofReal, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      field_simp)
    refine ⟨γ, hγ, ?_⟩
    rw [hγ2]
    have : conj a * a = (‖a‖ : ℂ) ^ 2 := Complex.conj_mul' a
    field_simp
    linear_combination this
  obtain ⟨r, hrd⟩ : ∃ r, r = Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hrd]; exact Real.sqrt_pos.2 hr
  have hr2 : r ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by rw [hrd]; exact Real.sq_sqrt hr.le
  refine ⟨Rm ⟨-‖a‖ / r, ‖b‖ / r⟩, Rm_mem ?_, Dm γ, Dm_mem hγ, ?_⟩
  · rw [Complex.normSq_mk]
    field_simp
    nlinarith
  · have hγ0 : γ ≠ 0 := fun e => by rw [e] at hγ; simp at hγ
    have hc : γ * conj γ = 1 := by rw [Complex.mul_conj, hγ]; simp
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    simp [Rm, Dm, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    apply mul_left_cancel₀ hγ0
    linear_combination hγe - (‖a‖ : ℂ) * b * hc

include hR

lemma col_reduce (S : Finset m) (s : m) (hs : s ∈ S) (U : Matrix m m ℂ) (T : Finset m) :
    T ⊆ S → s ∉ T → ∃ g, Good H S g ∧ ∀ t ∈ T, (g * U) t s = 0 := by
  induction T using Finset.induction_on with
  | empty => exact fun _ _ => ⟨1, Good.one H S, fun t ht => absurd ht (Finset.notMem_empty t)⟩
  | insert t T' ht ih =>
    intro hsub hsT
    obtain ⟨g, hg, hz⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
      (fun h => hsT (Finset.mem_insert_of_mem h))
    have hst : s ≠ t := fun e => hsT (e ▸ Finset.mem_insert_self t T')
    have htS : t ∈ S := hsub (Finset.mem_insert_self t T')
    obtain ⟨M1, h1, M2, h2, he⟩ := elim2 ((g * U) s s) ((g * U) t s)
    refine ⟨lift ![s, t] M1 * lift ![s, t] M2 * g,
      Good.mul H (Good.mul H (Good_lift H hR hs htS hst h1) (Good_lift H hR hs htS hst h2)) hg, ?_⟩
    intro t' ht'
    rw [Matrix.mul_assoc, lift_mul _ (inj2 hst)]
    rcases Finset.mem_insert.1 ht' with e | ht'
    · subst e
      have := lift_mul_mem ![s, t'] (inj2 hst) (M1 * M2) (g * U) 1 s
      simp [Fin.sum_univ_two] at this
      rw [this]; exact he
    · have hne : ∀ i, t' ≠ ![s, t] i := Fin.forall_fin_two.2
        ⟨fun e => hsT (Finset.mem_insert_of_mem (by have h := ht'; rw [e] at h; exact h)),
          fun e => ht (by have h := ht'; rw [e] at h; exact h)⟩
      rw [lift_mul_not _ _ _ _ hne]; exact hz t' ht'

include hH

theorem gen : ∀ S : Finset m, ∀ U ∈ specialUnitaryGroup m ℂ, FixOut S U → U ∈ H := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro U _ hF
    have : U = 1 := by ext x y; exact hF x y (Or.inl (Finset.notMem_empty x))
    rw [this]; exact H.one_mem
  | insert s S' hs ih =>
    intro U hU hF
    obtain ⟨g, hg, hz⟩ := col_reduce H hR (insert s S') s (Finset.mem_insert_self s S') U S'
      (Finset.subset_insert s S') hs
    obtain ⟨V, hVd⟩ : ∃ V, V = g * U := ⟨_, rfl⟩
    have hVSU : V ∈ specialUnitaryGroup m ℂ := by rw [hVd]; exact mul_mem hg.2.1 hU
    have hVF : FixOut (insert s S') V := by rw [hVd]; exact hg.2.2.mul hF
    have hcol : ∀ t, t ≠ s → V t s = 0 := by
      intro t hts
      by_cases htS : t ∈ S'
      · rw [hVd]; exact hz t htS
      · rw [hVF t s (Or.inl (by simp [hts, htS])), Matrix.one_apply, if_neg hts]
    obtain ⟨lam, hlam⟩ : ∃ lam, lam = V s s := ⟨_, rfl⟩
    have hnorm : conj lam * lam = 1 := by
      have hu := mem_unitaryGroup_iff'.1 (mem_specialUnitaryGroup_iff.1 hVSU).1
      have h1 := congrFun (congrFun hu s) s
      rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single s] at h1
      · rw [hlam]; exact h1
      · intro t _ hts; rw [hcol t hts, mul_zero]
      · intro h; exact absurd (Finset.mem_univ s) h
    obtain ⟨g2, hg2, h2s, h2c⟩ : ∃ g2, Good H (insert s S') g2 ∧ (g2 * V) s s = 1 ∧
        ∀ t, t ≠ s → (g2 * V) t s = 0 := by
      by_cases hne : S'.Nonempty
      · obtain ⟨t0, ht0⟩ := hne
        have hst0 : s ≠ t0 := fun e => hs (e ▸ ht0)
        have hlam1 : Complex.normSq (conj lam) = 1 := by
          rw [Complex.normSq_conj]
          have := Complex.normSq_eq_conj_mul_self (z := lam)
          rw [hnorm] at this
          exact_mod_cast this
        refine ⟨lift ![s, t0] (Dm (conj lam)), Good_lift H hR (Finset.mem_insert_self s S')
          (Finset.mem_insert_of_mem ht0) hst0 (Dm_mem hlam1), ?_, ?_⟩
        · have := lift_mul_mem ![s, t0] (inj2 hst0) (Dm (conj lam)) V 0 s
          simp [Fin.sum_univ_two] at this
          rw [this, hcol t0 (Ne.symm hst0), ← hlam]
          simpa [Dm] using hnorm
        · intro t hts
          by_cases ht : t = t0
          · subst ht
            have := lift_mul_mem ![s, t] (inj2 hst0) (Dm (conj lam)) V 1 s
            simp [Fin.sum_univ_two] at this
            rw [this, hcol t hts]
            simp [Dm]
          · rw [lift_mul_not _ _ _ _ (Fin.forall_fin_two.2 ⟨hts, ht⟩)]; exact hcol t hts
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        subst hne
        refine ⟨1, Good.one H _, ?_, fun t hts => by rw [Matrix.one_mul]; exact hcol t hts⟩
        rw [Matrix.one_mul, ← hlam]
        have hV : V = Matrix.diagonal (fun x => if x = s then lam else 1) := by
          ext x y
          rw [Matrix.diagonal_apply]
          by_cases hx : x = s
          · subst hx
            by_cases hy : x = y
            · subst hy; simp [hlam]
            · rw [if_neg hy, hVF x y (Or.inr (by simpa using Ne.symm hy)),
                Matrix.one_apply_ne hy]
          · rw [hVF x y (Or.inl (by simpa using hx)), Matrix.one_apply, if_neg hx]
        have hdet := (mem_specialUnitaryGroup_iff.1 hVSU).2
        rw [hV, Matrix.det_diagonal, Finset.prod_ite_eq'] at hdet
        simpa using hdet
    obtain ⟨W, hWd⟩ : ∃ W, W = g2 * V := ⟨_, rfl⟩
    rw [← hWd] at h2s h2c
    have hWSU : W ∈ specialUnitaryGroup m ℂ := by rw [hWd]; exact mul_mem hg2.2.1 hVSU
    have hWF : FixOut (insert s S') W := by rw [hWd]; exact hg2.2.2.mul hVF
    have hrow : ∀ y, y ≠ s → W s y = 0 := by
      have hu := mem_unitaryGroup_iff.1 (mem_specialUnitaryGroup_iff.1 hWSU).1
      have h1 := congrFun (congrFun hu s) s
      rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
      have h2 : ∑ y, Complex.normSq (W s y) = 1 := by
        have : ∀ y, W s y * star W y s = ((Complex.normSq (W s y) : ℝ) : ℂ) := fun y => by
          rw [Matrix.star_apply]; exact Complex.mul_conj _
        simp only [this] at h1
        exact_mod_cast h1
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s), h2s, Complex.normSq_one] at h2
      have h3 : ∑ x ∈ Finset.univ.erase s, Complex.normSq (W s x) = 0 := by linarith
      intro y hy
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)).1 h3 y
        (Finset.mem_erase.2 ⟨hy, Finset.mem_univ y⟩)
      exact Complex.normSq_eq_zero.1 this
    have hWF' : FixOut S' W := by
      intro x y h
      by_cases hx : x = s
      · subst hx
        by_cases hy : y = x
        · subst hy; rw [h2s, Matrix.one_apply_eq]
        · rw [hrow y hy, Matrix.one_apply_ne (Ne.symm hy)]
      · by_cases hy : y = s
        · subst hy; rw [h2c x hx, Matrix.one_apply_ne hx]
        · rcases h with h | h
          · exact hWF x y (Or.inl (by simp [hx, h]))
          · exact hWF x y (Or.inr (by simp [hy, h]))
    have hWH := ih W hWSU hWF'
    have e : U = gᴴ * (g2ᴴ * W) := by
      have ug := mem_unitaryGroup_iff'.1 (mem_specialUnitaryGroup_iff.1 hg.2.1).1
      have ug2 := mem_unitaryGroup_iff'.1 (mem_specialUnitaryGroup_iff.1 hg2.2.1).1
      rw [star_eq_conjTranspose] at ug ug2
      rw [hWd, hVd, ← Matrix.mul_assoc g2ᴴ, ug2, Matrix.one_mul, ← Matrix.mul_assoc, ug,
        Matrix.one_mul]
    rw [e]; exact H.mul_mem (hH _ hg.1) (H.mul_mem (hH _ hg2.1) hWH)

end Gen

section CG

variable {n : ℕ} (d : Fin n → ℕ)

abbrev St := (i : Fin n) → Fin (d i)

/-- `z` and `w` agree away from subsystem `a`. -/
def Agr (a : Fin n) (z w : St d) : Prop := ∀ k, k ≠ a → z k = w k

instance (a : Fin n) (z w : St d) : Decidable (Agr d a z w) := by unfold Agr; infer_instance

variable {d}

lemma Agr.refl (a : Fin n) (z : St d) : Agr d a z z := fun _ _ => rfl

lemma Agr.symm {a : Fin n} {z w : St d} (h : Agr d a z w) : Agr d a w z :=
  fun k hk => (h k hk).symm

lemma Agr.trans {a : Fin n} {z w v : St d} (h : Agr d a z w) (h' : Agr d a w v) :
    Agr d a z v := fun k hk => (h k hk).trans (h' k hk)

lemma Agr.eq {a : Fin n} {z w : St d} (h : Agr d a z w) (ha : z a = w a) : z = w := by
  funext k
  by_cases hk : k = a
  · subst hk; exact ha
  · exact h k hk

lemma upd_iff (a : Fin n) (x z : St d) (u : Fin (d a)) :
    z = Function.update x a u ↔ z a = u ∧ Agr d a z x := Function.eq_update_iff

variable (d)

/-- Block-diagonal gate on subsystem `a`: on each setting of the other subsystems, `F z`. -/
def CG (a : Fin n) (F : St d → Matrix (Fin (d a)) (Fin (d a)) ℂ) : Matrix (St d) (St d) ℂ :=
  fun z w => if Agr d a z w then F z (z a) (w a) else 0

def Indep {α : Type*} (a : Fin n) (F : St d → α) : Prop := ∀ z w, Agr d a z w → F z = F w

lemma sum_agr (a : Fin n) (z : St d) (g : St d → ℂ) :
    ∑ w, (if Agr d a z w then g w else 0) = ∑ t, g (Function.update z a t) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun t _ => Function.update z a t)
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro k hk
    rw [Function.update_of_ne hk]
  · intro t _ t' _ h
    have := congrFun h a
    simpa using this
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    refine ⟨w a, Finset.mem_univ _, ?_⟩
    symm
    rw [upd_iff]
    exact ⟨rfl, hw.symm⟩
  · intro t _; rfl

lemma CG_mul (a : Fin n) (F F' : St d → Matrix (Fin (d a)) (Fin (d a)) ℂ)
    (hF' : Indep d a F') : CG d a F * CG d a F' = CG d a (fun z => F z * F' z) := by
  ext z z'
  rw [Matrix.mul_apply]
  simp only [CG]
  by_cases h : Agr d a z z'
  · rw [if_pos h, Matrix.mul_apply]
    have : ∀ w, (if Agr d a z w then F z (z a) (w a) else 0)
          * (if Agr d a w z' then F' w (w a) (z' a) else 0)
        = if Agr d a z w then F z (z a) (w a) * F' z (w a) (z' a) else 0 := by
      intro w
      by_cases hw : Agr d a z w
      · rw [if_pos hw, if_pos hw, if_pos (hw.symm.trans h), hF' z w hw]
      · rw [if_neg hw, if_neg hw, zero_mul]
    simp only [this]
    rw [sum_agr d a z (fun w => F z (z a) (w a) * F' z (w a) (z' a))]
    simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro w _
    by_cases hw : Agr d a z w
    · rw [if_neg (fun h' => h (hw.trans h')), mul_zero]
    · rw [if_neg hw, zero_mul]

lemma CG_star (a : Fin n) (F : St d → Matrix (Fin (d a)) (Fin (d a)) ℂ)
    (hF : Indep d a F) : (CG d a F)ᴴ = CG d a (fun z => (F z)ᴴ) := by
  ext z w
  simp only [conjTranspose_apply, CG]
  by_cases h : Agr d a z w
  · rw [if_pos h, if_pos h.symm, hF w z h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm), star_zero]

lemma CG_one (a : Fin n) : CG d a (fun _ => 1) = 1 := by
  ext z w
  simp only [CG, Matrix.one_apply]
  by_cases h : Agr d a z w
  · rw [if_pos h]
    by_cases h2 : z a = w a
    · rw [if_pos h2, if_pos (h.eq h2)]
    · rw [if_neg h2, if_neg (fun e => h2 (by rw [e]))]
  · rw [if_neg h, if_neg (fun e => h (by rw [e]; exact Agr.refl _ _))]

open Classical in
/-- `W` where `p` holds, the identity elsewhere. -/
noncomputable def ctl {α : Type*} [One α] (p : St d → Prop) (W : α) : St d → α :=
  fun z => if p z then W else 1

lemma Indep_ctl {α : Type*} [One α] (a : Fin n) (p : St d → Prop) (hp : Indep d a p) (W : α) :
    Indep d a (ctl d p W) := by
  intro z w h
  have e := hp z w h
  by_cases hz : p z
  · have hw : p w := e ▸ hz
    simp [ctl, hz, hw]
  · have hw : ¬ p w := e ▸ hz
    simp [ctl, hz, hw]

lemma CG_lift_full {k : Type*} [Fintype k] [DecidableEq k] (a : Fin n) (x : St d)
    (f : k → Fin (d a)) (M : Matrix k k ℂ) :
    CG d a (ctl d (fun z => Agr d a z x) (lift f M))
      = lift (fun s => Function.update x a (f s)) M := by
  ext z w
  rw [lift_apply]
  simp only [CG, ctl, upd_iff]
  by_cases h : Agr d a z w
  · rw [if_pos h]
    have h1 : (1 : Matrix (St d) (St d) ℂ) z w = (1 : Matrix (Fin (d a)) (Fin (d a)) ℂ) (z a) (w a) := by
      simp only [Matrix.one_apply]
      by_cases h2 : z a = w a
      · rw [if_pos h2, if_pos (h.eq h2)]
      · rw [if_neg h2, if_neg (fun e => h2 (by rw [e]))]
    by_cases hx : Agr d a z x
    · have hw : Agr d a w x := h.symm.trans hx
      rw [if_pos hx, lift_apply, h1]
      simp [hx, hw]
    · rw [if_neg hx, h1]
      simp [hx]
  · rw [if_neg h]
    have h1 : (1 : Matrix (St d) (St d) ℂ) z w = 0 := by
      rw [Matrix.one_apply, if_neg (fun e => h (by rw [e]; exact Agr.refl _ _))]
    rw [h1, zero_add]
    symm
    apply Finset.sum_eq_zero; intro s _
    apply Finset.sum_eq_zero; intro t _
    by_cases hx : Agr d a z x
    · have hw : ¬ Agr d a w x := fun hw => h (hx.trans hw.symm)
      simp [hw]
    · simp [hx]

end CG

section Embed

variable {n : ℕ} (d : Fin n → ℕ)

lemma embedPair_star (a b : Fin n) (V : Matrix (Fin (d a) × Fin (d b)) (Fin (d a) × Fin (d b)) ℂ) :
    (embedPair d a b V)ᴴ = embedPair d a b Vᴴ := by
  ext x y
  simp only [conjTranspose_apply, embedPair]
  by_cases h : ∀ k, k ≠ a → k ≠ b → x k = y k
  · rw [if_pos h, if_pos (fun k h1 h2 => (h k h1 h2).symm)]
  · rw [if_neg h, if_neg (fun h' => h (fun k h1 h2 => (h' k h1 h2).symm)), star_zero]

lemma embedPair_swap (a b : Fin n) (V : Matrix (Fin (d a) × Fin (d b)) (Fin (d a) × Fin (d b)) ℂ) :
    embedPair d b a (V.submatrix Prod.swap Prod.swap) = embedPair d a b V := by
  ext x y
  simp only [embedPair, submatrix_apply, Prod.swap]
  by_cases h : ∀ k, k ≠ a → k ≠ b → x k = y k
  · rw [if_pos h, if_pos (fun k h1 h2 => h k h2 h1)]
  · rw [if_neg h, if_neg (fun h' => h (fun k h1 h2 => h' k h2 h1))]

lemma SU_submatrix {m m' : Type*} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (e : m ≃ m') (V : Matrix m' m' ℂ) (hV : V ∈ specialUnitaryGroup m' ℂ) :
    V.submatrix e e ∈ specialUnitaryGroup m ℂ := by
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff, star_eq_conjTranspose] at hV ⊢
  refine ⟨?_, by rw [det_submatrix_equiv_self]; exact hV.2⟩
  rw [conjTranspose_submatrix, submatrix_mul_equiv, hV.1, submatrix_one_equiv]

lemma embedPair_lift {k : Type*} [Fintype k] [DecidableEq k] (a b : Fin n) (hab : a ≠ b)
    (f : k → Fin (d a)) (β0 : Fin (d b)) (M : Matrix k k ℂ) :
    embedPair d a b (lift (fun s => (f s, β0)) M)
      = CG d a (ctl d (fun z => z b = β0) (lift f M)) := by
  ext z w
  simp only [embedPair, CG, ctl]
  by_cases h : ∀ k, k ≠ a → k ≠ b → z k = w k
  · rw [if_pos h, lift_apply]
    by_cases hb : z b = w b
    · have hA : Agr d a z w := by
        intro k hk
        by_cases hkb : k = b
        · subst hkb; exact hb
        · exact h k hk hkb
      rw [if_pos hA]
      by_cases h0 : z b = β0
      · have h0' : w b = β0 := hb ▸ h0
        rw [if_pos h0, lift_apply]
        simp [Matrix.one_apply, Prod.ext_iff, h0, h0']
      · have h0' : ¬ w b = β0 := hb ▸ h0
        rw [if_neg h0]
        simp [Matrix.one_apply, Prod.ext_iff, h0, h0', hb]
    · have hA : ¬ Agr d a z w := fun hA => hb (hA b hab.symm)
      rw [if_neg hA]
      by_cases h0 : z b = β0
      · have h0' : ¬ w b = β0 := fun e => hb (h0.trans e.symm)
        simp [Matrix.one_apply, Prod.ext_iff, h0', hb]
      · simp [Matrix.one_apply, Prod.ext_iff, h0, hb]
  · have hA : ¬ Agr d a z w := fun hA => h (fun k hk _ => hA k hk)
    rw [if_neg h, if_neg hA]

/-- The basis permutation induced on the global space by a map `π` on subsystems `b, c`. -/
def sg (b c : Fin n) (π : Fin (d b) × Fin (d c) → Fin (d b) × Fin (d c)) (w : St d) : St d :=
  Function.update (Function.update w b (π (w b, w c)).1) c (π (w b, w c)).2

variable {d}

lemma sg_b (b c : Fin n) (hbc : b ≠ c) (π : Fin (d b) × Fin (d c) → Fin (d b) × Fin (d c))
    (w : St d) : sg d b c π w b = (π (w b, w c)).1 := by
  simp [sg, Function.update_of_ne hbc]

lemma sg_c (b c : Fin n) (π : Fin (d b) × Fin (d c) → Fin (d b) × Fin (d c))
    (w : St d) : sg d b c π w c = (π (w b, w c)).2 := by
  simp [sg]

lemma sg_ne (b c : Fin n) (π : Fin (d b) × Fin (d c) → Fin (d b) × Fin (d c))
    (w : St d) (k : Fin n) (hb : k ≠ b) (hc : k ≠ c) : sg d b c π w k = w k := by
  simp [sg, Function.update_of_ne hb, Function.update_of_ne hc]

lemma sg_iff (b c : Fin n) (hbc : b ≠ c) (π : Fin (d b) × Fin (d c) → Fin (d b) × Fin (d c))
    (z w : St d) :
    z = sg d b c π w ↔ (∀ k, k ≠ b → k ≠ c → z k = w k) ∧ (z b, z c) = π (w b, w c) := by
  constructor
  · rintro rfl
    refine ⟨fun k hb hc => sg_ne b c π w k hb hc, ?_⟩
    rw [sg_b b c hbc, sg_c]
  · rintro ⟨h1, h2⟩
    funext k
    by_cases hc : k = c
    · subst hc; rw [sg_c, ← h2]
    · by_cases hb : k = b
      · subst hb; rw [sg_b _ _ hbc, ← h2]
      · rw [sg_ne b c π w k hb hc, h1 k hb hc]

lemma sg_invol (b c : Fin n) (hbc : b ≠ c) (π : Fin (d b) × Fin (d c) → Fin (d b) × Fin (d c))
    (hπ : Function.Involutive π) : Function.Involutive (sg d b c π) := by
  intro w
  symm
  rw [sg_iff b c hbc]
  refine ⟨fun k hb hc => (sg_ne b c π w k hb hc).symm, ?_⟩
  rw [sg_b b c hbc, sg_c, Prod.mk.eta, hπ]

lemma sg_Agr (a b c : Fin n) (hba : b ≠ a) (hca : c ≠ a) (hbc : b ≠ c)
    (π : Fin (d b) × Fin (d c) → Fin (d b) × Fin (d c)) (z w : St d) (h : Agr d a z w) :
    Agr d a (sg d b c π z) (sg d b c π w) := by
  intro k hk
  by_cases hc : k = c
  · subst hc; rw [sg_c, sg_c, h b hba, h k hk]
  · by_cases hb : k = b
    · subst hb; rw [sg_b _ _ hbc, sg_b _ _ hbc, h k hk, h c hca]
    · rw [sg_ne b c π z k hb hc, sg_ne b c π w k hb hc, h k hk]

lemma embedPair_sperm (b c : Fin n) (hbc : b ≠ c)
    (π : Fin (d b) × Fin (d c) → Fin (d b) × Fin (d c)) (ε : Fin (d b) × Fin (d c) → ℂ)
    (V : Matrix (Fin (d b) × Fin (d c)) (Fin (d b) × Fin (d c)) ℂ)
    (hV : ∀ i j, V i j = if i = π j then ε j else 0) (z w : St d) :
    embedPair d b c V z w = if z = sg d b c π w then ε (w b, w c) else 0 := by
  simp only [embedPair, hV, sg_iff b c hbc]
  by_cases h : ∀ k, k ≠ b → k ≠ c → z k = w k
  · rw [if_pos h]
    by_cases h2 : (z b, z c) = π (w b, w c)
    · rw [if_pos h2, if_pos ⟨h, h2⟩]
    · rw [if_neg h2, if_neg (fun e => h2 e.2)]
  · rw [if_neg h, if_neg (fun e => h e.1)]

end Embed

section Build

variable {n : ℕ} {d : Fin n → ℕ} (H : Submonoid (Matrix (St d) (St d) ℂ))

/-- Every special unitary on subsystems `a, b` lies in `H`. -/
def Edge (a b : Fin n) : Prop :=
  a ≠ b ∧ ∀ V ∈ specialUnitaryGroup (Fin (d a) × Fin (d b)) ℂ, embedPair d a b V ∈ H

lemma Edge.symm {a b : Fin n} (h : Edge H a b) : Edge H b a := by
  refine ⟨h.1.symm, fun V hV => ?_⟩
  have e : embedPair d b a V = embedPair d a b (V.submatrix Prod.swap Prod.swap) := by
    rw [← embedPair_swap d a b]
    rfl
  rw [e]
  exact h.2 _ (SU_submatrix (Equiv.prodComm _ _) V hV)

/-- All generating gates on the levels `f` of subsystem `a`, controlled on `p`, lie in `H`. -/
def Q (a : Fin n) (f : Fin 2 → Fin (d a)) (p : St d → Prop) : Prop :=
  ∀ M ∈ Fam, CG d a (ctl d p (lift f M)) ∈ H

lemma Indep.map {α β : Type*} {a : Fin n} {F : St d → α} (h : Indep d a F) (g : α → β) :
    Indep d a (fun z => g (F z)) := fun z w hzw => by
  show g (F z) = g (F w)
  rw [h z w hzw]

lemma Q_edge (a b : Fin n) (hE : Edge H a b) (f : Fin 2 → Fin (d a))
    (hf : Function.Injective f) (β0 : Fin (d b)) : Q H a f (fun z => z b = β0) := by
  intro M hM
  rw [← embedPair_lift d a b hE.1]
  exact hE.2 _ (lift_SU _ (fun s t h => hf (Prod.ext_iff.1 h).1) M (Fam_SU hM))

variable (hH : ∀ U ∈ H, Uᴴ ∈ H)
include hH

lemma Q_and (a : Fin n) (f : Fin 2 → Fin (d a)) (hf : Function.Injective f)
    (p1 p2 : St d → Prop) (hp1 : Indep d a p1) (hp2 : Indep d a p2)
    (h1 : Q H a f p1) (h2 : Q H a f p2) : Q H a f (fun z => p1 z ∧ p2 z) := by
  intro M hM
  obtain ⟨M1, hM1, M2, hM2, rfl⟩ := Fam_comm hM
  have i1 := Indep_ctl d a p1 hp1 (lift f M1)
  have i2 := Indep_ctl d a p2 hp2 (lift f M2)
  have hmem := H.mul_mem (H.mul_mem (H.mul_mem (h1 M1 hM1) (h2 M2 hM2)) (hH _ (h1 M1 hM1)))
    (hH _ (h2 M2 hM2))
  rw [CG_star d a _ i1, CG_star d a _ i2, CG_mul d a _ _ i2, CG_mul d a _ _ (i1.map _),
    CG_mul d a _ _ (i2.map _)] at hmem
  convert hmem using 2
  funext z
  have u1 : lift f M1 * lift f M1ᴴ = 1 := by rw [lift_mul f hf, Fam_mul_star hM1, lift_one]
  have u2 : lift f M2 * lift f M2ᴴ = 1 := by rw [lift_mul f hf, Fam_mul_star hM2, lift_one]
  by_cases c1 : p1 z <;> by_cases c2 : p2 z <;>
    simp [ctl, c1, c2, u1, u2, lift_conjTranspose, lift_mul f hf]

lemma Q_step (a b c : Fin n) (hba : b ≠ a) (hca : c ≠ a) (hbc : b ≠ c)
    (f : Fin 2 → Fin (d a)) (hf : Function.Injective f) (p : St d → Prop) (hp : Indep d a p)
    (β β' : Fin (d b)) (hβ : β' ≠ β) (γ : Fin (d c)) (hpb : ∀ z, p z → z b = β)
    (hE : Edge H b c) (hQ : Q H a f p) : Q H a f (fun z => p z ∧ z c = γ) := by
  intro M hM
  obtain ⟨M1, hM1, M2, hM2, rfl⟩ := Fam_comm hM
  obtain ⟨P, hP⟩ : ∃ P : Fin (d b) × Fin (d c), P = (β, γ) := ⟨_, rfl⟩
  obtain ⟨P', hP'⟩ : ∃ P : Fin (d b) × Fin (d c), P = (β', γ) := ⟨_, rfl⟩
  have hPP : P ≠ P' := fun e => hβ (by rw [hP, hP'] at e; exact (Prod.ext_iff.1 e).1.symm)
  obtain ⟨π, hπd⟩ : ∃ π : Fin (d b) × Fin (d c) → Fin (d b) × Fin (d c),
      π = Equiv.swap P P' := ⟨_, rfl⟩
  have hπ : Function.Involutive π := fun v => by rw [hπd]; exact Equiv.swap_apply_self P P' v
  obtain ⟨εp, hεp⟩ : ∃ εp : Fin (d b) × Fin (d c) → ℂ,
      εp = fun j => if j = P' then -1 else 1 := ⟨_, rfl⟩
  have hJ : (!![(0 : ℂ), -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
      ∈ specialUnitaryGroup (Fin 2) ℂ := by
    have : Rm Complex.I = !![(0 : ℂ), -1; 1, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Rm]
    rw [← this]; exact Fam_SU (Rm_mem Complex.normSq_I)
  have hinj : Function.Injective ![P, P'] := by
    intro s t h
    fin_cases s <;> fin_cases t <;> first | rfl | (exfalso; first | exact hPP h | exact hPP h.symm)
  obtain ⟨B, hBd⟩ : ∃ B, B = embedPair d b c (lift ![P, P'] !![(0 : ℂ), -1; 1, 0]) := ⟨_, rfl⟩
  have hB : B ∈ H := by rw [hBd]; exact hE.2 _ (lift_SU _ hinj _ hJ)
  obtain ⟨σ, hσd⟩ : ∃ σ, σ = sg d b c π := ⟨_, rfl⟩
  have hσ : Function.Involutive σ := by rw [hσd]; exact sg_invol b c hbc π hπ
  have hBf : ∀ z w, B z w = if z = σ w then εp (w b, w c) else 0 := by
    rw [hBd, hσd]
    refine embedPair_sperm b c hbc π εp _ (fun i j => ?_)
    rw [lift_J P P' hPP, hπd, hεp]
  have hσA : ∀ z w, Agr d a z w → Agr d a (σ z) (σ w) := by
    rw [hσd]; exact sg_Agr a b c hba hca hbc π
  have hσa : ∀ z, σ z a = z a := fun z => by
    rw [hσd]; exact sg_ne b c π z a hba.symm hca.symm
  obtain ⟨F, hFd⟩ : ∃ F, F = ctl d p (lift f M1ᴴ) := ⟨_, rfl⟩
  have iF : Indep d a F := by rw [hFd]; exact Indep_ctl d a p hp _
  have hconj : B * CG d a F * Bᴴ = CG d a (fun z => F (σ z)) := by
    ext z z'
    rw [sperm_conj σ hσ (fun w => εp (w b, w c)) B _ hBf]
    simp only [CG]
    by_cases h : Agr d a z z'
    · have h' := hσA z z' h
      rw [if_pos h, if_pos h', hσa, hσa, ← h' b hba, ← h' c hca]
      have e2 : εp (σ z b, σ z c) * star (εp (σ z b, σ z c)) = 1 := by
        rw [hεp]; simp only; split_ifs <;> simp
      rw [mul_right_comm, e2, one_mul]
    · have h' : ¬ Agr d a (σ z) (σ z') := fun h' => h (by
        have := hσA _ _ h'; rwa [hσ z, hσ z'] at this)
      rw [if_neg h, if_neg h', mul_zero, zero_mul]
  have hA : CG d a F ∈ H := by rw [hFd]; exact hQ _ (Fam_star hM1)
  have iF2 := Indep_ctl d a p hp (lift f M2)
  have hA2 := hQ _ hM2
  have hK := H.mul_mem (H.mul_mem (H.mul_mem hB hA) (hH _ hB)) (hH _ hA)
  rw [hconj, CG_star d a _ iF, CG_mul d a _ _ (iF.map _)] at hK
  have iK : Indep d a (fun z => F (σ z) * (F z)ᴴ) := fun z w h => by
    show F (σ z) * (F z)ᴴ = F (σ w) * (F w)ᴴ
    rw [iF _ _ (hσA z w h), iF z w h]
  have hT := H.mul_mem (H.mul_mem (H.mul_mem hK hA2) (hH _ hK)) (hH _ hA2)
  rw [CG_star d a _ iK, CG_star d a _ iF2, CG_mul d a _ _ iF2, CG_mul d a _ _ (iK.map _),
    CG_mul d a _ _ (iF2.map _)] at hT
  convert hT using 2
  funext z
  have s1 := Fam_star_mul hM1
  have s2 := Fam_mul_star hM2
  by_cases hz : p z
  · have hb := hpb z hz
    by_cases hc : z c = γ
    · have e : σ z b = β' := by
        rw [hσd, sg_b b c hbc, hb, hc, ← hP, hπd, Equiv.swap_apply_left, hP']
      have hσz : ¬ p (σ z) := fun h => hβ (e.symm.trans (hpb _ h))
      simp [hFd, ctl, hz, hc, hσz, lift_conjTranspose, lift_mul f hf]
    · have hσz : σ z = z := by
        symm
        rw [hσd, sg_iff b c hbc]
        refine ⟨fun _ _ _ => rfl, ?_⟩
        rw [hπd, Equiv.swap_apply_of_ne_of_ne]
        · rw [hP]; exact fun e => hc (Prod.ext_iff.1 e).2
        · rw [hP']; exact fun e => hc (Prod.ext_iff.1 e).2
      simp [hFd, ctl, hz, hc, hσz, lift_conjTranspose, lift_mul f hf, s1, s2, lift_one]
  · by_cases hs : p (σ z) <;>
      simp [hFd, ctl, hz, hs, lift_conjTranspose, lift_mul f hf, s1, s2, lift_one]

/-- `z` agrees with `x` on the subsystems in `C`. -/
def pC (x : St d) (C : Finset (Fin n)) : St d → Prop := fun z => ∀ k ∈ C, z k = x k

omit hH in
lemma Indep_pC (a : Fin n) (x : St d) (C : Finset (Fin n)) (ha : a ∉ C) :
    Indep d a (pC x C) := by
  intro z w h
  apply propext
  constructor
  · intro hz k hk; rw [← h k (fun e => ha (e ▸ hk))]; exact hz k hk
  · intro hw k hk; rw [h k (fun e => ha (e ▸ hk))]; exact hw k hk

omit hH in
lemma walk_ind {V : Type*} (Gr : SimpleGraph V) (S : V → Prop)
    (hS : ∀ u v, Gr.Adj u v → S v → S u) {u v : V} (w : Gr.Walk u v) : S v → S u := by
  induction w with
  | nil => exact id
  | cons h p ih => exact fun hv => hS _ _ h (ih hv)

omit hH in
lemma exists_ne_fin {N : ℕ} (hN : 2 ≤ N) (t : Fin N) : ∃ t' : Fin N, t' ≠ t := by
  by_cases h : t.val = 0
  · exact ⟨⟨1, by omega⟩, fun e => by have := congrArg Fin.val e; simp at this; omega⟩
  · exact ⟨⟨0, by omega⟩, fun e => by have := congrArg Fin.val e; simp at this; omega⟩

lemma reach (Gr : SimpleGraph (Fin n)) (hGr : ∀ b c, Gr.Adj b c → Edge H b c)
    (hd : ∀ i, 2 ≤ d i) (a : Fin n) (f : Fin 2 → Fin (d a)) (hf : Function.Injective f)
    (x : St d) (c : Fin n) (w : Gr.Walk c a) :
    c = a ∨ ∃ C : Finset (Fin n), c ∈ C ∧ a ∉ C ∧ Q H a f (pC x C) := by
  refine walk_ind Gr
    (fun c => c = a ∨ ∃ C : Finset (Fin n), c ∈ C ∧ a ∉ C ∧ Q H a f (pC x C)) ?_ w (Or.inl rfl)
  intro c c' hadj hc'
  by_cases hca : c = a
  · exact Or.inl hca
  right
  rcases hc' with h | ⟨C, hc'C, haC, hQ⟩
  · rw [h] at hadj
    refine ⟨{c}, Finset.mem_singleton_self c, by simpa using Ne.symm hca, ?_⟩
    have := Q_edge H a c (hGr c a hadj).symm f hf (x c)
    have e : pC x {c} = fun z => z c = x c := by
      funext z; simp [pC]
    rw [e]; exact this
  · by_cases hcC : c ∈ C
    · exact ⟨C, hcC, haC, hQ⟩
    · have hc'a : c' ≠ a := fun e => haC (e ▸ hc'C)
      have hc'c : c' ≠ c := fun e => hcC (e ▸ hc'C)
      obtain ⟨β', hβ'⟩ := exists_ne_fin (hd c') (x c')
      have := Q_step H hH a c' c hc'a hca hc'c f hf (pC x C) (Indep_pC a x C haC) (x c') β' hβ'
        (x c) (fun z hz => hz c' hc'C) (hGr c c' hadj).symm hQ
      refine ⟨insert c C, Finset.mem_insert_self c C, ?_, ?_⟩
      · rw [Finset.mem_insert]; exact fun h => h.elim (fun e => hca e.symm) haC
      · have e : pC x (insert c C) = fun z => pC x C z ∧ z c = x c := by
          funext z; apply propext
          simp only [pC, Finset.mem_insert]
          constructor
          · exact fun h => ⟨fun k hk => h k (Or.inr hk), h c (Or.inl rfl)⟩
          · rintro ⟨h1, h2⟩ k (rfl | hk)
            · exact h2
            · exact h1 k hk
        rw [e]; exact this

lemma all_ctl (Gr : SimpleGraph (Fin n)) (hc : Gr.Connected)
    (hGr : ∀ b c, Gr.Adj b c → Edge H b c) (hn : 2 ≤ n) (hd : ∀ i, 2 ≤ d i) (a : Fin n)
    (f : Fin 2 → Fin (d a)) (hf : Function.Injective f) (x : St d)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ∈ Fam) :
    lift (fun s => Function.update x a (f s)) M ∈ H := by
  have hreach : ∀ c, c ≠ a → ∃ C : Finset (Fin n), c ∈ C ∧ a ∉ C ∧ Q H a f (pC x C) := by
    intro c hca
    obtain ⟨w⟩ := hc.preconnected c a
    rcases reach H hH Gr hGr hd a f hf x c w with h | h
    · exact absurd h hca
    · exact h
  obtain ⟨c0, hc0⟩ : ∃ c0 : Fin n, c0 ≠ a := exists_ne_fin hn a
  have hall : ∀ S : Finset (Fin n),
      ∃ C : Finset (Fin n), S.erase a ⊆ C ∧ a ∉ C ∧ Q H a f (pC x C) := by
    intro S
    induction S using Finset.induction_on with
    | empty => obtain ⟨C, _, h2, h3⟩ := hreach c0 hc0; exact ⟨C, by simp, h2, h3⟩
    | insert s S' hs ih =>
      obtain ⟨C, h1, h2, h3⟩ := ih
      by_cases hsa : s = a
      · refine ⟨C, ?_, h2, h3⟩
        intro k hk
        rw [Finset.mem_erase, Finset.mem_insert] at hk
        rcases hk.2 with e | e
        · exact absurd (e.trans hsa) hk.1
        · exact h1 (Finset.mem_erase.2 ⟨hk.1, e⟩)
      · obtain ⟨C', h1', h2', h3'⟩ := hreach s hsa
        refine ⟨C ∪ C', ?_, ?_, ?_⟩
        · intro k hk
          rw [Finset.mem_erase, Finset.mem_insert] at hk
          rw [Finset.mem_union]
          rcases hk.2 with e | e
          · right; rw [e]; exact h1'
          · left; exact h1 (Finset.mem_erase.2 ⟨hk.1, e⟩)
        · rw [Finset.mem_union]; exact fun h => h.elim h2 h2'
        · have := Q_and H hH a f hf _ _ (Indep_pC a x C h2) (Indep_pC a x C' h2') h3 h3'
          have e : pC x (C ∪ C') = fun z => pC x C z ∧ pC x C' z := by
            funext z; apply propext
            simp only [pC, Finset.mem_union]
            constructor
            · exact fun h => ⟨fun k hk => h k (Or.inl hk), fun k hk => h k (Or.inr hk)⟩
            · exact fun h k hk => hk.elim (h.1 k) (h.2 k)
          rw [e]; exact this
  obtain ⟨C, h1, h2, h3⟩ := hall Finset.univ
  have e : pC x C = fun z => Agr d a z x := by
    funext z; apply propext
    constructor
    · intro h k hk; exact h k (h1 (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩))
    · intro h k hk; exact h k (fun e => h2 (e ▸ hk))
  rw [e] at h3
  have := h3 M hM
  rwa [CG_lift_full] at this

lemma hamming (base : ∀ (a : Fin n) (x : St d) (u v : Fin (d a)), u ≠ v →
      Rel H (Function.update x a u) (Function.update x a v)) :
    ∀ S : Finset (Fin n), ∀ y y' : St d, (∀ k, k ∉ S → y k = y' k) → y ≠ y' → Rel H y y' := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro y y' h hne
    exact absurd (funext fun k => h k (Finset.notMem_empty k)) hne
  | insert k S' hk ih =>
    intro y y' h hne
    by_cases hkk : y k = y' k
    · refine ih y y' (fun j hj => ?_) hne
      by_cases e : j = k
      · rw [e]; exact hkk
      · exact h j (by simp [e, hj])
    · have hb := base k y' (y k) (y' k) hkk
      rw [Function.update_eq_self] at hb
      by_cases hy : y = Function.update y' k (y k)
      · rw [hy] at hb ⊢
        simpa using hb
      · have := ih y (Function.update y' k (y k)) (fun j hj => by
            by_cases e : j = k
            · rw [e, Function.update_self]
            · rw [Function.update_of_ne e]; exact h j (by simp [e, hj])) hy
        exact Rel.trans H hH this hb hne

theorem build (Gr : SimpleGraph (Fin n)) (hc : Gr.Connected)
    (hGr : ∀ b c, Gr.Adj b c → Edge H b c) (hn : 2 ≤ n) (hd : ∀ i, 2 ≤ d i) :
    ∀ U ∈ specialUnitaryGroup (St d) ℂ, U ∈ H := by
  have base : ∀ (a : Fin n) (x : St d) (u v : Fin (d a)), u ≠ v →
      Rel H (Function.update x a u) (Function.update x a v) := by
    intro a x u v huv
    refine ⟨fun e => huv (by have := congrFun e a; simpa using this), fun M hM => ?_⟩
    have := all_ctl H hH Gr hc hGr hn hd a ![u, v] (inj2 huv) x M hM
    have e : (fun s => Function.update x a (![u, v] s))
        = ![Function.update x a u, Function.update x a v] := by
      funext s; fin_cases s <;> rfl
    rw [e] at this
    exact this
  have hR : ∀ y y' : St d, y ≠ y' → Rel H y y' := fun y y' hne =>
    hamming H hH base Finset.univ y y' (fun k hk => absurd (Finset.mem_univ k) hk) hne
  intro U hU
  exact gen H hH hR Finset.univ U hU
    (fun x y h => h.elim (fun h => absurd (Finset.mem_univ x) h)
      (fun h => absurd (Finset.mem_univ y) h))

end Build

lemma SU_star {m : Type*} [Fintype m] [DecidableEq m] (V : Matrix m m ℂ)
    (hV : V ∈ specialUnitaryGroup m ℂ) : Vᴴ ∈ specialUnitaryGroup m ℂ := by
  rw [mem_specialUnitaryGroup_iff] at hV ⊢
  refine ⟨?_, by rw [det_conjTranspose, hV.2, star_one]⟩
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_conjTranspose]
  have := mem_unitaryGroup_iff'.1 hV.1
  rwa [star_eq_conjTranspose] at this

end BaconThesis.Universality.Sol432

open BaconThesis.Universality BaconThesis.Universality.Sol432 Matrix in
theorem solution {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℕ) (hd : ∀ i, 2 ≤ d i)
    (G : Set (Matrix.unitaryGroup ((i : Fin n) → Fin (d i)) ℂ))
    (hG : (BaconThesis.Universality.compGraph d G).Connected) :
    (Matrix.specialUnitaryGroup ((i : Fin n) → Fin (d i)) ℂ : Set (Matrix _ _ ℂ)) ⊆
      BaconThesis.Universality.denseGen G := by
  let D : Submonoid (Matrix (St d) (St d) ℂ) :=
    ((Submonoid.closure G).map (Matrix.unitaryGroup (St d) ℂ).subtype).topologicalClosure
  have hD : (D : Set (Matrix (St d) (St d) ℂ)) = denseGen G := rfl
  let H : Submonoid (Matrix (St d) (St d) ℂ) :=
    { carrier := {U | U ∈ D ∧ Uᴴ ∈ D}
      mul_mem' := fun {A B} hA hB =>
        ⟨D.mul_mem hA.1 hB.1, by rw [conjTranspose_mul]; exact D.mul_mem hB.2 hA.2⟩
      one_mem' := ⟨D.one_mem, by rw [conjTranspose_one]; exact D.one_mem⟩ }
  have hH : ∀ U ∈ H, Uᴴ ∈ H := fun U hU =>
    ⟨hU.2, by rw [conjTranspose_conjTranspose]; exact hU.1⟩
  have hGr : ∀ b c, (compGraph d G).Adj b c → Edge H b c := by
    have key : ∀ b c, CompConnected d G b c → Edge H b c := by
      intro b c h
      refine ⟨h.1, fun V hV => ⟨?_, ?_⟩⟩
      · show embedPair d b c V ∈ (D : Set _)
        rw [hD]; exact h.2 V hV
      · show (embedPair d b c V)ᴴ ∈ (D : Set _)
        rw [hD, embedPair_star]; exact h.2 _ (SU_star V hV)
    intro b c hadj
    rw [compGraph, SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with h | h
    · exact key b c h
    · exact (key c b h).symm
  intro U hU
  have := build H hH (compGraph d G) hG hGr hn hd U hU
  rw [← hD]; exact this.1
