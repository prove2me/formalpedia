-- Prove2me | solution 1 for BaconThesis.WeakUniv.theorem_B_0_1
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T17:01:00.441593+00:00
-- url     : https://prove2.me/submissions/3f159390-eac1-4e18-a27b-958923d6a3ad

import Mathlib
import Definitions.Def_BaconThesis_WeakUniv_lieAlg
import Definitions.Def_BaconThesis_WeakUniv_dfsProj

attribute [local instance 100] LieRing.ofAssociativeRing

set_option linter.unusedSectionVars false

namespace BaconThesis.WeakUniv.SolB01

open BaconThesis.WeakUniv

section calculus

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The anti-Hermitian matrix `c |x⟩⟨y| - c̄ |y⟩⟨x|`. -/
def Mu (x y : ι) (c : ℂ) : Matrix ι ι ℂ := Matrix.single x y c - Matrix.single y x (star c)

lemma single_eq_smul (x y : ι) (v : ℂ) :
    Matrix.single x y v = v • Matrix.single x y (1 : ℂ) := by
  simp [Matrix.smul_single]

lemma single_apply' (x y : ι) (c : ℂ) (p q : ι) :
    Matrix.single x y c p q = if p = x ∧ q = y then c else 0 := by
  simp [Matrix.single_apply, eq_comm]

lemma Mu_swap (x y : ι) (c : ℂ) : Mu y x c = Mu x y (-star c) := by
  rw [Mu, Mu, single_eq_smul y x c, single_eq_smul x y (star c), single_eq_smul x y (-star c),
    single_eq_smul y x (star (-star c))]
  simp only [star_neg, star_star]
  module

lemma Mu_zero (x y : ι) : Mu x y 0 = 0 := by simp [Mu]

lemma lie_Mu_Mu {x y z : ι} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (a b : ℂ) :
    ⁅Mu x y a, Mu y z b⁆ = Mu x z (a * b) := by
  simp [Mu, Ring.lie_def, sub_mul, mul_sub, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, hxy, hyz, hxz, hxy.symm, hyz.symm, hxz.symm, mul_comm]

lemma single_mul_eq (x y : ι) (c : ℂ) (G : Matrix ι ι ℂ) :
    Matrix.single x y c * G = Matrix.of fun p q => if p = x then c * G y q else 0 := by
  ext p q
  by_cases h : p = x
  · subst h; simp [Matrix.single_mul_apply_same]
  · simp [Matrix.single_mul_apply_of_ne (h := h), h]

lemma mul_single_eq (x y : ι) (c : ℂ) (G : Matrix ι ι ℂ) :
    G * Matrix.single x y c = Matrix.of fun p q => if q = y then G p x * c else 0 := by
  ext p q
  by_cases h : q = y
  · subst h; simp [Matrix.mul_single_apply_same]
  · simp [Matrix.mul_single_apply_of_ne (hbj := h), h]

lemma diagonal_mul_single (f : ι → ℂ) (x y : ι) (c : ℂ) :
    Matrix.diagonal f * Matrix.single x y c = Matrix.single x y (f x * c) := by
  ext p q
  rw [Matrix.diagonal_mul, single_apply', single_apply']
  by_cases h : p = x ∧ q = y
  · obtain ⟨rfl, rfl⟩ := h; simp
  · simp [h]

lemma single_mul_diagonal (f : ι → ℂ) (x y : ι) (c : ℂ) :
    Matrix.single x y c * Matrix.diagonal f = Matrix.single x y (c * f y) := by
  ext p q
  rw [Matrix.mul_diagonal, single_apply', single_apply']
  by_cases h : p = x ∧ q = y
  · obtain ⟨rfl, rfl⟩ := h; simp
  · simp [h]

lemma lie_diag_Mu (f : ι → ℂ) (x y : ι) (c : ℂ) :
    ⁅Complex.I • Matrix.diagonal f, Mu x y c⁆ = (f x - f y) • Mu x y (Complex.I * c) := by
  simp only [Mu, Ring.lie_def, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.sub_mul,
    diagonal_mul_single, single_mul_diagonal, star_mul', Complex.star_def, Complex.conj_I]
  rw [single_eq_smul x y (f x * c), single_eq_smul y x (f y * _), single_eq_smul x y (c * f y),
    single_eq_smul y x (_ * f x), single_eq_smul x y (Complex.I * c),
    single_eq_smul y x (-Complex.I * _)]
  module

lemma lie_Mu_self {x y : ι} (hxy : x ≠ y) :
    ⁅Mu x y 1, Mu x y Complex.I⁆ =
      (2 * Complex.I) • (Matrix.single x x 1 - Matrix.single y y 1) := by
  simp [Mu, Ring.lie_def, sub_mul, mul_sub, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, hxy, hxy.symm]
  simp only [single_eq_smul _ _ Complex.I, single_eq_smul _ _ (-Complex.I)]
  module

/-- Bracket with an anti-Hermitian `G` whose only entries in the rows and columns of `u`, `v`
are `G u u' = g` and `G u' u = -ḡ`. -/
lemma lie_Mu_of_rows (G : Matrix ι ι ℂ) {u u' v : ι} (g : ℂ)
    (hv1 : ∀ y, G v y = 0) (hv2 : ∀ x, G x v = 0)
    (hu1 : ∀ y, G u y = if y = u' then g else 0)
    (hu2 : ∀ x, G x u = if x = u' then -star g else 0) (a : ℂ) :
    ⁅Mu v u a, G⁆ = Mu v u' (a * g) := by
  have F1 : Matrix.single v u a * G = Matrix.single v u' (a * g) := by
    ext p q
    rw [single_mul_eq, Matrix.of_apply, single_apply', hu1]
    by_cases h1 : p = v <;> by_cases h2 : q = u' <;> simp [h1, h2]
  have F2 : Matrix.single u v (star a) * G = 0 := by
    ext p q
    rw [single_mul_eq, Matrix.of_apply, hv1]
    simp
  have F3 : G * Matrix.single v u a = 0 := by
    ext p q
    rw [mul_single_eq, Matrix.of_apply, hv2]
    simp
  have F4 : G * Matrix.single u v (star a) = Matrix.single u' v (-star g * star a) := by
    ext p q
    rw [mul_single_eq, Matrix.of_apply, single_apply', hu2]
    by_cases h1 : p = u' <;> by_cases h2 : q = v <;> simp [h1, h2]
  rw [Mu, Mu, Ring.lie_def, Matrix.sub_mul, Matrix.mul_sub, F1, F2, F3, F4, star_mul',
    single_eq_smul u' v (-star g * star a), single_eq_smul u' v (star a * star g)]
  module

variable (L : LieSubalgebra ℝ (Matrix ι ι ℂ))

/-- Both `|x⟩⟨y| - |y⟩⟨x|` and `i(|x⟩⟨y| + |y⟩⟨x|)` (and their real combinations) lie in `L`. -/
def Rel (x y : ι) : Prop := x ≠ y ∧ ∀ c : ℂ, Mu x y c ∈ L

variable {L}

lemma Rel.symm {x y : ι} (h : Rel L x y) : Rel L y x :=
  ⟨h.1.symm, fun c => by rw [Mu_swap]; exact h.2 _⟩

lemma Rel.trans {x y z : ι} (hxy : Rel L x y) (hyz : Rel L y z) (hxz : x ≠ z) : Rel L x z :=
  ⟨hxz, fun c => by
    have := L.lie_mem (hxy.2 c) (hyz.2 1)
    rwa [lie_Mu_Mu hxy.1 hyz.1 hxz, mul_one] at this⟩

lemma Rel.trans' {x y z : ι} (hxy : x = y ∨ Rel L x y) (hyz : Rel L y z) (hxz : x ≠ z) :
    Rel L x z := by
  rcases hxy with rfl | h
  · exact hyz
  · exact h.trans hyz hxz

end calculus

section twoQubit

lemma Tz_apply (a b a' b' : Fin 2) :
    Tmat 0 0 1 0 0 (a, b) (a', b') = if a = 1 ∧ b = 0 ∧ a' = 1 ∧ b' = 0 then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;> simp [Tmat, finProdFinEquiv]

lemma T1_row (a b a' b' : Fin 2) (hab : a ≠ b) :
    Tmat 0 0 0 0 1 (a, b) (a', b') = if a' = b ∧ b' = a then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp_all [Tmat, finProdFinEquiv]

lemma T1_col (a b a' b' : Fin 2) (hab : a ≠ b) :
    Tmat 0 0 0 0 1 (a', b') (a, b) = if a' = b ∧ b' = a then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp_all [Tmat, finProdFinEquiv]

lemma T1_same (a a' b' : Fin 2) :
    Tmat 0 0 0 0 1 (a, a) (a', b') = 0 ∧ Tmat 0 0 0 0 1 (a', b') (a, a) = 0 := by
  fin_cases a <;> fin_cases a' <;> fin_cases b' <;> simp [Tmat, finProdFinEquiv]

lemma T1_eq : Tmat 0 0 0 0 1 = exchange - Tmat 1 0 0 0 0 - Tmat 0 0 0 1 0 := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp [Tmat, exchange, finProdFinEquiv]

end twoQubit

section qubits

variable {n : ℕ}

lemma embed_sub (k l : Fin n) (A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    embed n k l (A - B) = embed n k l A - embed n k l B := by
  ext x y
  simp only [embed, Matrix.sub_apply]
  split_ifs <;> simp

lemma eq_swap_iff {k l : Fin n} (hkl : k ≠ l) (u y : Fin n → Fin 2) :
    y = u ∘ Equiv.swap k l ↔ (∀ m, m ≠ k → m ≠ l → u m = y m) ∧ y k = u l ∧ y l = u k := by
  constructor
  · rintro rfl
    refine ⟨fun m hk hl => ?_, ?_, ?_⟩
    · simp [Equiv.swap_apply_of_ne_of_ne hk hl]
    · simp
    · simp
  · rintro ⟨h1, h2, h3⟩
    funext m
    by_cases hk : m = k
    · subst hk; simp [h2]
    · by_cases hl : m = l
      · subst hl; simp [h3]
      · simp [Equiv.swap_apply_of_ne_of_ne hk hl, h1 m hk hl]

/-- `Z̄` on qubits `k, l` is diagonal. -/
lemma embed_Tz {k l : Fin n} (hkl : k ≠ l) :
    embed n k l (Tmat 0 0 1 0 0) =
      Matrix.diagonal fun x : Fin n → Fin 2 => if x k = 1 ∧ x l = 0 then (1 : ℂ) else 0 := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp only [embed, Tz_apply, Matrix.diagonal_apply_eq, implies_true, if_true]
    split_ifs <;> first | rfl | tauto
  · rw [Matrix.diagonal_apply_ne _ hxy]
    simp only [embed]
    split_ifs with hoff
    · rw [Tz_apply, if_neg]
      rintro ⟨h1, h2, h3, h4⟩
      apply hxy
      funext m
      by_cases hk : m = k
      · subst hk; rw [h1, h3]
      · by_cases hl : m = l
        · subst hl; rw [h2, h4]
        · exact hoff m hk hl
    · rfl

/-- The row of `i T(0,0,0,0,1)` at a state whose bits `k, l` differ. -/
lemma G_row {k l : Fin n} (hkl : k ≠ l) (u : Fin n → Fin 2) (hu : u k ≠ u l)
    (y : Fin n → Fin 2) :
    (Complex.I • embed n k l (Tmat 0 0 0 0 1)) u y =
      if y = u ∘ Equiv.swap k l then Complex.I else 0 := by
  simp only [Matrix.smul_apply, embed, smul_eq_mul, eq_swap_iff hkl]
  split_ifs with h1 h2 h2
  · rw [T1_row _ _ _ _ hu, if_pos ⟨h2.2.1, h2.2.2⟩, mul_one]
  · rw [T1_row _ _ _ _ hu, if_neg (fun h => h2 ⟨h1, h.1, h.2⟩), mul_zero]
  · exact absurd h2.1 h1
  · rw [mul_zero]

lemma G_col {k l : Fin n} (hkl : k ≠ l) (u : Fin n → Fin 2) (hu : u k ≠ u l)
    (x : Fin n → Fin 2) :
    (Complex.I • embed n k l (Tmat 0 0 0 0 1)) x u =
      if x = u ∘ Equiv.swap k l then Complex.I else 0 := by
  simp only [Matrix.smul_apply, embed, smul_eq_mul, eq_swap_iff hkl]
  split_ifs with h1 h2 h2
  · rw [T1_col _ _ _ _ hu, if_pos ⟨h2.2.1, h2.2.2⟩, mul_one]
  · rw [T1_col _ _ _ _ hu, if_neg (fun h => h2 ⟨fun m hk hl => (h1 m hk hl).symm, h.1, h.2⟩),
      mul_zero]
  · exact absurd (fun m hk hl => (h2.1 m hk hl).symm) h1
  · rw [mul_zero]

lemma G_zero {k l : Fin n} (v : Fin n → Fin 2) (hv : v k = v l) (y : Fin n → Fin 2) :
    (Complex.I • embed n k l (Tmat 0 0 0 0 1)) v y = 0 ∧
      (Complex.I • embed n k l (Tmat 0 0 0 0 1)) y v = 0 := by
  simp only [Matrix.smul_apply, embed, smul_eq_mul, hv]
  constructor <;> split_ifs <;> simp [(T1_same _ _ _).1, (T1_same _ _ _).2]

/-- The generators on an adjacent pair, and `i T(0,0,0,0,1)`, lie in `L`. -/
lemma gen_mem (i : ℕ) (hi : i + 1 < n) :
    Complex.I • embed n ⟨i, by omega⟩ ⟨i + 1, hi⟩ (Tmat 0 0 1 0 0) ∈ lieAlg n ∧
      Complex.I • embed n ⟨i, by omega⟩ ⟨i + 1, hi⟩ (Tmat 0 0 0 0 1) ∈ lieAlg n := by
  have hmem : ∀ M ∈ gens n, Complex.I • M ∈ lieAlg n := fun M hM =>
    LieSubalgebra.subset_lieSpan ⟨M, hM, rfl⟩
  have hE := hmem _ ⟨i, hi, Or.inl rfl⟩
  have hP := hmem _ ⟨i, hi, Or.inr (Or.inl rfl)⟩
  have hQ := hmem _ ⟨i, hi, Or.inr (Or.inr (Or.inl rfl))⟩
  have hZ := hmem _ ⟨i, hi, Or.inr (Or.inr (Or.inr rfl))⟩
  refine ⟨hZ, ?_⟩
  rw [T1_eq, embed_sub, embed_sub, smul_sub, smul_sub]
  exact (lieAlg n).sub_mem ((lieAlg n).sub_mem hE hP) hQ

end qubits

section lift

variable {N : ℕ}

/-- The Hamming weight of a basis state. -/
def wt {n : ℕ} (x : Fin n → Fin 2) : ℕ := (Finset.univ.filter fun m => x m = 1).card

lemma wt_succ (u : Fin (N + 1) → Fin 2) :
    wt u = wt (Fin.init u) + if u (Fin.last N) = 1 then 1 else 0 := by
  rw [wt, wt, Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  rfl

lemma wt_swap {n : ℕ} (x : Fin n → Fin 2) (k l : Fin n) : wt (x ∘ Equiv.swap k l) = wt x := by
  simp only [wt, Finset.card_filter, Function.comp_apply]
  exact Equiv.sum_comp (Equiv.swap k l) fun m => if x m = 1 then 1 else 0

/-- `Y ⊗ I` on the last qubit. -/
def lift (Y : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) :
    Matrix (Fin (N + 1) → Fin 2) (Fin (N + 1) → Fin 2) ℂ :=
  fun x y => if x (Fin.last N) = y (Fin.last N) then Y (Fin.init x) (Fin.init y) else 0

lemma lift_add (Y Z : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) :
    lift (Y + Z) = lift Y + lift Z := by
  ext x y; simp only [lift, Matrix.add_apply]; split_ifs <;> simp

lemma lift_sub (Y Z : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) :
    lift (Y - Z) = lift Y - lift Z := by
  ext x y; simp only [lift, Matrix.sub_apply]; split_ifs <;> simp

lemma lift_smul (c : ℂ) (Y : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) :
    lift (c • Y) = c • lift Y := by
  ext x y; simp only [lift, Matrix.smul_apply]; split_ifs <;> simp

lemma lift_mul (Y Z : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) :
    lift (Y * Z) = lift Y * lift Z := by
  ext x y
  rw [Matrix.mul_apply, ← Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (N + 1) => Fin 2)
    (fun z => lift Y x z * lift Z z y), Fintype.sum_prod_type]
  simp only [lift, Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_last, Fin.init_snoc, Matrix.mul_apply]
  by_cases h : x (Fin.last N) = y (Fin.last N)
  · rw [if_pos h, Finset.sum_eq_single (y (Fin.last N))]
    · simp [h]
    · intro b _ hb
      simp [hb]
    · simp
  · rw [if_neg h]
    symm
    apply Finset.sum_eq_zero
    intro b _
    apply Finset.sum_eq_zero
    intro z _
    by_cases h1 : x (Fin.last N) = b
    · have : ¬ b = y (Fin.last N) := fun h2 => h (h1.trans h2)
      simp [this]
    · simp [h1]

lemma lift_embed (k l : Fin N) (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    lift (embed N k l M) = embed (N + 1) k.castSucc l.castSucc M := by
  ext x y
  have : (∀ m : Fin (N + 1), m ≠ k.castSucc → m ≠ l.castSucc → x m = y m) ↔
      x (Fin.last N) = y (Fin.last N) ∧
        ∀ m : Fin N, m ≠ k → m ≠ l → Fin.init x m = Fin.init y m := by
    rw [Fin.forall_fin_succ']
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2 (Fin.castSucc_ne_last k).symm (Fin.castSucc_ne_last l).symm,
        fun m hk hl => h1 m (fun h => hk (Fin.castSucc_injective _ h))
          (fun h => hl (Fin.castSucc_injective _ h))⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun m hk hl => h2 m (fun h => hk (by rw [h])) (fun h => hl (by rw [h])),
        fun _ _ => h1⟩
  by_cases h1 : x (Fin.last N) = y (Fin.last N)
  · by_cases h2 : ∀ m : Fin N, m ≠ k → m ≠ l → Fin.init x m = Fin.init y m
    · simp only [lift, embed, if_pos h1, if_pos h2, if_pos (this.mpr ⟨h1, h2⟩)]
      rfl
    · simp only [lift, embed, if_pos h1, if_neg h2, if_neg (fun h => h2 (this.mp h).2)]
  · simp only [lift, embed, if_neg h1, if_neg (fun h => h1 (this.mp h).1)]

/-- Elements of `L_N` act on the first `N` of `N + 1` qubits as elements of `L_{N+1}`. -/
lemma lift_mem {Y : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ} (hY : Y ∈ lieAlg N) :
    lift Y ∈ lieAlg (N + 1) := by
  let K : LieSubalgebra ℝ (Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) :=
    { carrier := {Y | lift Y ∈ lieAlg (N + 1)}
      add_mem' := fun {a b} ha hb => by
        change lift (a + b) ∈ lieAlg (N + 1)
        rw [lift_add]; exact (lieAlg (N + 1)).add_mem ha hb
      zero_mem' := by
        change lift 0 ∈ lieAlg (N + 1)
        have : lift (0 : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) = 0 := by
          ext x y; simp [lift]
        rw [this]; exact (lieAlg (N + 1)).zero_mem
      smul_mem' := fun r {a} ha => by
        change lift (r • a) ∈ lieAlg (N + 1)
        rw [← Complex.coe_smul, lift_smul, Complex.coe_smul]
        exact (lieAlg (N + 1)).smul_mem r ha
      lie_mem' := fun {a b} ha hb => by
        change lift ⁅a, b⁆ ∈ lieAlg (N + 1)
        rw [Ring.lie_def, lift_sub, lift_mul, lift_mul, ← Ring.lie_def]
        exact (lieAlg (N + 1)).lie_mem ha hb }
  have hle : lieAlg N ≤ K := by
    rw [lieAlg, LieSubalgebra.lieSpan_le]
    rintro _ ⟨G, ⟨i, hi, hG⟩, rfl⟩
    change lift (Complex.I • G) ∈ lieAlg (N + 1)
    rw [lift_smul]
    refine LieSubalgebra.subset_lieSpan ⟨lift G, ⟨i, by omega, ?_⟩, rfl⟩
    rcases hG with rfl | rfl | rfl | rfl
    · exact Or.inl (lift_embed _ _ _)
    · exact Or.inr (Or.inl (lift_embed _ _ _))
    · exact Or.inr (Or.inr (Or.inl (lift_embed _ _ _)))
    · exact Or.inr (Or.inr (Or.inr (lift_embed _ _ _)))
  exact hle hY

lemma eq_snoc_iff (u : Fin (N + 1) → Fin 2) (x : Fin N → Fin 2) (b : Fin 2) :
    u = Fin.snoc x b ↔ Fin.init u = x ∧ u (Fin.last N) = b := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨rfl, rfl⟩
    exact (Fin.snoc_init_self u).symm

lemma lift_single (x y : Fin N → Fin 2) (c : ℂ) :
    lift (Matrix.single x y c) =
      Matrix.single (Fin.snoc x 0 : Fin (N + 1) → Fin 2) (Fin.snoc y 0) c +
        Matrix.single (Fin.snoc x 1 : Fin (N + 1) → Fin 2) (Fin.snoc y 1) c := by
  ext u w
  simp only [lift, Matrix.add_apply, single_apply', eq_snoc_iff]
  generalize u (Fin.last N) = a
  generalize w (Fin.last N) = b
  by_cases h1 : Fin.init u = x <;> by_cases h2 : Fin.init w = y <;>
    fin_cases a <;> fin_cases b <;> simp [h1, h2]

lemma lift_Mu (x y : Fin N → Fin 2) (c : ℂ) :
    lift (Mu x y c) =
      Mu (Fin.snoc x 0 : Fin (N + 1) → Fin 2) (Fin.snoc y 0) c +
        Mu (Fin.snoc x 1 : Fin (N + 1) → Fin 2) (Fin.snoc y 1) c := by
  rw [Mu, lift_sub, lift_single, lift_single, Mu, Mu]
  abel

end lift

section induction

lemma fin2_ne {a b : Fin 2} (h : a ≠ b) : (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by
  fin_cases a <;> fin_cases b <;> simp_all

lemma fin2_trans {a b c : Fin 2} (h1 : a ≠ b) (h2 : b ≠ c) : a = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

variable {M : ℕ}

local notation "kk" => (Fin.castSucc (Fin.last M) : Fin (M + 2))
local notation "ll" => (Fin.last (M + 1) : Fin (M + 2))

lemma kk_ne_ll : kk ≠ ll := Fin.castSucc_ne_last _

/-- The diagonal generator `i Z̄` and `i T(0,0,0,0,1)` on the last two qubits. -/
lemma last_gens :
    Complex.I • Matrix.diagonal (fun z : Fin (M + 2) → Fin 2 =>
      if z kk = 1 ∧ z ll = 0 then (1 : ℂ) else 0) ∈ lieAlg (M + 2) ∧
    Complex.I • embed (M + 2) kk ll (Tmat 0 0 0 0 1) ∈ lieAlg (M + 2) := by
  have h := gen_mem (n := M + 2) M (by omega)
  refine ⟨?_, h.2⟩
  rw [← embed_Tz kk_ne_ll]
  exact h.1

/-- Splitting `Y ⊗ I` by the last qubit, when the edge changes the qubit before it. -/
lemma split_one {x y : Fin (M + 1) → Fin 2} (hrel : Rel (lieAlg (M + 1)) x y)
    (hx : x (Fin.last M) = 1) (hy : y (Fin.last M) = 0) (b : Fin 2) :
    Rel (lieAlg (M + 2)) (Fin.snoc x b : Fin (M + 2) → Fin 2) (Fin.snoc y b) := by
  have hne : ∀ b : Fin 2, (Fin.snoc x b : Fin (M + 2) → Fin 2) ≠ Fin.snoc y b := fun b h =>
    hrel.1 (by have := congrArg Fin.init h; simpa using this)
  have hW : ∀ c, Mu (Fin.snoc x 0 : Fin (M + 2) → Fin 2) (Fin.snoc y 0) c +
      Mu (Fin.snoc x 1 : Fin (M + 2) → Fin 2) (Fin.snoc y 1) c ∈ lieAlg (M + 2) := fun c => by
    rw [← lift_Mu]; exact lift_mem (hrel.2 c)
  have h0' : ∀ c, Mu (Fin.snoc x 0 : Fin (M + 2) → Fin 2) (Fin.snoc y 0) (Complex.I * c) ∈
      lieAlg (M + 2) := fun c => by
    have := (lieAlg (M + 2)).lie_mem last_gens.1 (hW c)
    rw [lie_add, lie_diag_Mu, lie_diag_Mu] at this
    simpa [Fin.snoc_castSucc, Fin.snoc_last, hx, hy] using this
  have h0 : ∀ c, Mu (Fin.snoc x 0 : Fin (M + 2) → Fin 2) (Fin.snoc y 0) c ∈ lieAlg (M + 2) :=
    fun c => by
      have := h0' (-Complex.I * c)
      rwa [show Complex.I * (-Complex.I * c) = c by
        rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]] at this
  have h1 : ∀ c, Mu (Fin.snoc x 1 : Fin (M + 2) → Fin 2) (Fin.snoc y 1) c ∈ lieAlg (M + 2) :=
    fun c => by
      have := (lieAlg (M + 2)).sub_mem (hW c) (h0 c)
      rwa [add_sub_cancel_left] at this
  obtain rfl | rfl : b = 0 ∨ b = 1 := by fin_cases b <;> simp
  · exact ⟨hne 0, h0⟩
  · exact ⟨hne 1, h1⟩

lemma split_ne {x y : Fin (M + 1) → Fin 2} (hrel : Rel (lieAlg (M + 1)) x y)
    (h : x (Fin.last M) ≠ y (Fin.last M)) (b : Fin 2) :
    Rel (lieAlg (M + 2)) (Fin.snoc x b : Fin (M + 2) → Fin 2) (Fin.snoc y b) := by
  rcases fin2_ne h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact split_one hrel hx hy b
  · exact (split_one hrel.symm hy hx b).symm

lemma snoc_ne {x y : Fin (M + 1) → Fin 2} (h : x ≠ y) (b : Fin 2) :
    (Fin.snoc x b : Fin (M + 2) → Fin 2) ≠ Fin.snoc y b := fun h' =>
  h (by have := congrArg Fin.init h'; simpa using this)

/-- All same-weight pairs with a common last bit, from the induction hypothesis. -/
lemma split_all
    (IH : ∀ x y : Fin (M + 1) → Fin 2, x ≠ y → wt x = wt y → Rel (lieAlg (M + 1)) x y)
    {x y : Fin (M + 1) → Fin 2} (hxy : x ≠ y) (hw : wt x = wt y) (b : Fin 2) :
    Rel (lieAlg (M + 2)) (Fin.snoc x b : Fin (M + 2) → Fin 2) (Fin.snoc y b) := by
  by_cases hl : x (Fin.last M) = y (Fin.last M)
  · obtain ⟨p, hp⟩ := Function.ne_iff.mp hxy
    have hcase : x p ≠ x (Fin.last M) ∨ y p ≠ y (Fin.last M) := by
      by_contra h
      push Not at h
      exact hp (h.1.trans (hl.trans h.2.symm))
    rcases hcase with hc | hc
    · set z := x ∘ Equiv.swap p (Fin.last M) with hz
      have hzl : z (Fin.last M) = x p := by simp [hz]
      have hzx : z ≠ x := fun h => hc (by rw [← hzl, h])
      have hzy : z ≠ y := fun h => hc (by rw [← hzl, h, hl])
      have hwz : wt z = wt x := wt_swap _ _ _
      exact (split_ne (IH x z hzx.symm hwz.symm) (by rw [hzl]; exact hc.symm) b).trans
        (split_ne (IH z y hzy (hwz.trans hw)) (by rw [hzl, ← hl]; exact hc) b) (snoc_ne hxy b)
    · set z := y ∘ Equiv.swap p (Fin.last M) with hz
      have hzl : z (Fin.last M) = y p := by simp [hz]
      have hzy : z ≠ y := fun h => hc (by rw [← hzl, h])
      have hzx : z ≠ x := fun h => hc (by rw [← hzl, h, hl])
      have hwz : wt z = wt y := wt_swap _ _ _
      exact (split_ne (IH x z hzx.symm (hw.trans hwz.symm)) (by rw [hzl, hl]; exact hc.symm)
        b).trans (split_ne (IH z y hzy hwz) (by rw [hzl]; exact hc) b) (snoc_ne hxy b)
  · exact split_ne (IH x y hxy hw) hl b

lemma same_last
    (IH : ∀ x y : Fin (M + 1) → Fin 2, x ≠ y → wt x = wt y → Rel (lieAlg (M + 1)) x y)
    {u w : Fin (M + 2) → Fin 2} (huw : u ≠ w) (hw : wt u = wt w) (hl : u ll = w ll) :
    Rel (lieAlg (M + 2)) u w := by
  have hne : Fin.init u ≠ Fin.init w := fun h =>
    huw (by rw [← Fin.snoc_init_self u, ← Fin.snoc_init_self w, h, hl])
  have hwt : wt (Fin.init u) = wt (Fin.init w) := by
    have h1 := wt_succ u
    have h2 := wt_succ w
    rw [hl] at h1
    omega
  have := split_all IH hne hwt (u ll)
  rwa [Fin.snoc_init_self, hl, Fin.snoc_init_self] at this

end induction

section cross

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma Mu_neg (x y : ι) (c : ℂ) : Mu x y (-c) = -Mu x y c := by
  rw [Mu, Mu, single_eq_smul x y (-c), single_eq_smul y x (star (-c)), single_eq_smul x y c,
    single_eq_smul y x (star c), star_neg]
  module

lemma Mu_decomp (x y : ι) (c : ℂ) :
    Mu x y c = c.re • Mu x y 1 + c.im • Mu x y Complex.I := by
  have hs : star c = (c.re : ℂ) - c.im * Complex.I := by
    apply Complex.ext <;> simp
  have hI : star Complex.I = -Complex.I := by simp
  rw [← Complex.coe_smul, ← Complex.coe_smul, Mu, Mu, Mu, single_eq_smul x y c,
    single_eq_smul y x (star c), single_eq_smul x y Complex.I,
    single_eq_smul y x (star Complex.I), star_one, hI]
  generalize Matrix.single x y (1 : ℂ) = E
  generalize Matrix.single y x (1 : ℂ) = E'
  have : c • E - star c • E' =
      ((c.re : ℂ) + c.im * Complex.I) • E - ((c.re : ℂ) - c.im * Complex.I) • E' := by
    rw [Complex.re_add_im, ← hs]
  rw [this]
  module

lemma Rel_of_two {L : LieSubalgebra ℝ (Matrix ι ι ℂ)} {x y : ι} (hxy : x ≠ y)
    (h1 : Mu x y 1 ∈ L) (hI : Mu x y Complex.I ∈ L) : Rel L x y :=
  ⟨hxy, fun c => by
    rw [Mu_decomp]
    exact L.add_mem (L.smul_mem _ h1) (L.smul_mem _ hI)⟩

end cross

section cross2

/-- On two qubits, `i T(0,0,0,0,1)` is the single edge between `|10⟩` and `|01⟩`. -/
lemma cross_two (u : Fin 2 → Fin 2)
    (hu : u (Fin.castSucc (Fin.last 0)) ≠ u (Fin.last 1)) :
    Rel (lieAlg 2) u (u ∘ Equiv.swap (Fin.castSucc (Fin.last 0)) (Fin.last 1)) := by
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, k = Fin.castSucc (Fin.last 0) := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l : Fin 2, l = Fin.last 1 := ⟨_, rfl⟩
  rw [← hk, ← hl] at hu ⊢
  have hkl : k ≠ l := by rw [hk, hl]; exact kk_ne_ll (M := 0)
  have hcover : ∀ m : Fin 2, m = k ∨ m = l := by
    intro m
    rw [hk, hl]
    fin_cases m
    · left; rfl
    · right; rfl
  have hG : Complex.I • embed 2 k l (Tmat 0 0 0 0 1) ∈ lieAlg 2 := by
    rw [hk, hl]; exact (last_gens (M := 0)).2
  have hD : Complex.I • Matrix.diagonal (fun z : Fin 2 → Fin 2 =>
      if z k = 1 ∧ z l = 0 then (1 : ℂ) else 0) ∈ lieAlg 2 := by
    rw [hk, hl]; exact (last_gens (M := 0)).1
  obtain ⟨u', hu'def⟩ : ∃ u', u' = u ∘ Equiv.swap k l := ⟨_, rfl⟩
  rw [← hu'def]
  have hu'k : u' k = u l := by simp [hu'def]
  have hu'l : u' l = u k := by simp [hu'def]
  have hu' : u' k ≠ u' l := by rw [hu'k, hu'l]; exact hu.symm
  have hu'' : u' ∘ Equiv.swap k l = u := by
    rw [hu'def]; funext m; simp
  have huu' : u ≠ u' := fun h => hu (by rw [← hu'k, ← h])
  have hGeq : Complex.I • embed 2 k l (Tmat 0 0 0 0 1) = Mu u u' Complex.I := by
    ext p q
    rw [Mu, Matrix.sub_apply, single_apply', single_apply', Complex.star_def, Complex.conj_I]
    by_cases hp : p k = p l
    · rw [(G_zero p hp q).1]
      have h1 : p ≠ u := fun h => hu (h ▸ hp)
      have h2 : p ≠ u' := fun h => hu' (h ▸ hp)
      simp [h1, h2]
    · have hpu : p = u ∨ p = u' := by
        by_cases h : p k = u k
        · left
          funext m
          rcases hcover m with rfl | rfl
          · exact h
          · exact fin2_trans (fun h' => hp (h.trans h'.symm)) hu
        · right
          funext m
          rcases hcover m with rfl | rfl
          · rw [hu'k]; exact fin2_trans h hu
          · rw [hu'l]; exact fin2_trans (Ne.symm hp) h
      rcases hpu with rfl | rfl
      · rw [G_row hkl p hu, ← hu'def]
        simp [huu']
      · rw [G_row hkl p hu', hu'']
        simp only [huu'.symm, false_and, if_false, true_and, zero_sub]
        split_ifs <;> simp
  have hMI : Mu u u' Complex.I ∈ lieAlg 2 := hGeq ▸ hG
  have hb := (lieAlg 2).lie_mem hD hMI
  rw [lie_diag_Mu, Complex.I_mul_I] at hb
  have h1 : Mu u u' (-1) ∈ lieAlg 2 := by
    rcases fin2_ne hu with ⟨a, b⟩ | ⟨a, b⟩
    · simpa [hu'k, hu'l, a, b] using hb
    · simpa [hu'k, hu'l, a, b] using hb
  rw [Mu_neg, neg_mem_iff] at h1
  exact Rel_of_two huu' h1 hMI

end cross2

section cross3

variable {M : ℕ}

local notation "kk" => (Fin.castSucc (Fin.last (M + 1)) : Fin (M + 3))
local notation "ll" => (Fin.last (M + 2) : Fin (M + 3))

lemma cross_aux
    (hA : ∀ u w : Fin (M + 3) → Fin 2, u ≠ w → wt u = wt w → u ll = w ll →
      Rel (lieAlg (M + 3)) u w)
    (u : Fin (M + 3) → Fin 2) (hu : u kk ≠ u ll) (h0 : u 0 ≠ u kk) :
    Rel (lieAlg (M + 3)) u (u ∘ Equiv.swap kk ll) := by
  have hkl : kk ≠ ll := kk_ne_ll (M := M + 1)
  have h0k : (0 : Fin (M + 3)) ≠ kk := by
    intro h; have := congrArg Fin.val h; simp at this
  have h0l : (0 : Fin (M + 3)) ≠ ll := by
    intro h; have := congrArg Fin.val h; simp at this
  obtain ⟨v, hv⟩ : ∃ v, v = u ∘ Equiv.swap 0 kk := ⟨_, rfl⟩
  obtain ⟨u', hu'def⟩ : ∃ u', u' = u ∘ Equiv.swap kk ll := ⟨_, rfl⟩
  rw [← hu'def]
  have hvk : v kk = u 0 := by simp [hv]
  have hvl : v ll = u ll := by
    rw [hv, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h0l.symm hkl.symm]
  have hvkl : v kk = v ll := by rw [hvk, hvl]; exact fin2_trans h0 hu
  have hvu : v ≠ u := fun h => h0 (by rw [← hvk, h])
  have hwv : wt v = wt u := by rw [hv]; exact wt_swap _ _ _
  have hu'k : u' kk = u ll := by simp [hu'def]
  have hu'l : u' ll = u kk := by simp [hu'def]
  have hvu' : v ≠ u' := fun h => hu (by rw [← hu'l, ← hu'k, ← h, hvkl])
  have huu' : u ≠ u' := fun h => hu (by rw [← hu'k, ← h])
  have hR := hA v u hvu hwv hvl
  have hG := (last_gens (M := M + 1)).2
  have hR' : Rel (lieAlg (M + 3)) v u' := by
    refine ⟨hvu', fun c => ?_⟩
    have hb := (lieAlg (M + 3)).lie_mem (hR.2 (c * -Complex.I)) hG
    rw [lie_Mu_of_rows _ (u := u) (u' := u') (v := v) Complex.I
      (fun y => (G_zero v hvkl y).1) (fun x => (G_zero v hvkl x).2)
      (fun y => by rw [G_row hkl u hu, hu'def])
      (fun x => by rw [G_col hkl u hu, hu'def]; simp)] at hb
    rwa [show c * -Complex.I * Complex.I = c by
      rw [mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, mul_one]] at hb
  exact hR.symm.trans hR' huu'

lemma cross_gen
    (hA : ∀ u w : Fin (M + 3) → Fin 2, u ≠ w → wt u = wt w → u ll = w ll →
      Rel (lieAlg (M + 3)) u w)
    (u : Fin (M + 3) → Fin 2) (hu : u kk ≠ u ll) :
    Rel (lieAlg (M + 3)) u (u ∘ Equiv.swap kk ll) := by
  have hkl : kk ≠ ll := kk_ne_ll (M := M + 1)
  have h0k : (0 : Fin (M + 3)) ≠ kk := by
    intro h; have := congrArg Fin.val h; simp at this
  have h0l : (0 : Fin (M + 3)) ≠ ll := by
    intro h; have := congrArg Fin.val h; simp at this
  by_cases h0 : u 0 = u kk
  · obtain ⟨u', hu'def⟩ : ∃ u', u' = u ∘ Equiv.swap kk ll := ⟨_, rfl⟩
    rw [← hu'def]
    have hu'k : u' kk = u ll := by simp [hu'def]
    have hu'l : u' ll = u kk := by simp [hu'def]
    have hu'0 : u' 0 = u 0 := by
      rw [hu'def, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h0k h0l]
    have hback : u' ∘ Equiv.swap kk ll = u := by
      rw [hu'def]; funext m; simp
    have := cross_aux hA u' (by rw [hu'k, hu'l]; exact hu.symm)
      (by rw [hu'0, hu'k, h0]; exact hu)
    rw [hback] at this
    exact this.symm
  · exact cross_aux hA u hu h0

end cross3

section connect

variable {M : ℕ}

local notation "kk" => (Fin.castSucc (Fin.last M) : Fin (M + 2))
local notation "ll" => (Fin.last (M + 1) : Fin (M + 2))

lemma connect_aux
    (hA : ∀ u w : Fin (M + 2) → Fin 2, u ≠ w → wt u = wt w → u ll = w ll →
      Rel (lieAlg (M + 2)) u w)
    (hc : ∀ u : Fin (M + 2) → Fin 2, u kk ≠ u ll → Rel (lieAlg (M + 2)) u (u ∘ Equiv.swap kk ll))
    (u w : Fin (M + 2) → Fin 2) (huw : u ≠ w) (hw : wt u = wt w) (hu0 : u ll = 0)
    (hw1 : w ll = 1) : Rel (lieAlg (M + 2)) u w := by
  have hkl : kk ≠ ll := kk_ne_ll
  have h1 := wt_succ u
  have h2 := wt_succ w
  rw [hu0] at h1
  rw [hw1] at h2
  simp only [Fin.isValue, zero_ne_one, if_false, add_zero, if_true] at h1 h2
  have hpos : 0 < wt (Fin.init u) := by omega
  rw [wt] at hpos
  obtain ⟨p', hp'⟩ := Finset.card_pos.mp hpos
  have hp1 : u p'.castSucc = 1 := (Finset.mem_filter.mp hp').2
  have hpl : p'.castSucc ≠ ll := Fin.castSucc_ne_last p'
  obtain ⟨u1, hu1⟩ : ∃ u1, u1 = u ∘ Equiv.swap p'.castSucc kk := ⟨_, rfl⟩
  have hu1k : u1 kk = 1 := by simp [hu1, hp1]
  have hu1l : u1 ll = 0 := by
    rw [hu1, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hpl.symm hkl.symm, hu0]
  have hwu1 : wt u1 = wt u := by rw [hu1]; exact wt_swap _ _ _
  have hr1 : u = u1 ∨ Rel (lieAlg (M + 2)) u u1 := by
    by_cases h : u = u1
    · exact Or.inl h
    · exact Or.inr (hA u u1 h hwu1.symm (by rw [hu0, hu1l]))
  obtain ⟨u2, hu2⟩ : ∃ u2, u2 = u1 ∘ Equiv.swap kk ll := ⟨_, rfl⟩
  have hcr : Rel (lieAlg (M + 2)) u1 u2 := by
    rw [hu2]; exact hc u1 (by rw [hu1k, hu1l]; simp)
  have hu2l : u2 ll = 1 := by simp [hu2, hu1k]
  have hwu2 : wt u2 = wt u1 := by rw [hu2]; exact wt_swap _ _ _
  have huu2 : u ≠ u2 := fun h => by
    have := congrFun h ll
    rw [hu0, hu2l] at this
    exact absurd this (by simp)
  have hr2 : Rel (lieAlg (M + 2)) u u2 := Rel.trans' hr1 hcr huu2
  by_cases h : u2 = w
  · rw [← h]; exact hr2
  · exact hr2.trans (hA u2 w h (by rw [hwu2, hwu1, hw]) (by rw [hu2l, hw1])) huw

lemma connect
    (hA : ∀ u w : Fin (M + 2) → Fin 2, u ≠ w → wt u = wt w → u ll = w ll →
      Rel (lieAlg (M + 2)) u w)
    (hc : ∀ u : Fin (M + 2) → Fin 2, u kk ≠ u ll → Rel (lieAlg (M + 2)) u (u ∘ Equiv.swap kk ll))
    (u w : Fin (M + 2) → Fin 2) (huw : u ≠ w) (hw : wt u = wt w) :
    Rel (lieAlg (M + 2)) u w := by
  by_cases hl : u ll = w ll
  · exact hA u w huw hw hl
  · rcases fin2_ne hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (connect_aux hA hc w u huw.symm hw.symm h2 h1).symm
    · exact connect_aux hA hc u w huw hw h1 h2

end connect

/-- Every pair of distinct basis states of equal Hamming weight is joined in `L`. -/
theorem main (n : ℕ) :
    ∀ u w : Fin n → Fin 2, u ≠ w → wt u = wt w → Rel (lieAlg n) u w := by
  induction n with
  | zero => exact fun u w h _ => absurd (Subsingleton.elim u w) h
  | succ n ih =>
    rcases n with _ | M
    · intro u w huw hw
      exfalso
      have h1 := wt_succ u
      have h2 := wt_succ w
      rw [Subsingleton.elim (Fin.init u) (Fin.init w)] at h1
      have hl : u (Fin.last 0) = w (Fin.last 0) := by
        by_contra hne
        rcases fin2_ne hne with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [a] at h1 <;> rw [b] at h2 <;>
          simp at h1 h2 <;> omega
      exact huw (by
        rw [← Fin.snoc_init_self u, ← Fin.snoc_init_self w,
          Subsingleton.elim (Fin.init u) (Fin.init w), hl])
    · have hA : ∀ u w : Fin (M + 2) → Fin 2, u ≠ w → wt u = wt w →
          u (Fin.last (M + 1)) = w (Fin.last (M + 1)) → Rel (lieAlg (M + 2)) u w :=
        fun u w h1 h2 h3 => same_last ih h1 h2 h3
      refine connect hA ?_
      rcases M with _ | M'
      · exact cross_two
      · exact cross_gen hA

end BaconThesis.WeakUniv.SolB01

open BaconThesis.WeakUniv BaconThesis.WeakUniv.SolB01
open scoped Matrix

theorem solution (n : ℕ) (hn : 2 ≤ n) (h : ℕ) (hh : h ≤ n)
    (X : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) (hX : Xᴴ = -X)
    (hsupp : dfsProj n h * X * dfsProj n h = X) (htr : X.trace = 0) :
    X ∈ lieAlg n := by
  classical
  have hmain := main n
  -- entries vanish off the weight-`h` sector
  have hXs : ∀ x y, X x y ≠ 0 → wt x = h ∧ wt y = h := by
    intro x y hxy
    have he : X x y = (if wt x = h then 1 else 0) * X x y * (if wt y = h then 1 else 0) := by
      conv_lhs => rw [← hsupp]
      simp only [dfsProj, Matrix.mul_diagonal, Matrix.diagonal_mul]
      rfl
    by_contra hcon
    apply hxy
    rw [he]
    by_cases h1 : wt x = h
    · have h2 : ¬ wt y = h := fun h2 => hcon ⟨h1, h2⟩
      simp [h2]
    · simp [h1]
  have hstar : ∀ x y, star (X x y) = -X y x := by
    intro x y
    have := congrFun (congrFun hX y) x
    simpa [Matrix.conjTranspose_apply] using this
  -- off-diagonal part
  have hoff : ∀ x y, x ≠ y → Mu x y (X x y) ∈ lieAlg n := by
    intro x y hne
    by_cases hz : X x y = 0
    · rw [hz, Mu_zero]; exact (lieAlg n).zero_mem
    · obtain ⟨h1, h2⟩ := hXs x y hz
      exact (hmain x y hne (h1.trans h2.symm)).2 _
  have hMd : ∀ x, Mu x x (X x x) = (2 * X x x) • Matrix.single x x (1 : ℂ) := by
    intro x
    rw [Mu, hstar, single_eq_smul x x (X x x), single_eq_smul x x (-X x x)]
    module
  have hXim : ∀ x, X x x = ((X x x).im : ℂ) * Complex.I := by
    intro x
    have h1 := congrArg Complex.re (hstar x x)
    simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at h1
    apply Complex.ext
    · simp; linarith
    · simp
  -- diagonal part
  have hdiag : ∑ x, Mu x x (X x x) ∈ lieAlg n := by
    by_cases hex : ∃ x0, X x0 x0 ≠ 0
    · obtain ⟨x0, hx0⟩ := hex
      have hsum : ∑ x, Mu x x (X x x) =
          ∑ x, (2 * X x x) • (Matrix.single x x (1 : ℂ) - Matrix.single x0 x0 1) := by
        simp only [hMd, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, ← Finset.mul_sum]
        have : ∑ i, X i i = 0 := htr
        rw [this, mul_zero, zero_smul, sub_zero]
      rw [hsum]
      refine (lieAlg n).sum_mem fun x _ => ?_
      by_cases hz : X x x = 0
      · rw [hz, mul_zero, zero_smul]; exact (lieAlg n).zero_mem
      · by_cases hxx0 : x = x0
        · rw [hxx0, sub_self, smul_zero]; exact (lieAlg n).zero_mem
        · have hR := hmain x x0 hxx0 ((hXs x x hz).1.trans (hXs x0 x0 hx0).1.symm)
          have hb := (lieAlg n).lie_mem (hR.2 1) (hR.2 Complex.I)
          rw [lie_Mu_self hxx0] at hb
          have := (lieAlg n).smul_mem (X x x).im hb
          rw [← Complex.coe_smul, smul_smul] at this
          rwa [show ((X x x).im : ℂ) * (2 * Complex.I) = 2 * X x x by
            conv_rhs => rw [hXim x]
            ring] at this
    · push Not at hex
      have : ∑ x, Mu x x (X x x) = 0 :=
        Finset.sum_eq_zero fun x _ => by rw [hex x, Mu_zero]
      rw [this]; exact (lieAlg n).zero_mem
  -- assemble
  have hXsum : (2 : ℂ) • X = ∑ x, ∑ y, Mu x y (X x y) := by
    have e1 : X = ∑ x, ∑ y, Matrix.single x y (X x y) := Matrix.matrix_eq_sum_single X
    have e2 : ∑ x, ∑ y, Matrix.single y x (star (X x y)) = -X := by
      rw [Finset.sum_comm]
      conv_rhs => rw [e1]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hstar, single_eq_smul y x (-X y x), single_eq_smul y x (X y x)]
      module
    simp only [Mu, Finset.sum_sub_distrib]
    rw [e2, ← e1]
    module
  have hsplit : ∑ x, ∑ y, Mu x y (X x y) =
      ∑ x, ∑ y, (if x = y then 0 else Mu x y (X x y)) + ∑ x, Mu x x (X x x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have : ∑ y, Mu x y (X x y) =
        ∑ y, ((if x = y then 0 else Mu x y (X x y)) + if x = y then Mu x y (X x y) else 0) :=
      Finset.sum_congr rfl fun y _ => by split_ifs <;> simp
    rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ x)]
  have hall : ∑ x, ∑ y, Mu x y (X x y) ∈ lieAlg n := by
    rw [hsplit]
    refine (lieAlg n).add_mem ((lieAlg n).sum_mem fun x _ => (lieAlg n).sum_mem fun y _ => ?_)
      hdiag
    split_ifs with hxy
    · exact (lieAlg n).zero_mem
    · exact hoff x y hxy
  have hfin := (lieAlg n).smul_mem (1 / 2 : ℝ) hall
  rw [← hXsum, ← Complex.coe_smul, smul_smul] at hfin
  simpa using hfin
