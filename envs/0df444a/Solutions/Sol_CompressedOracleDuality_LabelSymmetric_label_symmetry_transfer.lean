-- Prove2me | solution 1 for CompressedOracleDuality.LabelSymmetric.label_symmetry_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:39:03.885462+00:00
-- url     : https://prove2.me/submissions/348e6eb8-1fa6-402d-9c59-369b2978e228

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Progress

-- ===== from Solutions/COD/C.lean =====

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

namespace CODInfra

/-- the real scale 2^{-m/2} -/
def sc (m : ℕ) : ℝ := (Real.sqrt 2)⁻¹ ^ m

lemma sc_sq (m : ℕ) : sc m ^ 2 = ((2:ℝ) ^ m)⁻¹ := by
  rw [sc, ← pow_mul, mul_comm, pow_mul, inv_pow, Real.sq_sqrt (by norm_num), inv_pow]

lemma sc_pos (m : ℕ) : 0 < sc m := by unfold sc; positivity

lemma sc_sq_mul (m : ℕ) : sc m * sc m = ((2:ℝ) ^ m)⁻¹ := by rw [← sq, sc_sq]

lemma card_qubits (m : ℕ) : Fintype.card (Qubits m) = 2 ^ m := by
  simp [Qubits]

lemma C_none_none (m : ℕ) : compressionUnitary m none none = 0 := rfl
lemma C_none_some (m : ℕ) (w : Qubits m) : compressionUnitary m none (some w) = (sc m : ℂ) := rfl
lemma C_some_none (m : ℕ) (z : Qubits m) : compressionUnitary m (some z) none = (sc m : ℂ) := rfl
lemma C_some_some (m : ℕ) (z w : Qubits m) :
    compressionUnitary m (some z) (some w) = (if z = w then 1 else 0) - (((2:ℝ)^m)⁻¹ : ℂ) := by
  show (if z = w then 1 else 0) - (((sc m) ^ 2 : ℝ) : ℂ) = _
  rw [sc_sq]; push_cast; rfl

lemma C_symm (m : ℕ) (a b : Option (Qubits m)) :
    compressionUnitary m a b = compressionUnitary m b a := by
  cases a <;> cases b <;> simp only [C_none_none, C_none_some, C_some_none, C_some_some, eq_comm]

lemma C_star (m : ℕ) (a b : Option (Qubits m)) :
    star (compressionUnitary m a b) = compressionUnitary m a b := by
  cases a <;> cases b <;> simp only [C_none_none, C_none_some, C_some_none, C_some_some] <;>
    first | simp | (split_ifs <;> simp)

lemma two_pow_ne (m : ℕ) : ((2:ℂ)^m) ≠ 0 := by positivity

lemma sc_sq_C (m : ℕ) : (sc m : ℂ) * (sc m : ℂ) = (((2:ℝ)^m)⁻¹ : ℂ) := by
  rw [← Complex.ofReal_mul, sc_sq_mul]; push_cast; rfl

/-- Σ_y C(some y, e). -/
lemma sum_C_some_left (m : ℕ) (e : Option (Qubits m)) :
    ∑ y : Qubits m, compressionUnitary m (some y) e =
      if e = none then (((2:ℝ)^m * sc m : ℝ) : ℂ) else 0 := by
  cases e with
  | none => simp [C_some_none, card_qubits]
  | some w =>
    simp only [C_some_some, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_const, Finset.card_univ, card_qubits, nsmul_eq_mul, reduceCtorEq, if_false]
    have := two_pow_ne m
    push_cast; field_simp; ring

lemma C_mul_C (m : ℕ) : compressionUnitary m * compressionUnitary m = 1 := by
  have hN := two_pow_ne m
  have hs := sc_sq_C m
  ext a b
  rw [Matrix.mul_apply, Fintype.sum_option]
  cases a with
  | none =>
    cases b with
    | none =>
      simp only [C_none_none, C_none_some, C_some_none, mul_zero, zero_add, Finset.sum_const,
        Finset.card_univ, card_qubits, nsmul_eq_mul, Matrix.one_apply_eq, hs]
      push_cast; field_simp
    | some w =>
      simp only [C_none_none, C_none_some, C_some_some, zero_mul, zero_add, Matrix.one_apply,
        reduceCtorEq, if_false, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
        card_qubits, nsmul_eq_mul]
      push_cast; field_simp; ring
  | some z =>
    cases b with
    | none =>
      simp only [C_none_none, C_some_none, C_some_some, mul_zero, zero_add, Matrix.one_apply,
        reduceCtorEq, if_false, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
        card_qubits, nsmul_eq_mul]
      push_cast; field_simp; ring
    | some w =>
      simp only [C_some_none, C_none_some, C_some_some, Matrix.one_apply, Option.some.injEq, hs]
      simp only [sub_mul, mul_sub, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Finset.sum_const, Finset.card_univ, card_qubits, nsmul_eq_mul, Finset.sum_ite_irrel]
      split_ifs with h <;> push_cast <;> field_simp <;> ring

end CODInfra


-- ===== from Solutions/COD/CA.lean =====

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

namespace CODInfra

variable {n m : ℕ}

lemma compressAll_apply (D D' : Fin n → Option (Qubits m)) :
    compressAll n m D D' = ∏ i, compressionUnitary m (D i) (D' i) := rfl

/-- Product-of-sums for the cellwise products. -/
lemma sum_prod_cells (g : Fin n → Option (Qubits m) → ℂ) :
    ∑ E : Fin n → Option (Qubits m), ∏ i, g i (E i) = ∏ i, ∑ e, g i e := by
  rw [Fintype.prod_sum]

lemma compressAll_mul_self : compressAll n m * compressAll n m = 1 := by
  ext D D'
  rw [Matrix.mul_apply]
  simp only [compressAll_apply, ← Finset.prod_mul_distrib]
  rw [sum_prod_cells (fun i e => compressionUnitary m (D i) e * compressionUnitary m e (D' i))]
  have : ∀ i, ∑ e, compressionUnitary m (D i) e * compressionUnitary m e (D' i) =
      (1 : Matrix _ _ ℂ) (D i) (D' i) := fun i => by
    rw [← C_mul_C m, Matrix.mul_apply]
  simp only [this, Matrix.one_apply]
  by_cases h : D = D'
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, D i ≠ D' i := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma compressAll_symm (D D' : Fin n → Option (Qubits m)) :
    compressAll n m D D' = compressAll n m D' D := by
  simp only [compressAll_apply, C_symm m (D _)]

lemma compressAll_star (D D' : Fin n → Option (Qubits m)) :
    star (compressAll n m D D') = compressAll n m D D' := by
  simp only [compressAll_apply, star_prod, C_star]

lemma compressAll_conjTranspose : (compressAll n m).conjTranspose = compressAll n m := by
  ext D D'
  rw [Matrix.conjTranspose_apply, compressAll_star, compressAll_symm]

/-- the local lookup indicator -/
def lam (y' y : Qubits m) (b : Option (Qubits m)) : ℂ :=
  if y' = (match b with | some v => y + v | none => y) then 1 else 0

/-- the single-cell compressed-oracle matrix -/
def localM (m : ℕ) (y' y : Qubits m) (a' a : Option (Qubits m)) : ℂ :=
  ∑ b, compressionUnitary m a' b * compressionUnitary m b a * lam y' y b

lemma lookup_apply {W : Type*} [DecidableEq W] (p q : ((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))) :
    lookupUnitary n m W p q = if p.1.1.1 = q.1.1.1 ∧ p.1.2 = q.1.2 ∧ p.2 = q.2 then
      lam p.1.1.2 q.1.1.2 (q.2 q.1.1.1) else 0 := by
  unfold lookupUnitary lam
  simp only [Matrix.of_apply]
  by_cases h : p.1.1.1 = q.1.1.1 ∧ p.1.2 = q.1.2 ∧ p.2 = q.2
  · rw [if_pos h]
    cases q.2 q.1.1.1 <;> simp [h]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, h'.2.1, h'.2.2.1⟩)]

lemma kron1_apply {X Y : Type*} [DecidableEq X] (M : Matrix Y Y ℂ) (p q : X × Y) :
    Matrix.kronecker (1 : Matrix X X ℂ) M p q = if p.1 = q.1 then M p.2 q.2 else 0 := by
  obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]; split_ifs <;> simp

lemma mul_kron1_apply {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
    (M : Matrix (X × Y) (X × Y) ℂ) (B : Matrix Y Y ℂ) (p q : X × Y) :
    (M * Matrix.kronecker (1 : Matrix X X ℂ) B) p q = ∑ E, M p (q.1, E) * B E q.2 := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [kron1_apply, mul_ite, mul_zero]
  rw [Finset.sum_eq_single q.1]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma kron1_mul_apply {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
    (M : Matrix (X × Y) (X × Y) ℂ) (B : Matrix Y Y ℂ) (p q : X × Y) :
    (Matrix.kronecker (1 : Matrix X X ℂ) B * M) p q = ∑ E, B p.2 E * M (p.1, E) q := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [kron1_apply, ite_mul, zero_mul]
  rw [Finset.sum_eq_single p.1]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem compressedOracle_apply {W : Type*} [Fintype W] [DecidableEq W]
    (x' x : Fin n) (y' y : Qubits m) (w' w : W) (D' D : Fin n → Option (Qubits m)) :
    compressedOracle n m W (((x', y'), w'), D') (((x, y), w), D) =
      if x' = x ∧ w' = w ∧ (∀ i, i ≠ x → D' i = D i) then localM m y' y (D' x) (D x) else 0 := by
  rw [compressedOracle, mul_kron1_apply]
  simp_rw [kron1_mul_apply, lookup_apply]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul]
  have key : ∑ E : Fin n → Option (Qubits m), compressAll n m D' E * lam y' y (E x) *
      compressAll n m E D = if (∀ i, i ≠ x → D' i = D i) then localM m y' y (D' x) (D x) else 0 := by
    simp only [compressAll_apply]
    have : ∀ E : Fin n → Option (Qubits m), (∏ i, compressionUnitary m (D' i) (E i)) * lam y' y (E x) *
        ∏ i, compressionUnitary m (E i) (D i) = ∏ i, (compressionUnitary m (D' i) (E i) *
          compressionUnitary m (E i) (D i) * (if i = x then lam y' y (E i) else 1)) := by
      intro E
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ x]
      simp; ring
    simp_rw [this]
    rw [sum_prod_cells (fun i e => compressionUnitary m (D' i) e * compressionUnitary m e (D i) *
      (if i = x then lam y' y e else 1))]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
    simp only [if_true]
    have hrest : ∀ i ∈ Finset.univ.erase x, (∑ e, compressionUnitary m (D' i) e *
        compressionUnitary m e (D i) * (if i = x then lam y' y e else 1)) =
        if D' i = D i then 1 else 0 := by
      intro i hi
      simp only [if_neg (Finset.ne_of_mem_erase hi), mul_one]
      have := congrFun (congrFun (C_mul_C m) (D' i)) (D i)
      simp only [Matrix.mul_apply, Matrix.one_apply] at this
      exact this
    rw [Finset.prod_congr rfl hrest, Finset.prod_boole]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, localM]
    split_ifs <;> simp
  by_cases hxw : x' = x ∧ w' = w
  · simp only [hxw, true_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [key]
  · have : ∀ a : Prop, ¬ (x' = x ∧ w' = w ∧ a) := fun a h => hxw ⟨h.1, h.2.1⟩
    simp only [this, if_false, Finset.sum_const_zero, zero_mul]

end CODInfra


-- ===== from Solutions/COD/Purify.lean =====

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

namespace CODInfra

variable {n m : ℕ}

lemma act_apply {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) (i : ι) :
    act A v i = ∑ j, A i j * v j := rfl

lemma act_act {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act A (act B v) = act (A * B) v := by
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec_mulVec]

lemma act_one {ι : Type*} [Fintype ι] [DecidableEq ι] (v : EuclideanSpace ℂ ι) :
    act 1 v = v := by
  simp only [act, Matrix.one_mulVec, WithLp.toLp_ofLp]

lemma act_kron_one_apply {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (U : Matrix X X ℂ) (v : EuclideanSpace ℂ (X × Y)) (z : X) (E : Y) :
    act (Matrix.kronecker U (1 : Matrix Y Y ℂ)) v (z, E) = ∑ z', U z z' * v (z', E) := by
  rw [act_apply, Fintype.sum_prod_type]
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma act_one_kron_apply {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
    (B : Matrix Y Y ℂ) (v : EuclideanSpace ℂ (X × Y)) (z : X) (E : Y) :
    act (Matrix.kronecker (1 : Matrix X X ℂ) B) v (z, E) = ∑ E', B E E' * v (z, E') := by
  rw [act_apply, Fintype.sum_prod_type]
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single z]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

lemma kron_comm_one {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (U : Matrix X X ℂ) (B : Matrix Y Y ℂ) :
    Matrix.kronecker U (1 : Matrix Y Y ℂ) * Matrix.kronecker (1 : Matrix X X ℂ) B =
      Matrix.kronecker (1 : Matrix X X ℂ) B * Matrix.kronecker U (1 : Matrix Y Y ℂ) := by
  simp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

/-- the oracle-register-side compression `I ⊗ C^{⊗n}` -/
abbrev Kc (n m : ℕ) (W : Type*) [Fintype W] [DecidableEq W] :
    Matrix (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m)))
      (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))) ℂ :=
  Matrix.kronecker (1 : Matrix ((Fin n × Qubits m) × W) ((Fin n × Qubits m) × W) ℂ)
    (compressAll n m)

lemma Kc_mul_Kc (W : Type*) [Fintype W] [DecidableEq W] : Kc n m W * Kc n m W = 1 := by
  simp only [Kc, Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul, compressAll_mul_self]; simp

/-- The purified standard-oracle state `Σ_f 2^{-mn/2} |ψ_t^f⟩|f⟩`. -/
def purified {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Fin n) (Qubits m) W T) (t : Fin (T + 1)) :
    EuclideanSpace ℂ (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))) :=
  WithLp.toLp 2 fun p => ∑ f : Fin n → Qubits m,
    if p.2 = (fun i => some (f i)) then ((sc m ^ n : ℝ) : ℂ) * A.stateAt (xorOracle f) t p.1 else 0

lemma purified_apply {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Fin n) (Qubits m) W T) (t : Fin (T + 1)) (z) (E : Fin n → Option (Qubits m)) :
    purified A t (z, E) = ∑ f : Fin n → Qubits m,
      if E = (fun i => some (f i)) then ((sc m ^ n : ℝ) : ℂ) * A.stateAt (xorOracle f) t z else 0 :=
  rfl

lemma purified_some {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Fin n) (Qubits m) W T) (t : Fin (T + 1)) (z) (f : Fin n → Qubits m) :
    purified A t (z, fun i => some (f i)) = ((sc m ^ n : ℝ) : ℂ) * A.stateAt (xorOracle f) t z := by
  rw [purified_apply, Finset.sum_eq_single f]
  · simp
  · intro g _ hg
    rw [if_neg]
    intro h; apply hg; funext i; have := congrFun h i; simpa using this.symm
  · simp

lemma purified_not_some {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Fin n) (Qubits m) W T) (t : Fin (T + 1)) (z) (E : Fin n → Option (Qubits m))
    (hE : ∃ i, E i = none) : purified A t (z, E) = 0 := by
  rw [purified_apply]
  apply Finset.sum_eq_zero
  intro f _
  rw [if_neg]
  rintro rfl
  obtain ⟨i, hi⟩ := hE
  simp at hi

lemma sum_compressAll_some (D : Fin n → Option (Qubits m)) :
    ∑ f : Fin n → Qubits m, compressAll n m D (fun i => some (f i)) =
      if D = (fun _ => none) then ((((2:ℝ)^m * sc m) ^ n : ℝ) : ℂ) else 0 := by
  simp only [compressAll_apply]
  rw [← Fintype.prod_sum (fun i a => compressionUnitary m (D i) (some a))]
  have : ∀ i, ∑ a, compressionUnitary m (D i) (some a) =
      if D i = none then (((2:ℝ)^m * sc m : ℝ) : ℂ) else 0 := by
    intro i
    simp_rw [C_symm m (D i)]
    exact sum_C_some_left m (D i)
  simp_rw [this]
  rw [Finset.prod_ite_zero]
  by_cases h : D = fun _ => none
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro h'; apply h; funext i; simpa using h' i

lemma N_sc_sq (m : ℕ) : ((2:ℝ)^m * sc m) * sc m = 1 := by
  rw [mul_assoc, sc_sq_mul]; field_simp

/-- **Purification identity**: the compressed-oracle state is `(I ⊗ C^{⊗n})` applied to the
purified standard-oracle state. -/
theorem compressedStateAt_eq {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Fin n) (Qubits m) W T) (t : Fin (T + 1)) :
    compressedStateAt A t = act (Kc n m W) (purified A t) := by
  induction t using Fin.induction with
  | zero =>
    ext ⟨z, D⟩
    simp only [compressedStateAt, Fin.induction_zero]
    rw [act_kron_one_apply, act_one_kron_apply]
    simp_rw [purified_apply]
    simp only [mul_ite, mul_zero, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have h0 : ∀ f : Fin n → Qubits m, A.stateAt (xorOracle f) 0 = act (A.U 0 : Matrix _ _ ℂ) A.start :=
      fun f => by simp [QueryAlg.stateAt]
    simp_rw [h0]
    rw [← Finset.sum_mul, sum_compressAll_some]
    simp only [tensorVec, ket, WithLp.ofLp_toLp, PiLp.single_apply]
    by_cases hD : D = fun _ => none
    · subst hD
      simp only [if_true, mul_one]
      rw [← mul_assoc, ← Complex.ofReal_mul, ← mul_pow, N_sc_sq, one_pow]
      simp [act_apply]
    · simp [hD]
  | succ s ih =>
    have hstep : compressedStateAt A s.succ = act (Matrix.kronecker (A.U s.succ : Matrix _ _ ℂ)
        (1 : Matrix (Fin n → Option (Qubits m)) (Fin n → Option (Qubits m)) ℂ))
        (act (compressedOracle n m W) (compressedStateAt A s.castSucc)) := by
      simp [compressedStateAt, Fin.induction_succ]
    rw [hstep, ih]
    have hO : compressedOracle n m W = Kc n m W * lookupUnitary n m W * Kc n m W := rfl
    have hcomm : Matrix.kronecker (A.U s.succ : Matrix _ _ ℂ)
        (1 : Matrix (Fin n → Option (Qubits m)) (Fin n → Option (Qubits m)) ℂ) * Kc n m W =
        Kc n m W * Matrix.kronecker (A.U s.succ : Matrix _ _ ℂ)
        (1 : Matrix (Fin n → Option (Qubits m)) (Fin n → Option (Qubits m)) ℂ) :=
      kron_comm_one _ _
    have hM : Matrix.kronecker (A.U s.succ : Matrix _ _ ℂ)
        (1 : Matrix (Fin n → Option (Qubits m)) (Fin n → Option (Qubits m)) ℂ) *
        (Kc n m W * lookupUnitary n m W * Kc n m W) * Kc n m W =
        Kc n m W * (Matrix.kronecker (A.U s.succ : Matrix _ _ ℂ)
        (1 : Matrix (Fin n → Option (Qubits m)) (Fin n → Option (Qubits m)) ℂ) *
          lookupUnitary n m W) := by
      simp only [mul_assoc, Kc_mul_Kc, mul_one]
      rw [← mul_assoc, hcomm, mul_assoc]
    rw [hO, act_act, act_act, hM, ← act_act, ← act_act]
    congr 1
    ext ⟨z, E⟩
    rw [act_kron_one_apply, purified_apply]
    have hL : ∀ z', act (lookupUnitary n m W) (purified A s.castSucc) (z', E) =
        ∑ f : Fin n → Qubits m, if E = (fun i => some (f i)) then ((sc m ^ n : ℝ) : ℂ) *
          act (Matrix.kronecker (xorOracle f) (1 : Matrix W W ℂ))
            (A.stateAt (xorOracle f) s.castSucc) z' else 0 := by
      intro z'
      rw [act_apply, Fintype.sum_prod_type]
      simp_rw [lookup_apply]
      simp only [ite_mul, zero_mul]
      have hin : ∀ x : (Fin n × Qubits m) × W, (∑ x_1 : Fin n → Option (Qubits m),
          if z'.1.1 = x.1.1 ∧ z'.2 = x.2 ∧ E = x_1 then
            lam z'.1.2 x.1.2 (x_1 x.1.1) * purified A s.castSucc (x, x_1) else 0) =
          if z'.1.1 = x.1.1 ∧ z'.2 = x.2 then
            lam z'.1.2 x.1.2 (E x.1.1) * purified A s.castSucc (x, E) else 0 := by
        intro x
        rw [Finset.sum_eq_single E]
        · simp
        · intro b _ hb; rw [if_neg]; exact fun h => hb h.2.2.symm
        · simp
      simp_rw [hin]
      by_cases hE : ∃ f : Fin n → Qubits m, E = fun i => some (f i)
      · obtain ⟨f, rfl⟩ := hE
        rw [Finset.sum_eq_single f]
        · simp only [if_true, purified_some, act_apply, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          obtain ⟨⟨x1, x2⟩, x3⟩ := x
          obtain ⟨⟨y1, y2⟩, y3⟩ := z'
          simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, xorOracle,
            Matrix.of_apply, lam]
          by_cases h1 : y1 = x1 <;> by_cases h3 : y3 = x3 <;> simp [h1, h3] <;> ring
        · intro g _ hg; rw [if_neg]; intro h; apply hg; funext i
          have := congrFun h i; simpa using this.symm
        · simp
      · push Not at hE
        rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
        · intro f _; rw [if_neg (hE f)]
        · intro x _
          have hn : ∃ i, E i = none := by
            by_contra hc; push Not at hc
            apply hE (fun i => (E i).get (Option.isSome_iff_ne_none.mpr (hc i)))
            funext i; simp
          rw [purified_not_some A _ _ E hn]; simp
    simp_rw [hL]
    have hS : ∀ f : Fin n → Qubits m, A.stateAt (xorOracle f) s.succ =
        act (A.U s.succ : Matrix _ _ ℂ) (act (Matrix.kronecker (xorOracle f) (1 : Matrix W W ℂ))
          (A.stateAt (xorOracle f) s.castSucc)) := fun f => by
      simp [QueryAlg.stateAt, Fin.induction_succ]
    simp_rw [hS, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f _
    split_ifs
    · rw [act_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro x _; ring
    · simp

end CODInfra


-- ===== from Solutions/COD/Norm.lean =====

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

namespace CODInfra

variable {n m : ℕ}

lemma inner_eq_sum {ι : Type*} [Fintype ι] (v w : EuclideanSpace ℂ ι) :
    inner ℂ v w = ∑ i, star (v i) * w i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_comm]

lemma inner_act_act {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (v w : EuclideanSpace ℂ ι) :
    inner ℂ (act M v) (act M w) = inner ℂ v (act (M.conjTranspose * M) w) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, act, WithLp.ofLp_toLp]
  rw [← Matrix.mulVec_mulVec, Matrix.star_mulVec, dotProduct_comm _ (star _),
    Matrix.dotProduct_mulVec, dotProduct_comm]

lemma norm_act_of_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (hM : M.conjTranspose * M = 1) (v : EuclideanSpace ℂ ι) : ‖act M v‖ = ‖v‖ := by
  have h := inner_act_act M v v
  rw [hM, act_one, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have : ‖act M v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 this

lemma unitary_ct_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) :
    (U : Matrix ι ι ℂ).conjTranspose * (U : Matrix ι ι ℂ) = 1 := by
  have := U.2
  rw [Matrix.mem_unitaryGroup_iff'] at this
  simpa [Matrix.star_eq_conjTranspose] using this

lemma kron_one_ct_mul {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (U : Matrix X X ℂ) (hU : U.conjTranspose * U = 1) :
    (Matrix.kronecker U (1 : Matrix Y Y ℂ)).conjTranspose * Matrix.kronecker U (1 : Matrix Y Y ℂ) = 1 := by
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU]; simp

lemma one_kron_ct_mul {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (U : Matrix Y Y ℂ) (hU : U.conjTranspose * U = 1) :
    (Matrix.kronecker (1 : Matrix X X ℂ) U).conjTranspose * Matrix.kronecker (1 : Matrix X X ℂ) U = 1 := by
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU]; simp

lemma xorOracle_ct_mul {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [AddCommGroup κ] (f : ι → κ) : (xorOracle f).conjTranspose * xorOracle f = 1 := by
  have h1 : (xorOracle f).conjTranspose = xorOracle (-f) := by
    ext ⟨i, y⟩ ⟨j, z⟩
    simp only [Matrix.conjTranspose_apply, xorOracle, Matrix.of_apply, Pi.neg_apply]
    by_cases hij : i = j
    · subst hij
      by_cases h : z = y + f i
      · simp [h]
      · have : ¬ y = z + -f i := by intro h'; apply h; rw [h']; abel
        simp [h, this]
    · simp [hij, Ne.symm hij]
  rw [h1]
  have := xorOracle_mul_neg (-f)
  simpa using this

lemma Kc_ct_mul (W : Type*) [Fintype W] [DecidableEq W] :
    (Kc n m W).conjTranspose * Kc n m W = 1 := by
  apply one_kron_ct_mul
  rw [compressAll_conjTranspose, compressAll_mul_self]

lemma norm_stateAt {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W] [DecidableEq ι]
    [DecidableEq κ] [DecidableEq W] [AddCommGroup κ] {T : ℕ} (A : QueryAlg ι κ W T)
    (f : ι → κ) (t : Fin (T + 1)) : ‖A.stateAt (xorOracle f) t‖ = 1 := by
  induction t using Fin.induction with
  | zero =>
    simp only [QueryAlg.stateAt, Fin.induction_zero]
    rw [norm_act_of_unitary _ (unitary_ct_mul _), A.start_unit]
  | succ s ih =>
    simp only [QueryAlg.stateAt, Fin.induction_succ] at ih ⊢
    rw [norm_act_of_unitary _ (unitary_ct_mul _),
      norm_act_of_unitary _ (kron_one_ct_mul _ (xorOracle_ct_mul f)), ih]

lemma sum_db_some {M : Type*} [AddCommMonoid M] (g : (Fin n → Option (Qubits m)) → M)
    (hg : ∀ E, (∃ i, E i = none) → g E = 0) :
    ∑ E, g E = ∑ f : Fin n → Qubits m, g (fun i => some (f i)) := by
  have hinj : Function.Injective (fun (f : Fin n → Qubits m) (i : Fin n) => some (f i)) := by
    intro f g h; funext i; have := congrFun h i; simpa using this
  rw [← Finset.sum_image (fun a _ b _ h => hinj h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro E _ hE
  apply hg
  by_contra hc; push Not at hc
  apply hE
  rw [Finset.mem_image]
  refine ⟨fun i => (E i).get (Option.isSome_iff_ne_none.mpr (hc i)), Finset.mem_univ _, ?_⟩
  funext i; simp

lemma norm_sq_eq_sum {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    ‖v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]

lemma norm_purified {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Fin n) (Qubits m) W T) (t : Fin (T + 1)) : ‖purified A t‖ = 1 := by
  have h2 : ‖purified A t‖ ^ 2 = 1 := by
    rw [norm_sq_eq_sum, Fintype.sum_prod_type, Finset.sum_comm]
    rw [sum_db_some (fun E => ∑ z, ‖purified A t (z, E)‖ ^ 2)]
    · simp only [purified_some, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
        ← Finset.mul_sum]
      have : ∀ f : Fin n → Qubits m, ∑ z, ‖(A.stateAt (xorOracle f) t) z‖ ^ 2 = 1 := by
        intro f; rw [← norm_sq_eq_sum, norm_stateAt]; simp
      simp only [this, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, card_qubits, nsmul_eq_mul]
      rw [sq_abs, ← pow_mul, mul_comm n 2, pow_mul, sc_sq]
      push_cast; rw [← pow_mul, inv_pow, ← pow_mul]; field_simp; simp
    · intro E hE
      apply Finset.sum_eq_zero; intro z _
      rw [purified_not_some A t z E hE]; simp
  have := norm_nonneg (purified A t)
  nlinarith [sq_nonneg (‖purified A t‖ - 1), sq_nonneg (‖purified A t‖ + 1)]

theorem norm_compressedStateAt {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Fin n) (Qubits m) W T) (t : Fin (T + 1)) : ‖compressedStateAt A t‖ = 1 := by
  rw [compressedStateAt_eq, norm_act_of_unitary _ (Kc_ct_mul W), norm_purified]

end CODInfra


-- ===== from Solutions/COD/Gram.lean =====

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

namespace CODInfra
open CompressedOracleDuality.LabelSymmetric

variable {n : ℕ}

lemma dbSize_le_of_agree (D' D : Database n) (x : Input n) (h : ∀ i, i ≠ x → D' i = D i) :
    dbSize D' ≤ dbSize D + 1 := by
  classical
  unfold dbSize dbSupport
  calc (Finset.univ.filter (fun i => D' i ≠ none)).card
      ≤ (insert x (Finset.univ.filter (fun i => D i ≠ none))).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        by_cases hix : i = x
        · simp [hix]
        · simp [Finset.mem_insert, hix, ← h i hix, hi]
    _ ≤ _ := Finset.card_insert_le _ _

/-- the compressed database after `t` queries has at most `t` entries -/
theorem compressedStateAt_support {W : Type} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Input n) (Label n) W T) (t : Fin (T + 1)) (z : Memory n W) (D : Database n)
    (hD : t.val < dbSize D) : compressedStateAt A t (z, D) = 0 := by
  induction t using Fin.induction generalizing z D with
  | zero =>
    simp only [compressedStateAt, Fin.induction_zero]
    rw [act_kron_one_apply]
    apply Finset.sum_eq_zero; intro z' _
    have : D ≠ fun _ => none := by
      rintro rfl; simp [dbSize, dbSupport] at hD
    simp [tensorVec, ket, PiLp.single_apply, this]
  | succ s ih =>
    simp only [compressedStateAt, Fin.induction_succ]
    rw [act_kron_one_apply]
    apply Finset.sum_eq_zero; intro z' _
    rw [act_apply]
    rw [Finset.sum_eq_zero, mul_zero]
    rintro ⟨⟨⟨x, y⟩, w⟩, D0⟩ _
    obtain ⟨⟨x', y'⟩, w'⟩ := z'
    rw [compressedOracle_apply]
    split_ifs with h
    · have h1 := dbSize_le_of_agree D D0 x h.2.2
      have : (s.castSucc : Fin (T+1)).val < dbSize D0 := by
        simp only [Fin.val_succ] at hD; simp only [Fin.val_castSucc]; omega
      have := ih ((x, y), w) _ this
      simp only [compressedStateAt] at this ⊢
      rw [this, mul_zero]
    · simp

lemma sum_compressAll_update {m N : ℕ} (D E : Fin N → Option (Qubits m)) (x : Fin N) :
    ∑ y : Qubits m, compressAll N m (Function.update D x (some y)) E =
      if E x = none then (((2:ℝ)^m * sc m : ℝ) : ℂ) *
        ∏ i ∈ Finset.univ \ {x}, compressionUnitary m (D i) (E i) else 0 := by
  simp only [compressAll_apply]
  have : ∀ y : Qubits m, ∏ i, compressionUnitary m (Function.update D x (some y) i) (E i) =
      compressionUnitary m (some y) (E x) * ∏ i ∈ Finset.univ \ {x}, compressionUnitary m (D i) (E i) := by
    intro y
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
    simp only [Function.update_self]
    congr 1
    rw [Finset.sdiff_singleton_eq_erase]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  simp_rw [this]
  rw [← Finset.sum_mul, sum_C_some_left]
  split_ifs <;> simp

/-- rows of the compressed state are valid -/
theorem compressedStateAt_valid {W : Type} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Input n) (Label n) W T) (t : Fin (T + 1)) (z : Memory n W) (D : Database n)
    (x : Input n) : ∑ y : Label n, compressedStateAt A t (z, Function.update D x (some y)) = 0 := by
  rw [compressedStateAt_eq]
  simp only [Kc, act_one_kron_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro E _
  rw [sum_compressAll_update]
  split_ifs with hE
  · rw [purified_not_some A t z E ⟨x, hE⟩, mul_zero]
  · rw [zero_mul]

end CODInfra

namespace CompressedOracleDuality.LabelSymmetric
open CODInfra

theorem gram_facts_proof {n S T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Input n) (Label n) W T) (t : Fin (T + 1))
    (hn : 6 ≤ n) (hmem : 2 ^ n * 2 ^ n * Fintype.card W ≤ 2 ^ S) :
    (gramAt A t).PosSemidef ∧ (gramAt A t).trace = 1 ∧
    (gramAt A t).rank ≤ 2 ^ S ∧ SupportedAt (gramAt A t) t.val ∧ ValidMatrix (gramAt A t) := by
  refine ⟨Matrix.posSemidef_conjTranspose_mul_self _, ?_, ?_, ?_, ?_⟩
  · -- trace
    have h := norm_compressedStateAt A t
    have h2 : ∑ p, ‖compressedStateAt A t p‖ ^ 2 = 1 := by rw [← norm_sq_eq_sum, h]; simp
    rw [Fintype.sum_prod_type, Finset.sum_comm] at h2
    simp only [gramAt, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      coefficientAt]
    have : ∀ D z, star (compressedStateAt A t (z, D)) * compressedStateAt A t (z, D) =
        ((‖compressedStateAt A t (z, D)‖ ^ 2 : ℝ) : ℂ) := by
      intro D z
      rw [mul_comm]; push_cast; exact Complex.mul_conj' _
    simp_rw [this]
    rw [← Complex.ofReal_one, ← h2]
    push_cast; rfl
  · -- rank
    simp only [gramAt]
    rw [Matrix.rank_conjTranspose_mul_self]
    refine (Matrix.rank_le_card_height _).trans ?_
    simpa [Memory, Input, Label, card_qubits] using hmem
  · -- support
    intro D₁ D₂ h
    simp only [gramAt, Matrix.mul_apply, Matrix.conjTranspose_apply, coefficientAt]
    apply Finset.sum_eq_zero
    intro z _
    rcases h with h | h
    · rw [compressedStateAt_support A t z D₁ h]; simp
    · rw [compressedStateAt_support A t z D₂ h]; simp
  · -- validity
    intro v D x
    simp only [gramAt, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply,
      coefficientAt, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero; intro D' _
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero; intro z _
    simp only [mul_assoc]
    rw [← Finset.sum_mul, ← star_sum, compressedStateAt_valid, star_zero, zero_mul]


end CompressedOracleDuality.LabelSymmetric


-- ===== from Solutions/COD/LabelSym.lean =====

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

namespace CODInfra
open CompressedOracleDuality.LabelSymmetric

variable {n : ℕ}

/-- relabelling as an equivalence of databases -/
def relabelEquiv (σ : Equiv.Perm (Label n)) : Database n ≃ Database n where
  toFun := relabel σ
  invFun := relabel σ⁻¹
  left_inv D := by funext x; simp only [relabel]; cases D x <;> simp
  right_inv D := by funext x; simp only [relabel]; cases D x <;> simp

lemma relabelEquiv_apply (σ : Equiv.Perm (Label n)) (D : Database n) :
    relabelEquiv σ D = relabel σ D := rfl

lemma symm_iff_submatrix (G : DBMatrix n) :
    MatrixLabelSymmetric G ↔ ∀ σ, G.submatrix (relabelEquiv σ) (relabelEquiv σ) = G := by
  constructor
  · intro h σ; ext D₁ D₂; exact h σ D₁ D₂
  · intro h σ D₁ D₂; exact congrFun (congrFun (h σ) D₁) D₂

/-- the PSD square root of a label-symmetric PSD matrix is label-symmetric -/
theorem sqrt_symm (G : DBMatrix n) (hG : G.PosSemidef) (hs : MatrixLabelSymmetric G) :
    MatrixLabelSymmetric (sqrtGram G) := by
  rw [symm_iff_submatrix] at hs ⊢
  intro σ
  set e := relabelEquiv (n := n) σ
  have hS : (0 : DBMatrix n) ≤ CFC.sqrt G := CFC.sqrt_nonneg G
  have hS' : (CFC.sqrt G).PosSemidef := Matrix.nonneg_iff_posSemidef.1 hS
  have h1 : (CFC.sqrt G).submatrix e e * (CFC.sqrt G).submatrix e e = G := by
    rw [Matrix.submatrix_mul_equiv, CFC.sqrt_mul_sqrt_self G (Matrix.nonneg_iff_posSemidef.2 hG), hs σ]
  have h2 : (0 : DBMatrix n) ≤ (CFC.sqrt G).submatrix e e :=
    Matrix.nonneg_iff_posSemidef.2 ((Matrix.posSemidef_submatrix_equiv e).2 hS')
  have := CFC.sqrt_unique h1 h2
  simp only [sqrtGram]
  rw [← this]

lemma C_relabel (σ : Equiv.Perm (Label n)) (a b : Option (Label n)) :
    compressionUnitary n (a.map σ) (b.map σ) = compressionUnitary n a b := by
  cases a <;> cases b <;> simp [C_none_none, C_none_some, C_some_none, C_some_some]

lemma compressAll_relabel (σ : Equiv.Perm (Label n)) (D E : Database n) :
    compressAll (2 ^ n) n (relabel σ D) (relabel σ E) = compressAll (2 ^ n) n D E := by
  simp only [compressAll_apply, relabel, C_relabel]

/-- conjugating by `C^{⊗N}` preserves label symmetry -/
lemma conj_compress_symm (M : DBMatrix n) (hM : MatrixLabelSymmetric M) :
    MatrixLabelSymmetric (fun D₁ D₂ => ∑ E₁, ∑ E₂,
      compressAll (2 ^ n) n D₁ E₁ * compressAll (2 ^ n) n D₂ E₂ * M E₁ E₂) := by
  intro σ D₁ D₂
  simp only
  rw [← Equiv.sum_comp (relabelEquiv σ)]
  apply Finset.sum_congr rfl; intro E₁ _
  rw [← Equiv.sum_comp (relabelEquiv σ)]
  apply Finset.sum_congr rfl; intro E₂ _
  simp only [relabelEquiv_apply, compressAll_relabel, hM σ]

/-- Gram matrix of a joint memory–database vector -/
def gramOf {W : Type} [Fintype W] (u : EuclideanSpace ℂ (Memory n W × Database n)) : DBMatrix n :=
  fun D₁ D₂ => ∑ z, star (u (z, D₁)) * u (z, D₂)

lemma gramOf_act_Kc {W : Type} [Fintype W] [DecidableEq W]
    (u : EuclideanSpace ℂ (Memory n W × Database n)) (D₁ D₂ : Database n) :
    gramOf (act (Kc (2 ^ n) n W) u) D₁ D₂ = ∑ E₁, ∑ E₂,
      compressAll (2 ^ n) n D₁ E₁ * compressAll (2 ^ n) n D₂ E₂ * gramOf u E₁ E₂ := by
  simp only [gramOf, Kc, act_one_kron_apply, star_sum, star_mul', compressAll_star,
    Finset.sum_mul_sum]
  conv_rhs => arg 2; ext E₁; arg 2; ext E₂; rw [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext E₁; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro E₁ _
  apply Finset.sum_congr rfl; intro E₂ _
  apply Finset.sum_congr rfl; intro z _
  ring

lemma gramAt_eq_gramOf {T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Input n) (Label n) W T) (t : Fin (T + 1)) :
    gramAt A t = gramOf (compressedStateAt A t) := by
  ext D₁ D₂; simp [gramAt, gramOf, Matrix.mul_apply, coefficientAt]

lemma relabel_some (σ : Equiv.Perm (Label n)) (H : Input n → Label n) :
    relabel σ (fun i => some (H i)) = fun i => some ((σ ∘ H) i) := by
  funext i; simp [relabel]

lemma relabel_none (σ : Equiv.Perm (Label n)) (E : Database n) (hE : ∃ i, E i = none) :
    ∃ i, relabel σ E i = none := by
  obtain ⟨i, hi⟩ := hE; exact ⟨i, by simp [relabel, hi]⟩

lemma exists_some_of_not_none (E : Database n) (hE : ¬ ∃ i, E i = none) :
    ∃ H : Input n → Label n, E = fun i => some (H i) := by
  push Not at hE
  exact ⟨fun i => (E i).get (Option.isSome_iff_ne_none.mpr (hE i)), by funext i; simp⟩

lemma gramOf_purified_some {T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Input n) (Label n) W T) (t : Fin (T + 1)) (H₁ H₂ : Input n → Label n) :
    gramOf (purified A t) (fun i => some (H₁ i)) (fun i => some (H₂ i)) =
      ((sc n ^ (2 ^ n)) ^ 2 : ℝ) * inner ℂ (A.stateAt (xorOracle H₁) t) (A.stateAt (xorOracle H₂) t) := by
  simp only [gramOf, purified_some, inner_eq_sum, star_mul', Complex.star_def, Complex.conj_ofReal,
    Finset.mul_sum]
  apply Finset.sum_congr rfl; intro z _
  push_cast; ring

lemma gramOf_purified_none {T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Input n) (Label n) W T) (t : Fin (T + 1)) (E₁ E₂ : Database n)
    (h : (∃ i, E₁ i = none) ∨ (∃ i, E₂ i = none)) : gramOf (purified A t) E₁ E₂ = 0 := by
  simp only [gramOf]
  apply Finset.sum_eq_zero; intro z _
  rcases h with h | h
  · rw [purified_not_some A t z E₁ h]; simp
  · rw [purified_not_some A t z E₂ h]; simp

lemma purified_symm_iff {T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Input n) (Label n) W T) (t : Fin (T + 1)) :
    MatrixLabelSymmetric (gramOf (purified A t)) ↔
      ∀ (H₁ H₂ : Input n → Label n) (σ : Equiv.Perm (Label n)),
        inner ℂ (A.stateAt (xorOracle H₁) t) (A.stateAt (xorOracle H₂) t) =
        inner ℂ (A.stateAt (xorOracle (σ ∘ H₁)) t) (A.stateAt (xorOracle (σ ∘ H₂)) t) := by
  have hc : ((sc n ^ (2 ^ n)) ^ 2 : ℝ) ≠ 0 := by have := sc_pos n; positivity
  constructor
  · intro h H₁ H₂ σ
    have := h σ (fun i => some (H₁ i)) (fun i => some (H₂ i))
    rw [relabel_some, relabel_some, gramOf_purified_some, gramOf_purified_some] at this
    have hc' : (((sc n ^ (2 ^ n)) ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
    exact (mul_left_cancel₀ hc' this).symm
  · intro h σ E₁ E₂
    by_cases h1 : ∃ i, E₁ i = none
    · rw [gramOf_purified_none A t _ _ (Or.inl (relabel_none σ E₁ h1)),
        gramOf_purified_none A t _ _ (Or.inl h1)]
    by_cases h2 : ∃ i, E₂ i = none
    · rw [gramOf_purified_none A t _ _ (Or.inr (relabel_none σ E₂ h2)),
        gramOf_purified_none A t _ _ (Or.inr h2)]
    obtain ⟨H₁, rfl⟩ := exists_some_of_not_none E₁ h1
    obtain ⟨H₂, rfl⟩ := exists_some_of_not_none E₂ h2
    rw [relabel_some, relabel_some, gramOf_purified_some, gramOf_purified_some, h H₁ H₂ σ]

end CODInfra

namespace CompressedOracleDuality.LabelSymmetric
open CODInfra

theorem label_symmetry_transfer_proof {n T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Input n) (Label n) W T) :
    (IsLabelSymmetric A ↔ ∀ t : Fin (T + 1), MatrixLabelSymmetric (gramAt A t)) ∧
    (IsLabelSymmetric A → ∀ t : Fin (T + 1), MatrixLabelSymmetric (sqrtGram (gramAt A t))) := by
  have hψ : ∀ t, compressedStateAt A t = act (Kc (2 ^ n) n W) (purified A t) :=
    compressedStateAt_eq A
  have hφ : ∀ t, purified A t = act (Kc (2 ^ n) n W) (compressedStateAt A t) := by
    intro t; rw [hψ, act_act, Kc_mul_Kc, act_one]
  have key : ∀ t, MatrixLabelSymmetric (gramAt A t) ↔ MatrixLabelSymmetric (gramOf (purified A t)) := by
    intro t
    constructor
    · intro h
      have := conj_compress_symm _ h
      have e : gramOf (purified A t) = fun D₁ D₂ => ∑ E₁, ∑ E₂,
          compressAll (2 ^ n) n D₁ E₁ * compressAll (2 ^ n) n D₂ E₂ * gramAt A t E₁ E₂ := by
        ext D₁ D₂; rw [hφ, gramOf_act_Kc, gramAt_eq_gramOf]
      rw [e]; exact this
    · intro h
      have := conj_compress_symm _ h
      have e : gramAt A t = fun D₁ D₂ => ∑ E₁, ∑ E₂,
          compressAll (2 ^ n) n D₁ E₁ * compressAll (2 ^ n) n D₂ E₂ * gramOf (purified A t) E₁ E₂ := by
        ext D₁ D₂; rw [gramAt_eq_gramOf, hψ, gramOf_act_Kc]
      rw [e]; exact this
  have part1 : IsLabelSymmetric A ↔ ∀ t : Fin (T + 1), MatrixLabelSymmetric (gramAt A t) := by
    simp only [key, purified_symm_iff, IsLabelSymmetric]
  refine ⟨part1, ?_⟩
  intro h t
  exact sqrt_symm _ (Matrix.posSemidef_conjTranspose_mul_self _) (part1.1 h t)

end CompressedOracleDuality.LabelSymmetric


end

open QAlgorithms CompressedOracleDuality.LabelSymmetric
open scoped BigOperators MatrixOrder ComplexOrder

theorem solution {n T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Input n) (Label n) W T) :
    (IsLabelSymmetric A ↔ ∀ t : Fin (T + 1), MatrixLabelSymmetric (gramAt A t)) ∧
    (IsLabelSymmetric A → ∀ t : Fin (T + 1), MatrixLabelSymmetric (sqrtGram (gramAt A t))) :=
  CompressedOracleDuality.LabelSymmetric.label_symmetry_transfer_proof A
