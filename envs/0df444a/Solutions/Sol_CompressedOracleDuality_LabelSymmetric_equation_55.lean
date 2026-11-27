-- Prove2me | solution 1 for CompressedOracleDuality.LabelSymmetric.equation_55
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:23:28.667794+00:00
-- url     : https://prove2.me/submissions/532f3489-38b8-4103-a57c-25e19e078119

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


-- ===== from Solutions/COD/Cells.lean =====

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

namespace CODInfra

variable {N m : ℕ}

/-- cellwise tensor product of single-cell matrices -/
def tens (M : Fin N → Matrix (Option (Qubits m)) (Option (Qubits m)) ℂ) :
    Matrix (Fin N → Option (Qubits m)) (Fin N → Option (Qubits m)) ℂ :=
  fun D E => ∏ i, M i (D i) (E i)

lemma tens_mul (M M' : Fin N → Matrix (Option (Qubits m)) (Option (Qubits m)) ℂ) :
    tens M * tens M' = tens (fun i => M i * M' i) := by
  ext D F
  simp only [tens, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  rw [sum_prod_cells (fun i e => M i (D i) e * M' i e (F i))]

lemma tens_one : tens (fun _ => (1 : Matrix (Option (Qubits m)) (Option (Qubits m)) ℂ)) =
    (1 : Matrix (Fin N → Option (Qubits m)) (Fin N → Option (Qubits m)) ℂ) := by
  ext D F
  simp only [tens, Matrix.one_apply]
  by_cases h : D = F
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, D i ≠ F i := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- compression on the cells of `S`, identity elsewhere -/
def partC (S : Finset (Fin N)) : Matrix (Fin N → Option (Qubits m)) (Fin N → Option (Qubits m)) ℂ :=
  tens (fun i => if i ∈ S then compressionUnitary m else 1)

lemma partC_univ : partC (Finset.univ : Finset (Fin N)) = compressAll N m := by
  ext D E; simp [partC, tens, compressAll_apply]

lemma partC_mul_self (S : Finset (Fin N)) : partC (m := m) S * partC S = 1 := by
  rw [partC, tens_mul, ← tens_one]
  congr 1; funext i
  split_ifs <;> simp [C_mul_C]

lemma partC_conjTranspose (S : Finset (Fin N)) : (partC (m := m) S).conjTranspose = partC S := by
  ext D E
  simp only [Matrix.conjTranspose_apply, partC, tens, star_prod]
  apply Finset.prod_congr rfl; intro i _
  split_ifs
  · rw [C_star, C_symm]
  · simp only [Matrix.one_apply]; split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

lemma partC_ct_mul (S : Finset (Fin N)) : (partC (m := m) S).conjTranspose * partC S = 1 := by
  rw [partC_conjTranspose, partC_mul_self]

lemma partC_apply_ne {S : Finset (Fin N)} {x : Fin N} (hx : x ∉ S)
    (D E : Fin N → Option (Qubits m)) (h : D x ≠ E x) : partC S D E = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ x)
  simp [hx, Matrix.one_apply, h]

/-- the update bijection: databases ≃ (database with `⊥` at `x`) × (value at `x`). -/
lemma sum_update_split {M : Type*} [AddCommMonoid M] (x : Fin N)
    (F : (Fin N → Option (Qubits m)) → M) :
    ∑ E, F E = ∑ E, if E x = none then ∑ a, F (Function.update E x a) else 0 := by
  classical
  rw [← Finset.sum_filter]
  rw [← Finset.sum_product']
  symm
  apply Finset.sum_nbij' (fun p => Function.update p.1 x p.2)
    (fun D => (Function.update D x none, D x))
  · intro p _; simp
  · intro D _; simp
  · rintro ⟨E, a⟩ hp
    have hp' : E x = none := by simpa using hp
    simp only [Function.update_idem, Function.update_self, Prod.mk.injEq, and_true]
    funext i; by_cases hi : i = x
    · subst hi; simp [hp']
    · simp [Function.update_of_ne hi]
  · intro D _; simp
  · intro p _; rfl

/-- peeling one compressed cell off -/
lemma partC_peel {S : Finset (Fin N)} {x : Fin N} (hx : x ∈ S) (D E : Fin N → Option (Qubits m)) :
    partC S D E = compressionUnitary m (D x) (E x) *
      partC (S.erase x) (Function.update D x (E x)) E := by
  simp only [partC, tens]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x),
    ← Finset.mul_prod_erase Finset.univ (fun i => (if i ∈ S.erase x then compressionUnitary m else 1)
      (Function.update D x (E x) i) (E i)) (Finset.mem_univ x)]
  simp only [hx, if_true, Finset.mem_erase, ne_eq, not_true_eq_false, false_and, if_false,
    Function.update_self, Matrix.one_apply_eq, one_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hix := Finset.ne_of_mem_erase hi
  simp [hix, Function.update_of_ne hix]

lemma partC_vec_peel {S : Finset (Fin N)} {x : Fin N} (hx : x ∈ S) (v : EuclideanSpace ℂ (Fin N → Option (Qubits m)))
    (D : Fin N → Option (Qubits m)) :
    act (partC S) v D = ∑ a, compressionUnitary m (D x) a *
      act (partC (S.erase x)) v (Function.update D x a) := by
  simp only [act_apply]
  simp_rw [partC_peel hx D, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro E _
  rw [Finset.sum_eq_single (E x)]
  · ring
  · intro a _ ha
    rw [partC_apply_ne (Finset.notMem_erase x S) _ _ (by simpa using ha)]; simp
  · simp

lemma partC_update_notmem {S : Finset (Fin N)} {x : Fin N} (hx : x ∉ S)
    (D F : Fin N → Option (Qubits m)) (a b : Option (Qubits m)) :
    partC S (Function.update D x a) (Function.update F x b) =
      if a = b then partC S (Function.update D x none) (Function.update F x none) else 0 := by
  simp only [partC, tens]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x),
    ← Finset.mul_prod_erase Finset.univ (fun i => (if i ∈ S then compressionUnitary m else 1)
      (Function.update D x none i) (Function.update F x none i)) (Finset.mem_univ x)]
  simp only [hx, if_false, Function.update_self, Matrix.one_apply, if_true, one_mul]
  have : ∏ i ∈ Finset.univ.erase x, (if i ∈ S then compressionUnitary m else 1)
      (Function.update D x a i) (Function.update F x b i) =
      ∏ i ∈ Finset.univ.erase x, (if i ∈ S then compressionUnitary m else 1)
      (Function.update D x none i) (Function.update F x none i) := by
    apply Finset.prod_congr rfl; intro i hi
    have hix := Finset.ne_of_mem_erase hi
    simp [Function.update_of_ne hix]
  rw [this]; split_ifs <;> simp

/-- a cell outside `S` stays valid under `partC S` -/
lemma partC_valid_notmem {S : Finset (Fin N)} {x : Fin N} (hx : x ∉ S)
    (v : EuclideanSpace ℂ (Fin N → Option (Qubits m)))
    (hv : ∀ E, ∑ u, v (Function.update E x (some u)) = 0) (D : Fin N → Option (Qubits m)) :
    ∑ u, act (partC S) v (Function.update D x (some u)) = 0 := by
  have key : ∀ a, act (partC S) v (Function.update D x a) = ∑ F, if F x = none then
      partC S (Function.update D x none) F * v (Function.update F x a) else 0 := by
    intro a
    rw [act_apply, sum_update_split x]
    apply Finset.sum_congr rfl; intro F _
    split_ifs with hF
    · rw [Finset.sum_eq_single a]
      · rw [partC_update_notmem hx D F a a, if_pos rfl]
        congr 2
        conv_rhs => rw [← Function.update_eq_self x F, hF]
      · intro b _ hb; rw [partC_update_notmem hx D F a b, if_neg (Ne.symm hb)]; simp
      · simp
    · rfl
  simp_rw [key]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero; intro F _
  split_ifs
  · rw [← Finset.mul_sum, hv, mul_zero]
  · simp

/-- `partC S` commutes with conditioning on the content of a cell outside `S` -/
lemma partC_cond_notmem {S : Finset (Fin N)} {x : Fin N} (hx : x ∉ S)
    (p : Option (Qubits m) → Prop) [DecidablePred p]
    (v : EuclideanSpace ℂ (Fin N → Option (Qubits m))) (D : Fin N → Option (Qubits m)) :
    act (partC S) (WithLp.toLp 2 fun E => if p (E x) then v E else 0) D =
      if p (D x) then act (partC S) v D else 0 := by
  simp only [act_apply, WithLp.ofLp_toLp]
  split_ifs with hD
  · apply Finset.sum_congr rfl; intro E _
    by_cases hE : D x = E x
    · rw [← hE, if_pos hD]
    · rw [partC_apply_ne hx D E hE]; simp
  · apply Finset.sum_eq_zero; intro E _
    by_cases hE : D x = E x
    · rw [← hE, if_neg hD, mul_zero]
    · rw [partC_apply_ne hx D E hE]; simp

/-- the key single-cell identity: on a cell holding `some y`, compression only adds a multiple of
the `⊥`-entry (validity kills the uniform part). -/
lemma partC_peel_some {S : Finset (Fin N)} {x : Fin N} (hx : x ∈ S)
    (v : EuclideanSpace ℂ (Fin N → Option (Qubits m)))
    (hv : ∀ E, ∑ u, v (Function.update E x (some u)) = 0) (D : Fin N → Option (Qubits m))
    (y : Qubits m) (hD : D x = some y) :
    act (partC S) v D = act (partC (S.erase x)) v D +
      (sc m : ℂ) * act (partC (S.erase x)) v (Function.update D x none) := by
  rw [partC_vec_peel hx, Fintype.sum_option, hD, C_some_none]
  have hval := partC_valid_notmem (Finset.notMem_erase x S) v hv D
  simp only [C_some_some, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.mul_sum, hval, mul_zero, sub_zero]
  rw [← hD, Function.update_eq_self]; ring

end CODInfra


-- ===== from Solutions/COD/TwoCell.lean =====

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

namespace CODInfra

variable {N m : ℕ}

/-- restriction of a vector to a predicate -/
def restr (P : (Fin N → Option (Qubits m)) → Prop) [DecidablePred P]
    (v : EuclideanSpace ℂ (Fin N → Option (Qubits m))) : EuclideanSpace ℂ (Fin N → Option (Qubits m)) :=
  WithLp.toLp 2 fun D => if P D then v D else 0

lemma norm_sq_restr (P : (Fin N → Option (Qubits m)) → Prop) [DecidablePred P]
    (v : EuclideanSpace ℂ (Fin N → Option (Qubits m))) :
    ‖restr P v‖ ^ 2 = ∑ D, if P D then ‖v D‖ ^ 2 else 0 := by
  rw [norm_sq_eq_sum]; apply Finset.sum_congr rfl; intro D _
  simp only [restr, WithLp.ofLp_toLp]; split_ifs <;> simp

lemma norm_le_of_sq_le {ι : Type*} [Fintype ι] (v w : EuclideanSpace ℂ ι)
    (h : ∑ i, ‖v i‖ ^ 2 ≤ ∑ i, ‖w i‖ ^ 2) : ‖v‖ ≤ ‖w‖ := by
  rw [← norm_sq_eq_sum, ← norm_sq_eq_sum] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 h

/-- partial compression on cells outside the conditioned ones preserves the norm of a restriction -/
lemma norm_partC_restr_cell {S : Finset (Fin N)} {x : Fin N} (hx : x ∉ S)
    (p : Option (Qubits m) → Prop) [DecidablePred p]
    (v : EuclideanSpace ℂ (Fin N → Option (Qubits m))) :
    ‖restr (fun D => p (D x)) (act (partC S) v)‖ = ‖restr (fun D => p (D x)) v‖ := by
  have : restr (fun D => p (D x)) (act (partC S) v) =
      act (partC S) (restr (fun D => p (D x)) v) := by
    ext D
    simp only [restr, WithLp.ofLp_toLp]
    rw [partC_cond_notmem hx p v D]
  rw [this, norm_act_of_unitary _ (partC_ct_mul S)]

/-- sum over databases with a prescribed cell, re-indexed at `⊥` -/
lemma sum_cell_some_shift (x : Fin N) (y : Qubits m) (Q : (Fin N → Option (Qubits m)) → Prop)
    [DecidablePred Q] (g : (Fin N → Option (Qubits m)) → ℝ)
    (hQ : ∀ D, Q D ↔ Q (Function.update D x none)) :
    ∑ D, (if D x = some y ∧ Q D then g (Function.update D x none) else 0) =
      ∑ E, (if E x = none ∧ Q E then g E else 0) := by
  rw [sum_update_split x]
  apply Finset.sum_congr rfl; intro E _
  by_cases hE : E x = none
  · rw [if_pos hE, Finset.sum_eq_single (some y)]
    · have h1 : Function.update (Function.update E x (some y)) x none = E := by
        rw [Function.update_idem, ← hE, Function.update_eq_self]
      simp only [Function.update_self, true_and, h1]
      have h2 : Q (Function.update E x (some y)) ↔ Q E := by rw [hQ, h1]
      by_cases hq : Q E
      · rw [if_pos (h2.2 hq), if_pos ⟨hE, hq⟩]
      · rw [if_neg (fun h => hq (h2.1 h)), if_neg (fun h => hq h.2)]
    · intro b _ hb; simp [hb]
    · simp
  · simp [hE]

lemma partC_apply_ne' {S : Finset (Fin N)} (D E : Fin N → Option (Qubits m))
    (h : ¬ ∀ i, i ∉ S → D i = E i) : partC S D E = 0 := by
  push Not at h
  obtain ⟨i, hi, hne⟩ := h
  exact partC_apply_ne hi D E hne

lemma partC_restr_comm {S : Finset (Fin N)} (P : (Fin N → Option (Qubits m)) → Prop)
    [DecidablePred P] (hP : ∀ D E, (∀ i, i ∉ S → D i = E i) → (P D ↔ P E))
    (v : EuclideanSpace ℂ (Fin N → Option (Qubits m))) :
    restr P (act (partC S) v) = act (partC S) (restr P v) := by
  ext D
  simp only [restr, WithLp.ofLp_toLp, act_apply]
  split_ifs with hD
  · apply Finset.sum_congr rfl; intro E _
    by_cases hDE : ∀ i, i ∉ S → D i = E i
    · rw [if_pos ((hP D E hDE).1 hD)]
    · rw [partC_apply_ne' D E hDE]; simp
  · symm; apply Finset.sum_eq_zero; intro E _
    by_cases hDE : ∀ i, i ∉ S → D i = E i
    · rw [if_neg (fun h => hD ((hP D E hDE).2 h)), mul_zero]
    · rw [partC_apply_ne' D E hDE]; simp

lemma norm_partC_restr {S : Finset (Fin N)} (P : (Fin N → Option (Qubits m)) → Prop)
    [DecidablePred P] (hP : ∀ D E, (∀ i, i ∉ S → D i = E i) → (P D ↔ P E))
    (v : EuclideanSpace ℂ (Fin N → Option (Qubits m))) :
    ‖restr P (act (partC S) v)‖ = ‖restr P v‖ := by
  rw [partC_restr_comm P hP, norm_act_of_unitary _ (partC_ct_mul S)]

/-- **Two-cell compression bound** (the `ℓ = 2` case of Zhandry's Lemma 5 on a valid vector). -/
theorem two_cell_bound (v : EuclideanSpace ℂ (Fin N → Option (Qubits m))) {x₁ x₂ : Fin N}
    (hx : x₁ ≠ x₂) (y : Qubits m)
    (hv1 : ∀ E, ∑ u, v (Function.update E x₁ (some u)) = 0)
    (hv2 : ∀ E, ∑ u, v (Function.update E x₂ (some u)) = 0) :
    ‖restr (fun D => D x₁ = some y ∧ D x₂ = some y) (act (compressAll N m) v)‖ ≤
      ‖restr (fun D => D x₁ = some y ∧ D x₂ = some y) v‖ + Real.sqrt 2 * sc m * ‖v‖ := by
  set S1 : Finset (Fin N) := Finset.univ.erase x₁ with hS1
  set S2 : Finset (Fin N) := S1.erase x₂ with hS2
  have hx1S1 : x₁ ∉ S1 := Finset.notMem_erase _ _
  have hx2S1 : x₂ ∈ S1 := Finset.mem_erase.2 ⟨Ne.symm hx, Finset.mem_univ _⟩
  have hx2S2 : x₂ ∉ S2 := Finset.notMem_erase _ _
  have hx1S2 : x₁ ∉ S2 := fun h => hx1S1 (Finset.mem_of_mem_erase h)
  set w1 := act (partC (m := m) S1) v
  set w2 := act (partC (m := m) S2) v
  set P : (Fin N → Option (Qubits m)) → Prop := fun D => D x₁ = some y ∧ D x₂ = some y
  set X : EuclideanSpace ℂ (Fin N → Option (Qubits m)) :=
    WithLp.toLp 2 fun D => if P D then w2 (Function.update D x₂ none) else 0
  set Y : EuclideanSpace ℂ (Fin N → Option (Qubits m)) :=
    WithLp.toLp 2 fun D => if P D then w1 (Function.update D x₁ none) else 0
  have hdecomp : restr P (act (compressAll N m) v) = restr P w2 + (sc m : ℂ) • X + (sc m : ℂ) • Y := by
    ext D
    simp only [restr, X, Y, WithLp.ofLp_toLp, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    split_ifs with hD
    · rw [← partC_univ]
      rw [partC_peel_some (Finset.mem_univ x₁) v hv1 D y hD.1]
      rw [partC_peel_some hx2S1 v hv2 D y hD.2]
    · simp only [mul_zero, add_zero]
  -- norms of the pieces
  have hX : ‖X‖ = ‖restr (fun D => D x₂ = none ∧ D x₁ = some y) v‖ := by
    rw [← norm_partC_restr (S := S2) _ (fun D E h => by rw [h x₂ hx2S2, h x₁ hx1S2]) v]
    have h1 : ‖X‖ ^ 2 = ‖restr (fun D => D x₂ = none ∧ D x₁ = some y) w2‖ ^ 2 := by
      rw [norm_sq_restr, norm_sq_eq_sum]
      have : ∀ D, ‖X D‖ ^ 2 = if D x₂ = some y ∧ D x₁ = some y then
          ‖w2 (Function.update D x₂ none)‖ ^ 2 else 0 := by
        intro D; simp only [X, P, WithLp.ofLp_toLp]
        by_cases h : D x₂ = some y ∧ D x₁ = some y
        · rw [if_pos ⟨h.2, h.1⟩, if_pos h]
        · rw [if_neg (fun h' => h ⟨h'.2, h'.1⟩), if_neg h]; simp
      simp_rw [this]
      exact sum_cell_some_shift x₂ y (fun D => D x₁ = some y) (fun E => ‖w2 E‖ ^ 2)
        (fun D => by rw [Function.update_of_ne hx])
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 h1
  have hY : ‖Y‖ ≤ ‖restr (fun D => D x₁ = none) v‖ := by
    rw [← norm_partC_restr (S := S1) _ (fun D E h => by rw [h x₁ hx1S1]) v]
    have h1 : ‖Y‖ ^ 2 ≤ ‖restr (fun D => D x₁ = none) w1‖ ^ 2 := by
      rw [norm_sq_restr, norm_sq_eq_sum]
      have : ∀ D, ‖Y D‖ ^ 2 = if D x₁ = some y ∧ D x₂ = some y then
          ‖w1 (Function.update D x₁ none)‖ ^ 2 else 0 := by
        intro D; simp only [Y, P, WithLp.ofLp_toLp]
        split_ifs <;> simp
      simp_rw [this]
      rw [sum_cell_some_shift x₁ y (fun D => D x₂ = some y) (fun E => ‖w1 E‖ ^ 2)
        (fun D => by rw [Function.update_of_ne (Ne.symm hx)])]
      apply Finset.sum_le_sum; intro E _
      split_ifs <;> simp_all
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 h1
  have hP2 : ‖restr P w2‖ = ‖restr P v‖ :=
    norm_partC_restr (S := S2) _ (fun D E h => by simp only [P]; rw [h x₁ hx1S2, h x₂ hx2S2]) v
  -- orthogonality of the two error pieces
  have horth : ‖restr (fun D => D x₂ = none ∧ D x₁ = some y) v‖ ^ 2 +
      ‖restr (fun D => D x₁ = none) v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [norm_sq_restr, norm_sq_restr, norm_sq_eq_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro D _
    by_cases h1 : D x₁ = none
    · have : ¬ (D x₂ = none ∧ D x₁ = some y) := fun h => by rw [h1] at h; simp at h
      simp [h1, this]
    · simp only [h1, if_false, add_zero]; split_ifs <;> simp
  set a := ‖restr (fun D => D x₂ = none ∧ D x₁ = some y) v‖
  set b := ‖restr (fun D => D x₁ = none) v‖
  have hab : a + b ≤ Real.sqrt 2 * ‖v‖ := by
    have ha := norm_nonneg (restr (fun D => D x₂ = none ∧ D x₁ = some y) v)
    have hb := norm_nonneg (restr (fun D => D x₁ = none) v)
    rw [← Real.sqrt_sq (add_nonneg ha hb), ← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (a - b)]
  have hsc := sc_pos m
  calc ‖restr P (act (compressAll N m) v)‖
      ≤ ‖restr P w2‖ + ‖(sc m : ℂ) • X‖ + ‖(sc m : ℂ) • Y‖ := by
        rw [hdecomp]; exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _) |>.trans
          (by rw [add_assoc])
    _ = ‖restr P v‖ + sc m * a + sc m * ‖Y‖ := by
        rw [hP2, norm_smul, norm_smul, hX, Complex.norm_real, Real.norm_of_nonneg hsc.le]
    _ ≤ ‖restr P v‖ + sc m * a + sc m * b := by gcongr
    _ = ‖restr P v‖ + sc m * (a + b) := by ring
    _ ≤ ‖restr P v‖ + sc m * (Real.sqrt 2 * ‖v‖) := by gcongr
    _ = _ := by ring

end CODInfra


-- ===== from Solutions/COD/Eq55.lean =====

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

namespace CODInfra
open CompressedOracleDuality.LabelSymmetric

variable {n : ℕ}

lemma prob_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) (z : ι) :
    prob ψ z = ‖ψ z‖ ^ 2 := by
  simp [prob, ket, EuclideanSpace.inner_single_left]

/-- the success predicate on a compressed database -/
def succPred (o : CollisionOutput n) (E : Database n) : Prop :=
  match o with
  | none => False
  | some (x₁, x₂, y) => x₁ < x₂ ∧ E x₁ = some y ∧ E x₂ = some y

lemma successful_iff (H : Input n → Label n) (o : CollisionOutput n) :
    Successful H o ↔ succPred o (fun i => some (H i)) := by
  rcases o with _ | ⟨x₁, x₂, y⟩
  · simp [Successful, succPred]
  · simp [Successful, succPred]

lemma card_oracles (n : ℕ) : (Fintype.card (Input n → Label n) : ℝ)⁻¹ = (sc n ^ (2 ^ n)) ^ 2 := by
  have hc : Fintype.card (Input n → Label n) = (2 ^ n) ^ (2 ^ n) := by
    rw [Fintype.card_fun, card_qubits]; simp [Input]
  rw [hc]
  have : (sc n ^ (2 ^ n)) ^ 2 = (sc n ^ 2) ^ (2 ^ n) := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [this, sc_sq, inv_pow]; push_cast; rfl

lemma collisionSuccess_eq {W : Type} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Input n) (Label n) W T) (out : Memory n W → CollisionOutput n) :
    collisionSuccess A out = ∑ z, ∑ E, (open Classical in
      if succPred (out z) E then ‖purified A (Fin.last T) (z, E)‖ ^ 2 else 0) := by
  classical
  unfold collisionSuccess
  rw [card_oracles, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [sum_db_some (fun E => ∑ z, if succPred (out z) E then ‖purified A (Fin.last T) (z, E)‖ ^ 2 else 0)]
  · apply Finset.sum_congr rfl; intro H _
    rw [probEvent, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro z _
    simp only [successful_iff, prob_eq]
    split_ifs
    · rw [purified_some, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]; rfl
    · simp
  · intro E hE
    apply Finset.sum_eq_zero; intro z _
    rw [purified_not_some A _ z E hE]; simp

lemma succPred_not_cf (o : CollisionOutput n) (E : Database n) (h : succPred o E) :
    ¬ CollisionFree E := by
  rcases o with _ | ⟨x₁, x₂, y⟩
  · exact h.elim
  · obtain ⟨hlt, h1, h2⟩ := h
    intro hcf
    exact (ne_of_lt hlt) (hcf x₁ x₂ y h1 h2)

lemma sqrt2_sc (n : ℕ) : Real.sqrt 2 * sc n = Real.sqrt (2 / (2:ℝ) ^ n) := by
  have h1 : sc n = Real.sqrt ((2:ℝ) ^ n)⁻¹ := by
    rw [← sc_sq, Real.sqrt_sq (sc_pos n).le]
  rw [h1, ← Real.sqrt_mul (by norm_num), div_eq_mul_inv]

lemma minkowski_ptwise {ι : Type*} [Fintype ι] (a b c : ι → ℝ) (k : ℝ) (hk : 0 ≤ k)
    (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i + k * c i) :
    Real.sqrt (∑ i, a i ^ 2) ≤ Real.sqrt (∑ i, b i ^ 2) + k * Real.sqrt (∑ i, c i ^ 2) := by
  let va : EuclideanSpace ℝ ι := WithLp.toLp 2 a
  let vb : EuclideanSpace ℝ ι := WithLp.toLp 2 b
  let vc : EuclideanSpace ℝ ι := WithLp.toLp 2 c
  have hn : ∀ v : EuclideanSpace ℝ ι, ‖v‖ = Real.sqrt (∑ i, v i ^ 2) := by
    intro v; rw [EuclideanSpace.norm_eq]; simp [Real.norm_eq_abs, sq_abs]
  have h1 : ‖va‖ ≤ ‖vb + k • vc‖ := by
    rw [hn, hn]; apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum; intro i _
    simp only [va, vb, vc, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_toLp]
    exact pow_le_pow_left₀ (ha i) (hab i) 2
  have h2 := norm_add_le vb (k • vc)
  rw [norm_smul, Real.norm_of_nonneg hk] at h2
  have := h1.trans h2
  rw [hn va, hn vb, hn vc] at this
  simpa [va, vb, vc] using this

end CODInfra

namespace CompressedOracleDuality.LabelSymmetric
open CODInfra

theorem equation_55_proof {n T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Input n) (Label n) W T) (out : Memory n W → CollisionOutput n)
    (hn : 6 ≤ n) :
    collisionSuccess A out ≤ (progressAt A (Fin.last T) + Real.sqrt (2 / (2 : ℝ) ^ n)) ^ 2 := by
  classical
  set ψ := compressedStateAt A (Fin.last T) with hψ
  set φ := purified A (Fin.last T) with hφ
  have hφψ : φ = act (Kc (2 ^ n) n W) ψ := by
    rw [hψ, compressedStateAt_eq, act_act, Kc_mul_Kc, act_one]
  let ψz : Memory n W → EuclideanSpace ℂ (Database n) := fun z => WithLp.toLp 2 fun E => ψ (z, E)
  have hφz : ∀ z E, φ (z, E) = act (compressAll (2 ^ n) n) (ψz z) E := by
    intro z E; rw [hφψ, act_one_kron_apply]; rfl
  let a : Memory n W → ℝ := fun z => ‖restr (succPred (out z)) (act (compressAll (2 ^ n) n) (ψz z))‖
  let b : Memory n W → ℝ := fun z => ‖restr (succPred (out z)) (ψz z)‖
  let c : Memory n W → ℝ := fun z => ‖ψz z‖
  have hp : collisionSuccess A out = ∑ z, a z ^ 2 := by
    rw [collisionSuccess_eq]; apply Finset.sum_congr rfl; intro z _
    simp only [a]; rw [norm_sq_restr]
    apply Finset.sum_congr rfl; intro E _
    rw [hφz]
  have hab : ∀ z, a z ≤ b z + Real.sqrt 2 * sc n * c z := by
    intro z
    simp only [a, b, c]
    rcases ho : out z with _ | ⟨x₁, x₂, y⟩
    · have : ∀ v : EuclideanSpace ℂ (Database n), restr (succPred (none : CollisionOutput n)) v = 0 := by
        intro v; ext E; simp [restr, succPred]
      rw [this, this, norm_zero]; have := sc_pos n; positivity
    · by_cases hlt : x₁ < x₂
      · have heq : ∀ v : EuclideanSpace ℂ (Database n), restr (succPred (some (x₁, x₂, y))) v =
            restr (fun D => D x₁ = some y ∧ D x₂ = some y) v := by
          intro v; ext E; simp [restr, succPred, hlt]
        rw [heq, heq]
        exact two_cell_bound (ψz z) (ne_of_lt hlt) y
          (fun E => compressedStateAt_valid A _ z E x₁) (fun E => compressedStateAt_valid A _ z E x₂)
      · have : ∀ v : EuclideanSpace ℂ (Database n), restr (succPred (some (x₁, x₂, y))) v = 0 := by
          intro v; ext E; simp [restr, succPred, hlt]
        rw [this, this, norm_zero]; have := sc_pos n; positivity
  have hb : Real.sqrt (∑ z, b z ^ 2) ≤ progressAt A (Fin.last T) := by
    have h2 : ∑ z, b z ^ 2 ≤ progressAt A (Fin.last T) ^ 2 := by
      simp only [progressAt, b]
      rw [norm_sq_eq_sum]
      conv_rhs => rw [Fintype.sum_prod_type (f := fun p => ‖(projectDatabase true
        (compressedStateAt A (Fin.last T))).ofLp p‖ ^ 2)]
      apply Finset.sum_le_sum; intro z _
      rw [norm_sq_restr]
      apply Finset.sum_le_sum; intro E _
      simp only [projectDatabase, WithLp.ofLp_toLp, if_true]
      split_ifs with h1 h2 h2
      · exact absurd h2 (succPred_not_cf _ _ h1)
      · rfl
      · simp
      · exact sq_nonneg _
    calc Real.sqrt (∑ z, b z ^ 2) ≤ Real.sqrt (progressAt A (Fin.last T) ^ 2) := Real.sqrt_le_sqrt h2
      _ = _ := Real.sqrt_sq (norm_nonneg _)
  have hc : Real.sqrt (∑ z, c z ^ 2) = 1 := by
    have : ∑ z, c z ^ 2 = 1 := by
      simp only [c]
      have h := norm_compressedStateAt A (Fin.last T)
      have h2 : ‖ψ‖ ^ 2 = 1 := by rw [h]; norm_num
      rw [norm_sq_eq_sum, Fintype.sum_prod_type] at h2
      rw [← h2]; apply Finset.sum_congr rfl; intro z _
      rw [norm_sq_eq_sum]
    rw [this, Real.sqrt_one]
  have hmk := minkowski_ptwise a b c (Real.sqrt 2 * sc n) (by have := sc_pos n; positivity)
    (fun z => norm_nonneg _) hab
  rw [hc, mul_one, sqrt2_sc] at hmk
  rw [hp]
  have hsum : 0 ≤ ∑ z, a z ^ 2 := Finset.sum_nonneg (fun z _ => sq_nonneg _)
  calc ∑ z, a z ^ 2 = Real.sqrt (∑ z, a z ^ 2) ^ 2 := (Real.sq_sqrt hsum).symm
    _ ≤ _ := by
      apply pow_le_pow_left₀ (Real.sqrt_nonneg _)
      linarith

end CompressedOracleDuality.LabelSymmetric


end

open QAlgorithms CompressedOracleDuality.LabelSymmetric
open scoped BigOperators MatrixOrder ComplexOrder

theorem solution {n T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Input n) (Label n) W T) (out : Memory n W → CollisionOutput n)
    (hn : 6 ≤ n) :
    collisionSuccess A out ≤ (progressAt A (Fin.last T) + Real.sqrt (2 / (2 : ℝ) ^ n)) ^ 2 :=
  CompressedOracleDuality.LabelSymmetric.equation_55_proof A out hn
