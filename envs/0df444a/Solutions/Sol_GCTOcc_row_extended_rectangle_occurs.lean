-- Prove2me | solution 1 for GCTOcc.row_extended_rectangle_occurs
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T03:58:14.278478+00:00
-- url     : https://prove2.me/submissions/a70d8f84-17db-4976-aa2a-ce683b18b655

import Mathlib
import Definitions.Def_GCTOcc_occurrence

set_option autoImplicit false

open MvPolynomial Filter Topology

/-! G1 (Kadish–Landsberg, m ≥ 1) for a586c963 GCTOcc.no_occurrence_obstructions. -/

/-- The variables of the `n × n` block. -/
def klBlock (n : ℕ) : Set (ℕ × ℕ) := {v | v.1 < n ∧ v.2 < n}

theorem kl_substLin_X_block (n : ℕ) (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (a b : Fin n) :
    GCTOcc.substLin n g (X ((a : ℕ), (b : ℕ))) =
      ∑ w : Fin n × Fin n, C (g (a, b) w) * X (((w.1 : ℕ)), ((w.2 : ℕ))) := by
  simp [GCTOcc.substLin, a.isLt, b.isLt]

/-- Right action: `substLin h ∘ substLin g = substLin (g * h)`. -/
theorem kl_substLin_mul (n : ℕ) (g h : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (p : GCTOcc.PolyR) :
    GCTOcc.substLin n h (GCTOcc.substLin n g p) = GCTOcc.substLin n (g * h) p := by
  unfold GCTOcc.substLin
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 1
  apply MvPolynomial.algHom_ext
  intro v
  simp only [aeval_X]
  by_cases hv : v.1 < n ∧ v.2 < n
  · simp only [dif_pos hv, map_sum, map_mul, aeval_C, algebraMap_eq, aeval_X]
    simp only [Fin.is_lt, and_self, dif_pos, Fin.eta, Matrix.mul_apply, map_sum, Finset.sum_mul,
      Finset.mul_sum, C_mul, mul_assoc]
    rw [Finset.sum_comm]
  · simp [dif_neg hv]

theorem kl_substLin_mem_supported (n : ℕ) (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (p : GCTOcc.PolyR) (hp : p ∈ supported ℂ (klBlock n)) :
    GCTOcc.substLin n g p ∈ supported ℂ (klBlock n) := by
  rw [supported_eq_adjoin_X] at hp
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    simp only [GCTOcc.substLin, aeval_X, dif_pos (show v.1 < n ∧ v.2 < n from hv)]
    refine Subalgebra.sum_mem _ (fun w _ => Subalgebra.mul_mem _ ?_ ?_)
    · exact Subalgebra.algebraMap_mem _ _
    · exact X_mem_supported.2 (show ((w.1 : ℕ) < n ∧ (w.2 : ℕ) < n) from ⟨w.1.isLt, w.2.isLt⟩)
  | algebraMap r =>
    simp only [GCTOcc.substLin, AlgHom.commutes]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    simp only [GCTOcc.substLin, map_add] at hx hy ⊢
    exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    simp only [GCTOcc.substLin, map_mul] at hx hy ⊢
    exact Subalgebra.mul_mem _ hx hy

theorem kl_isForm_iff (n : ℕ) (p : GCTOcc.PolyR) :
    GCTOcc.IsForm n p ↔ p.IsHomogeneous n ∧ p ∈ supported ℂ (klBlock n) := by
  unfold GCTOcc.IsForm
  rw [mem_supported]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun v hv => ?_⟩
    obtain ⟨c, hc, hvc⟩ := (mem_vars v).1 hv
    exact h2 c hc v hvc
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun c hc v hvc => h2 ((mem_vars v).2 ⟨c, hc, hvc⟩)⟩

theorem kl_isForm_substLin (n : ℕ) (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (p : GCTOcc.PolyR) (hp : GCTOcc.IsForm n p) : GCTOcc.IsForm n (GCTOcc.substLin n g p) := by
  rw [kl_isForm_iff] at hp ⊢
  refine ⟨?_, kl_substLin_mem_supported n g p hp.2⟩
  have := hp.1.aeval (S := ℂ) (n := 1)
    (fun v : ℕ × ℕ => if h : v.1 < n ∧ v.2 < n then
      ∑ w : Fin n × Fin n, C (g (⟨v.1, h.1⟩, ⟨v.2, h.2⟩) w) * X (((w.1 : ℕ)), ((w.2 : ℕ)))
      else X v) ?_
  · simpa [GCTOcc.substLin] using this
  · intro v
    by_cases hv : v.1 < n ∧ v.2 < n
    · simp only [dif_pos hv]
      exact IsHomogeneous.sum _ _ _ (fun w _ => (isHomogeneous_C_mul_X _ _))
    · simp only [dif_neg hv]
      exact isHomogeneous_X _ _

/-- An HWV is invariant under unipotent upper triangular matrices. -/
theorem kl_hwv_unipotent {n d : ℕ} {lam : ℕ → ℕ} {F : GCTOcc.CoordRing} (hF : GCTOcc.IsHWV n d lam F)
    (b : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hb : GCTOcc.IsUpperTri n b)
    (hb1 : ∀ v, b v v = 1) (p : GCTOcc.PolyR) (hp : GCTOcc.IsForm n p) :
    GCTOcc.evalCoeff (GCTOcc.substLin n b p) F = GCTOcc.evalCoeff p F := by
  rw [hF.2 b hb (fun v => by simp [hb1 v]) p hp]
  simp [hb1]

/-- The diagonal matrix with `t` at `w` and `1` elsewhere. -/
noncomputable def klDiag (n : ℕ) (w : Fin n × Fin n) (t : ℂ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  Matrix.diagonal (fun v => if v = w then t else 1)

theorem kl_hwv_diag {n d : ℕ} {lam : ℕ → ℕ} {F : GCTOcc.CoordRing} (hF : GCTOcc.IsHWV n d lam F)
    (w : Fin n × Fin n) (t : ℂ) (ht : t ≠ 0) (p : GCTOcc.PolyR) (hp : GCTOcc.IsForm n p) :
    GCTOcc.evalCoeff (GCTOcc.substLin n (klDiag n w t) p) F
      = t ^ lam (GCTOcc.idx n w) * GCTOcc.evalCoeff p F := by
  have hup : GCTOcc.IsUpperTri n (klDiag n w t) := by
    intro v u hvu
    have : v ≠ u := by rintro rfl; exact lt_irrefl _ hvu
    simp [klDiag, Matrix.diagonal_apply_ne _ this]
  rw [hF.2 _ hup (fun v => by by_cases h : v = w <;> simp [klDiag, h, ht]) p hp]
  congr 1
  rw [Finset.prod_eq_single w]
  · simp [klDiag]
  · intro v _ hv
    simp [klDiag, hv]
  · simp

/-- Torus kill: if scaling the variable `w` fixes the form `p` and `lam (idx w) > 0`, then any
HWV of weight `lam` vanishes at `p`. -/
theorem kl_hwv_kill {n d : ℕ} {lam : ℕ → ℕ} {F : GCTOcc.CoordRing} (hF : GCTOcc.IsHWV n d lam F)
    (w : Fin n × Fin n) (hw : 0 < lam (GCTOcc.idx n w)) (p : GCTOcc.PolyR)
    (hp : GCTOcc.IsForm n p) (hfix : GCTOcc.substLin n (klDiag n w 2) p = p) :
    GCTOcc.evalCoeff p F = 0 := by
  have h := kl_hwv_diag hF w 2 two_ne_zero p hp
  rw [hfix] at h
  have h2 : (2 : ℂ) ^ lam (GCTOcc.idx n w) ≠ 1 := by
    have h3 : (1 : ℕ) < 2 ^ lam (GCTOcc.idx n w) := Nat.one_lt_two_pow hw.ne'
    intro hc
    have h4 : ((2 ^ lam (GCTOcc.idx n w) : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by push_cast; exact hc
    exact h3.ne' (Nat.cast_injective h4)
  have : (1 - (2 : ℂ) ^ lam (GCTOcc.idx n w)) * GCTOcc.evalCoeff p F = 0 := by
    rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.1 this with h3 | h3
  · exact absurd (sub_eq_zero.1 h3).symm h2
  · exact h3

/-- The variables of the `m × m` block. -/
def klSq (m : ℕ) : Set (ℕ × ℕ) := {v | v.1 < m ∧ v.2 < m}

theorem kl_paddedPerm_supported (m n : ℕ) (hm : 0 < m) :
    GCTOcc.paddedPerm m n ∈ supported ℂ (klSq m) := by
  unfold GCTOcc.paddedPerm GCTOcc.permPoly
  refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (X_mem_supported.2 (show ((0, 0) : ℕ × ℕ) ∈ klSq m from ⟨hm, hm⟩)) _) ?_
  refine Subalgebra.sum_mem _ (fun σ _ => Subalgebra.prod_mem _ (fun i _ => ?_))
  exact X_mem_supported.2 (show ((i : ℕ) < m ∧ ((σ i : Fin m) : ℕ) < m) from ⟨i.isLt, (σ i).isLt⟩)

theorem kl_paddedPerm_homog (m n : ℕ) (hmn : m ≤ n) :
    (GCTOcc.paddedPerm m n).IsHomogeneous n := by
  have h1 : ((X (0, 0) : GCTOcc.PolyR) ^ (n - m)).IsHomogeneous (n - m) := isHomogeneous_X_pow _ _
  have h2 : (GCTOcc.permPoly m).IsHomogeneous m := by
    unfold GCTOcc.permPoly
    apply IsHomogeneous.sum
    intro σ _
    simpa using IsHomogeneous.prod (Finset.univ : Finset (Fin m))
      (fun i => (X ((i : ℕ), ((σ i : Fin m) : ℕ)) : GCTOcc.PolyR)) (fun _ => 1)
      (fun i _ => isHomogeneous_X ℂ _)
  have := h1.mul h2
  rwa [Nat.sub_add_cancel hmn] at this

theorem kl_isForm_paddedPerm (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n) :
    GCTOcc.IsForm n (GCTOcc.paddedPerm m n) := by
  rw [kl_isForm_iff]
  refine ⟨kl_paddedPerm_homog m n hmn, supported_mono ?_ (kl_paddedPerm_supported m n hm)⟩
  intro v hv
  exact ⟨lt_of_lt_of_le hv.1 hmn, lt_of_lt_of_le hv.2 hmn⟩

/-- `substLin` on a polynomial in the `m × m` block only sees the rows of that block. -/
theorem kl_substLin_congr (n m : ℕ) (hmn : m ≤ n) (p : GCTOcc.PolyR)
    (hp : p ∈ supported ℂ (klSq m)) (h1 h2 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hrow : ∀ v : Fin n × Fin n, (v.1 : ℕ) < m → (v.2 : ℕ) < m → h1 v = h2 v) :
    GCTOcc.substLin n h1 p = GCTOcc.substLin n h2 p := by
  unfold GCTOcc.substLin
  rw [aeval_def, aeval_def]
  apply eval₂_congr
  intro i c hi hc
  have hiv : i ∈ p.vars := (mem_vars_iff_mem_support i).2 ⟨c, mem_support_iff.2 hc, hi⟩
  have hi' : i.1 < m ∧ i.2 < m := (mem_supported.1 hp) hiv
  have hh : i.1 < n ∧ i.2 < n := ⟨lt_of_lt_of_le hi'.1 hmn, lt_of_lt_of_le hi'.2 hmn⟩
  simp only [dif_pos hh]
  rw [hrow (⟨i.1, hh.1⟩, ⟨i.2, hh.2⟩) hi'.1 hi'.2]

/-- Among `M + 1` vectors in a space of dimension `M`, one lies in the span of the earlier ones. -/
theorem kl_exists_dep {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (c : ℕ → V) (M : ℕ) (hM : Module.finrank ℂ V = M) :
    ∃ k ≤ M, c k ∈ Submodule.span ℂ (c '' Set.Iio k) := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ k, k ≤ M + 1 → LinearIndepOn ℂ c (Set.Iio k) := by
    intro k
    induction k with
    | zero => intro _; simpa using (linearIndepOn_empty (R := ℂ) (v := c))
    | succ k ih =>
      intro hk
      have hset : Set.Iio (k + 1) = insert k (Set.Iio k) := by
        ext x; simp [Nat.lt_succ_iff_lt_or_eq, or_comm]
      rw [hset, linearIndepOn_insert (by simp)]
      exact ⟨ih (by omega), hcon k (by omega)⟩
  have h := (key (M + 1) le_rfl).encard_le_toENat_rank
  rw [← Finset.coe_range, Set.encard_coe_eq_coe_finsetCard, Finset.card_range,
    ← Module.finrank_eq_rank, hM] at h
  have h' : ((M + 1 : ℕ) : ℕ∞) ≤ (M : ℕ∞) := by simpa using h
  have h'' : M + 1 ≤ M := by exact_mod_cast h'
  omega

theorem kl_idx_eq (n : ℕ) (x : Fin n × Fin n) :
    ((finProdFinEquiv x : Fin (n * n)) : ℕ) = GCTOcc.idx n x := by
  simp [finProdFinEquiv_apply_val, GCTOcc.idx]
  ring

/-- Rows half of G1 at orbit points: if `lam` is positive on `0, …, m*m` then every HWV of weight
`lam` vanishes at every `g`-substitution of the padded permanent. -/
def gctPF (f : ℂ → ℂ) : Prop := ∃ P : Polynomial ℂ, ∀ t, f t = P.eval t

theorem gctPF_const (c : ℂ) : gctPF (fun _ => c) := ⟨Polynomial.C c, fun t => by simp⟩

theorem gctPF_id : gctPF (fun t => t) := ⟨Polynomial.X, fun t => by simp⟩

theorem gctPF_add {f g : ℂ → ℂ} (hf : gctPF f) (hg : gctPF g) : gctPF (fun t => f t + g t) := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨P + Q, fun t => by simp [hP, hQ]⟩

theorem gctPF_mul {f g : ℂ → ℂ} (hf : gctPF f) (hg : gctPF g) : gctPF (fun t => f t * g t) := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨P * Q, fun t => by simp [hP, hQ]⟩

theorem gctPF_sum {ι : Type} (s : Finset ι) (f : ι → ℂ → ℂ) (h : ∀ i ∈ s, gctPF (f i)) :
    gctPF (fun t => ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using gctPF_const 0
  | insert a s ha ih =>
    have h1 := gctPF_add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    simpa [Finset.sum_insert ha] using h1

theorem gctPF_prod {ι : Type} (s : Finset ι) (f : ι → ℂ → ℂ) (h : ∀ i ∈ s, gctPF (f i)) :
    gctPF (fun t => ∏ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using gctPF_const 1
  | insert a s ha ih =>
    have h1 := gctPF_mul (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    simpa [Finset.prod_insert ha] using h1

theorem gctPF_continuous {f : ℂ → ℂ} (hf : gctPF f) : Continuous f := by
  obtain ⟨P, hP⟩ := hf
  have : f = fun t => P.eval t := funext hP
  rw [this]
  exact P.continuous

theorem gctPF_finite_zeros {f : ℂ → ℂ} (hf : gctPF f) {t₀ : ℂ} (h : f t₀ ≠ 0) :
    {t | f t = 0}.Finite := by
  obtain ⟨P, hP⟩ := hf
  have hP0 : P ≠ 0 := by
    rintro rfl
    exact h (by simp [hP])
  apply (Polynomial.finite_setOf_isRoot hP0).subset
  intro t ht
  simp only [Set.mem_setOf_eq] at ht ⊢
  rw [hP] at ht
  exact ht

theorem gct_coeff_substLin_line (n : ℕ) (A B : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (p : GCTOcc.PolyR) : ∀ m : (ℕ × ℕ) →₀ ℕ,
    gctPF (fun t => coeff m (GCTOcc.substLin n (A + t • B) p)) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    intro m
    simp only [GCTOcc.substLin, aeval_C]
    exact gctPF_const _
  | add p q hp hq =>
    intro m
    simp only [GCTOcc.substLin, map_add, coeff_add] at hp hq ⊢
    exact gctPF_add (hp m) (hq m)
  | mul_X p v hp =>
    intro m
    simp only [GCTOcc.substLin, map_mul, aeval_X] at hp ⊢
    simp only [coeff_mul]
    apply gctPF_sum
    intro x _
    apply gctPF_mul (hp x.1)
    by_cases hv : v.1 < n ∧ v.2 < n
    · simp only [dif_pos hv, coeff_sum, coeff_C_mul]
      apply gctPF_sum
      intro w _
      apply gctPF_mul _ (gctPF_const _)
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      exact gctPF_add (gctPF_const _) (gctPF_mul gctPF_id (gctPF_const _))
    · simp only [dif_neg hv]
      exact gctPF_const _

theorem gctPF_evalF (F : GCTOcc.CoordRing) (c : ((ℕ × ℕ) →₀ ℕ) → ℂ → ℂ)
    (hc : ∀ m, gctPF (c m)) : gctPF (fun t => eval (fun m => c m t) F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simpa using gctPF_const a
  | add p q hp hq => simpa using gctPF_add hp hq
  | mul_X p m hp => simpa using gctPF_mul hp (hc m)

theorem gctPF_evalCoeff_line (n : ℕ) (A B : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (p : GCTOcc.PolyR) (F : GCTOcc.CoordRing) :
    gctPF (fun t => GCTOcc.evalCoeff (GCTOcc.substLin n (A + t • B) p) F) := by
  unfold GCTOcc.evalCoeff
  exact gctPF_evalF F (fun m t => coeff m (GCTOcc.substLin n (A + t • B) p))
    (gct_coeff_substLin_line n A B p)

theorem gctPF_det {N : Type} [Fintype N] [DecidableEq N] (A B : Matrix N N ℂ) :
    gctPF (fun t => (A + t • B).det) := by
  simp only [Matrix.det_apply']
  apply gctPF_sum
  intro σ _
  apply gctPF_mul (gctPF_const _)
  apply gctPF_prod
  intro i _
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact gctPF_add (gctPF_const _) (gctPF_mul gctPF_id (gctPF_const _))

/-- A point of the orbit closure where `F` does not vanish yields an orbit point where it does
not vanish. -/
theorem gct_orbit_of_closure {n : ℕ} {p₀ p : GCTOcc.PolyR} (hp : p ∈ GCTOcc.orbitClosure n p₀)
    (F : GCTOcc.CoordRing) (hF : GCTOcc.evalCoeff p F ≠ 0) :
    ∃ g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ, IsUnit g.det ∧
      GCTOcc.evalCoeff (GCTOcc.substLin n g p₀) F ≠ 0 := by
  obtain ⟨g, hg, hlim⟩ := hp
  have h1 : Tendsto (fun k => (fun m => coeff m (GCTOcc.substLin n (g k) p₀))) atTop
      (𝓝 (fun m => coeff m p)) := tendsto_pi_nhds.2 hlim
  have h2 := ((MvPolynomial.continuous_eval F).tendsto _).comp h1
  have h3 := h2.eventually (isOpen_ne.mem_nhds hF)
  obtain ⟨k, hk⟩ := h3.exists
  exact ⟨g k, hg k, hk⟩

/-- Scaling all coordinates scales a degree `d` homogeneous polynomial by `s ^ d`. -/
theorem kl_eval_smul (F : GCTOcc.CoordRing) (d : ℕ) (hF : F.IsHomogeneous d) (s : ℂ)
    (x : ((ℕ × ℕ) →₀ ℕ) → ℂ) : eval (fun μ => s * x μ) F = s ^ d * eval x F := by
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun μ hμ => ?_)
  have hw := hF (mem_support_iff.1 hμ)
  simp only [eval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  rw [← hw]
  simp only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one]
  ring

theorem kl_evalCoeff_C_mul (F : GCTOcc.CoordRing) (d : ℕ) (hF : F.IsHomogeneous d) (s : ℂ)
    (R : GCTOcc.PolyR) : GCTOcc.evalCoeff (C s * R) F = s ^ d * GCTOcc.evalCoeff R F := by
  unfold GCTOcc.evalCoeff
  simp only [coeff_C_mul]
  exact kl_eval_smul F d hF s _

/-- The elementary matrix with a single `1` at `(v0, v0)`. -/
theorem kl_coeff_aeval_diag (c : ℕ × ℕ → ℂ) (p : GCTOcc.PolyR) (μ : (ℕ × ℕ) →₀ ℕ) :
    coeff μ (aeval (fun v => C (c v) * X v) p) = (μ.prod fun v k => c v ^ k) * coeff μ p := by
  classical
  have key : ∀ (s : (ℕ × ℕ) →₀ ℕ) (a : ℂ), aeval (fun v => C (c v) * X v) (monomial s a)
      = monomial s (a * s.prod fun v k => c v ^ k) := by
    intro s a
    rw [aeval_monomial, monomial_eq]
    simp only [mul_pow, Finsupp.prod_mul, algebraMap_eq, C_mul, ← map_pow]
    rw [map_finsuppProd C]
    ring
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, key, coeff_sum, coeff_monomial]
  rw [Finset.sum_eq_single μ]
  · simp [mul_comm]
  · intro b _ hb; simp [hb]
  · intro hμ
    simp only [if_pos rfl]
    rw [notMem_support_iff.1 hμ]; simp

theorem kl_coeff_substLin_diag0 (n : ℕ) (hn : 0 < n) (t : ℂ) (p : GCTOcc.PolyR)
    (μ : (ℕ × ℕ) →₀ ℕ) :
    coeff μ (GCTOcc.substLin n (klDiag n (⟨0, hn⟩, ⟨0, hn⟩) t) p) = t ^ μ (0, 0) * coeff μ p := by
  classical
  have hf : (fun v : ℕ × ℕ => if h : v.1 < n ∧ v.2 < n then
      ∑ w : Fin n × Fin n, C (klDiag n (⟨0, hn⟩, ⟨0, hn⟩) t (⟨v.1, h.1⟩, ⟨v.2, h.2⟩) w)
        * X (((w.1 : ℕ)), ((w.2 : ℕ)))
      else X v) = fun v => C (if v = (0, 0) then t else 1) * X v := by
    funext v
    by_cases hv : v.1 < n ∧ v.2 < n
    · rw [dif_pos hv, Finset.sum_eq_single (⟨v.1, hv.1⟩, ⟨v.2, hv.2⟩)]
      · simp only [klDiag, Matrix.diagonal_apply_eq]
        congr 2
        · congr 1
          apply propext
          constructor
          · intro h; rw [Prod.ext_iff] at h ⊢; simp [Fin.ext_iff] at h; exact ⟨h.1, h.2⟩
          · intro h; rw [Prod.ext_iff] at h ⊢; simp [Fin.ext_iff]; exact ⟨h.1, h.2⟩
      · intro w _ hw
        simp [klDiag, Matrix.diagonal_apply_ne _ (Ne.symm hw)]
      · simp
    · rw [dif_neg hv]
      have : v ≠ (0, 0) := by rintro rfl; exact hv ⟨hn, hn⟩
      simp [this]
  unfold GCTOcc.substLin
  rw [hf, kl_coeff_aeval_diag]
  congr 1
  rw [Finsupp.prod]
  simp only [ite_pow, one_pow]
  rw [Finset.prod_ite_eq']
  split_ifs with h
  · rfl
  · rw [Finsupp.notMem_support_iff.1 h, pow_zero]

/-- Value of a polynomial function `F` at coefficient vector `x`, expanded in monomials. -/
theorem kl_eval_expand (F : GCTOcc.CoordRing) (x : ((ℕ × ℕ) →₀ ℕ) → ℂ) :
    eval x F = ∑ ν ∈ F.support, coeff ν F * ν.prod fun μ k => x μ ^ k := by
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun ν _ => eval_monomial)

theorem kl_le_deg (μ : (ℕ × ℕ) →₀ ℕ) (v : ℕ × ℕ) : μ v ≤ μ.sum fun _ k => k := by
  classical
  by_cases hv : v ∈ μ.support
  · rw [Finsupp.sum]
    exact Finset.single_le_sum (f := fun i => μ i) (fun _ _ => Nat.zero_le _) hv
  · rw [Finsupp.notMem_support_iff.1 hv]; exact Nat.zero_le _

theorem kl_weight_one (μ : (ℕ × ℕ) →₀ ℕ) : Finsupp.weight 1 μ = μ.sum fun _ k => k := by
  simp [Finsupp.weight_apply, Finsupp.sum]

theorem kl_weight_one' (ν : ((ℕ × ℕ) →₀ ℕ) →₀ ℕ) : Finsupp.weight 1 ν = ν.sum fun _ k => k := by
  simp [Finsupp.weight_apply, Finsupp.sum]

/-- The `X00`-weight of a monomial in the coordinate ring. -/
def klW (ν : ((ℕ × ℕ) →₀ ℕ) →₀ ℕ) : ℕ := ν.sum fun μ k => μ (0, 0) * k

/-- Weight-space extraction: the value of an HWV at a form equals the sum over the monomials of
`F` of `X00`-weight `lam 0`. -/
theorem kl_hwv_extract (n d : ℕ) (hn : 0 < n) (lam : ℕ → ℕ) (F : GCTOcc.CoordRing)
    (hF : GCTOcc.IsHWV n d lam F) (q : GCTOcc.PolyR) (hq : GCTOcc.IsForm n q) :
    GCTOcc.evalCoeff q F = ∑ ν ∈ F.support.filter (fun ν => klW ν = lam 0),
      coeff ν F * ν.prod fun μ k => coeff μ q ^ k := by
  classical
  have hidx : GCTOcc.idx n (⟨0, hn⟩, ⟨0, hn⟩) = 0 := by simp [GCTOcc.idx]
  have hval : ∀ t : ℂ, t ≠ 0 → ∑ ν ∈ F.support,
      (coeff ν F * ν.prod fun μ k => coeff μ q ^ k) * t ^ klW ν
        = t ^ lam 0 * GCTOcc.evalCoeff q F := by
    intro t ht
    have h1 := kl_hwv_diag hF (⟨0, hn⟩, ⟨0, hn⟩) t ht q hq
    rw [hidx] at h1
    rw [← h1]
    unfold GCTOcc.evalCoeff
    rw [kl_eval_expand]
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    simp only [kl_coeff_substLin_diag0, mul_pow, Finsupp.prod_mul, ← pow_mul]
    rw [mul_assoc]
    congr 1
    rw [mul_comm]
    congr 1
    rw [klW, Finsupp.prod, Finsupp.sum, Finset.prod_pow_eq_pow_sum]
  let Pol : Polynomial ℂ := ∑ ν ∈ F.support,
      Polynomial.C (coeff ν F * ν.prod fun μ k => coeff μ q ^ k) * Polynomial.X ^ klW ν
    - Polynomial.C (GCTOcc.evalCoeff q F) * Polynomial.X ^ lam 0
  have hPol : Pol = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply ((Set.finite_singleton (0 : ℂ)).infinite_compl).mono
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Pol, Polynomial.eval_sub,
      Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    rw [hval t ht]; ring
  have hc := congrArg (fun r => Polynomial.coeff r (lam 0)) hPol
  simp only [Pol, Polynomial.coeff_sub, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow,
    if_pos rfl, ↓reduceIte, Polynomial.coeff_zero] at hc
  rw [sub_eq_zero] at hc
  rw [Finset.sum_filter, ← hc]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  by_cases h : klW ν = lam 0
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- G2-i. -/
theorem hwv_truncate (n d s : ℕ) (hs : s ≤ n) (lam : ℕ → ℕ)
    (hlam : GCTOcc.IsPartitionOf lam (n * n) (n * d))
    (hbody : (∑ i ∈ Finset.range (n * n), lam (i + 1)) ≤ s)
    (F : GCTOcc.CoordRing) (hF : GCTOcc.IsHWV n d lam F) (q : GCTOcc.PolyR)
    (hq : GCTOcc.IsForm n q) (hne : GCTOcc.evalCoeff q F ≠ 0) :
    ∃ h : GCTOcc.PolyR, h.IsHomogeneous s ∧ (∀ μ ∈ h.support, ∀ v ∈ μ.support, v.1 < n ∧ v.2 < n) ∧
      GCTOcc.evalCoeff (X (0, 0) ^ (n - s) * h) F ≠ 0 := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    have hs0 : s = 0 := by omega
    subst hs0
    exact ⟨q, hq.1, hq.2, by simpa using hne⟩
  -- lam 0 ≥ n d - s
  have hlam0 : n * d ≤ lam 0 + s := by
    have h1 := Finset.sum_range_succ' lam (n * n)
    have h2 := Finset.sum_range_succ lam (n * n)
    have h0 := hlam.2.2
    have hN := hlam.2.1 (n * n) le_rfl
    omega
  set S := q.support.filter (fun μ => n - s ≤ μ (0, 0)) with hS
  set qhi : GCTOcc.PolyR := ∑ μ ∈ S, monomial μ (coeff μ q) with hqhi
  set h : GCTOcc.PolyR := ∑ μ ∈ S, monomial (μ - Finsupp.single (0, 0) (n - s)) (coeff μ q) with hh
  have hcoeff : ∀ μ, coeff μ qhi = if n - s ≤ μ (0, 0) then coeff μ q else 0 := by
    intro μ
    rw [hqhi, coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
    by_cases h2 : n - s ≤ μ (0, 0)
    · rw [if_pos h2]
      by_cases hμ : μ ∈ q.support
      · rw [if_pos (Finset.mem_filter.2 ⟨hμ, h2⟩)]
      · rw [if_neg (fun h => hμ (Finset.mem_filter.1 h).1), notMem_support_iff.1 hμ]
    · rw [if_neg h2, if_neg (show μ ∉ S from fun h => h2 (Finset.mem_filter.1 h).2)]
  have hXh : X (0, 0) ^ (n - s) * h = qhi := by
    rw [hh, hqhi, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun μ hμ => ?_)
    have h2 : n - s ≤ μ (0, 0) := (Finset.mem_filter.1 hμ).2
    rw [X_pow_eq_monomial, monomial_mul, one_mul,
      add_tsub_cancel_of_le (Finsupp.single_le_iff.2 h2)]
  have hqform : GCTOcc.IsForm n qhi := by
    refine ⟨?_, ?_⟩
    · intro μ hμ
      rw [hcoeff] at hμ
      split_ifs at hμ with h2
      · exact hq.1 hμ
      · exact absurd rfl hμ
    · intro μ hμ v hv
      rw [mem_support_iff, hcoeff] at hμ
      split_ifs at hμ with h2
      · exact hq.2 μ (mem_support_iff.2 hμ) v hv
      · exact absurd rfl hμ
  refine ⟨h, ?_, ?_, ?_⟩
  · -- homogeneity of h
    rw [hh]
    apply IsHomogeneous.sum
    intro μ hμ
    apply isHomogeneous_monomial
    have hμq := hq.1 (mem_support_iff.1 (Finset.mem_filter.1 hμ).1)
    have h2 : n - s ≤ μ (0, 0) := (Finset.mem_filter.1 hμ).2
    have hμd : Finsupp.degree μ = n := by rw [Finsupp.degree_eq_weight_one]; exact hμq
    have e1 := congrArg Finsupp.degree (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 h2))
    rw [map_add, Finsupp.degree_single] at e1
    omega
  · intro μ hμ v hv
    have hsub := support_sum (s := S) (f := fun μ => monomial (μ - Finsupp.single (0, 0) (n - s))
      (coeff μ q)) hμ
    simp only [Finset.mem_biUnion] at hsub
    obtain ⟨ρ, hρ, hρμ⟩ := hsub
    have := support_monomial_subset hρμ
    rw [Finset.mem_singleton] at this
    subst this
    have hvρ : v ∈ ρ.support := by
      rw [Finsupp.mem_support_iff] at hv ⊢
      simp only [Finsupp.tsub_apply] at hv
      omega
    exact hq.2 ρ (Finset.mem_filter.1 hρ).1 v hvρ
  · rw [hXh]
    -- F(q) = F(qhi) by weight extraction
    rw [kl_hwv_extract n d hn lam F hF qhi hqform]
    rw [kl_hwv_extract n d hn lam F hF q hq] at hne
    convert hne using 1
    refine Finset.sum_congr rfl (fun ν hν => ?_)
    obtain ⟨hνF, hνw⟩ := Finset.mem_filter.1 hν
    rw [klW] at hνw
    congr 1
    by_cases hz : ∃ μ ∈ ν.support, coeff μ q = 0
    · obtain ⟨μ, hμν, hμ0⟩ := hz
      have hμhi : coeff μ qhi = 0 := by rw [hcoeff]; split_ifs <;> simp [hμ0]
      rw [Finsupp.prod, Finsupp.prod, Finset.prod_eq_zero hμν, Finset.prod_eq_zero hμν]
      · rw [hμ0, zero_pow (Finsupp.mem_support_iff.1 hμν)]
      · rw [hμhi, zero_pow (Finsupp.mem_support_iff.1 hμν)]
    · push_neg at hz
      rw [Finsupp.prod, Finsupp.prod]
      refine Finset.prod_congr rfl (fun μ hμν => ?_)
      rw [hcoeff, if_pos]
      -- every monomial used has X00-degree ≥ n - s
      by_contra hlt
      push_neg at hlt
      have hdeg : ∀ ρ ∈ ν.support, ρ (0, 0) ≤ n := by
        intro ρ hρ
        have := hq.1 (hz ρ hρ)
        rw [kl_weight_one] at this
        rw [← this]; exact kl_le_deg ρ (0, 0)
      have hνd := hF.1 (mem_support_iff.1 hνF)
      rw [kl_weight_one'] at hνd
      have hsum : (ν.sum fun ρ k => ρ (0, 0) * k) + (ν.sum fun ρ k => (n - ρ (0, 0)) * k)
          = n * d := by
        rw [← hνd, ← Finsupp.sum_add, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun ρ hρ => ?_)
        rw [← Nat.add_mul, Nat.add_sub_cancel' (hdeg ρ hρ), mul_comm]
      have hbig : s + 1 ≤ ν.sum fun ρ k => (n - ρ (0, 0)) * k := by
        rw [Finsupp.sum]
        calc s + 1 ≤ (n - μ (0, 0)) * ν μ := by
              have := Finsupp.mem_support_iff.1 hμν
              have h1 : 1 ≤ ν μ := Nat.pos_of_ne_zero this
              have h2 : s + 1 ≤ n - μ (0, 0) := by omega
              nlinarith
          _ ≤ ∑ ρ ∈ ν.support, (n - ρ (0, 0)) * ν ρ :=
              Finset.single_le_sum (f := fun ρ => (n - ρ (0, 0)) * ν ρ)
                (fun _ _ => Nat.zero_le _) hμν
      omega

/-! G2-ii' (hwv_few_monomials): polarization; a degree `d` function nonvanishing at `P * h` is
nonvanishing at `P * h'` for some `h'` with at most `d` monomials, all taken from `h`. -/

theorem kl_eval_aeval {σ : Type} (f : σ → MvPolynomial σ ℂ) (c : σ → ℂ) (G : MvPolynomial σ ℂ) :
    eval c (aeval f G) = eval (fun j => eval c (f j)) G := by
  induction G using MvPolynomial.induction_on with
  | C a => rw [aeval_C, algebraMap_eq, eval_C, eval_C]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p j hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, eval_X]

theorem kl_coeff_restrict {σ : Type} [DecidableEq σ] (G : MvPolynomial σ ℂ) (T : Finset σ)
    (α : σ →₀ ℕ) (hα : α.support ⊆ T) :
    coeff α (aeval (fun j => if j ∈ T then (X j : MvPolynomial σ ℂ) else 0) G) = coeff α G := by
  classical
  have key : ∀ (β : σ →₀ ℕ) (a : ℂ),
      aeval (fun j => if j ∈ T then (X j : MvPolynomial σ ℂ) else 0) (monomial β a)
        = if β.support ⊆ T then monomial β a else 0 := by
    intro β a
    rw [aeval_monomial, Finsupp.prod]
    split_ifs with hβ
    · rw [monomial_eq, Finsupp.prod, algebraMap_eq]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      rw [if_pos (hβ hj)]
    · obtain ⟨j, hj, hjT⟩ := Finset.not_subset.1 hβ
      rw [Finset.prod_eq_zero hj (by rw [if_neg hjT, zero_pow (Finsupp.mem_support_iff.1 hj)]),
        mul_zero]
  conv_lhs => rw [G.as_sum]
  rw [map_sum, coeff_sum]
  simp only [key]
  rw [Finset.sum_eq_single α]
  · rw [if_pos hα, coeff_monomial, if_pos rfl]
  · intro β _ hβ
    split_ifs
    · rw [coeff_monomial, if_neg hβ]
    · simp
  · intro hα'
    rw [notMem_support_iff.1 hα']
    simp

theorem kl_card_support_le (α : ((ℕ × ℕ) →₀ ℕ) →₀ ℕ) : α.support.card ≤ Finsupp.degree α := by
  rw [Finsupp.degree, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum (fun i hi => Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi))

/-- G2-ii'. -/
theorem hwv_few_monomials (d : ℕ) (F : GCTOcc.CoordRing) (hFd : F.IsHomogeneous d)
    (P h : GCTOcc.PolyR) (hne : GCTOcc.evalCoeff (P * h) F ≠ 0) :
    ∃ h' : GCTOcc.PolyR, h'.support ⊆ h.support ∧ h'.support.card ≤ d ∧
      GCTOcc.evalCoeff (P * h') F ≠ 0 := by
  classical
  set J := h.support with hJ
  let L : ((ℕ × ℕ) →₀ ℕ) → GCTOcc.CoordRing := fun ν =>
    ∑ μ ∈ J, C (coeff ν (P * monomial μ 1)) * X μ
  set G : GCTOcc.CoordRing := aeval L F with hG
  -- value of G at a coefficient vector
  have hval : ∀ c : ((ℕ × ℕ) →₀ ℕ) → ℂ,
      eval c G = GCTOcc.evalCoeff (P * ∑ μ ∈ J, monomial μ (c μ)) F := by
    intro c
    rw [hG, kl_eval_aeval]
    unfold GCTOcc.evalCoeff
    have hfun : (fun j => eval c (L j)) = (fun m => coeff m (P * ∑ μ ∈ J, monomial μ (c μ))) := by
      funext ν
      simp only [L, map_sum, map_mul, eval_C, eval_X, Finset.mul_sum, coeff_sum]
      refine Finset.sum_congr rfl (fun μ _ => ?_)
      rw [show (monomial μ (c μ) : GCTOcc.PolyR) = C (c μ) * monomial μ 1 by
        rw [C_mul_monomial, mul_one]]
      rw [mul_left_comm, coeff_C_mul, mul_comm]
    rw [hfun]
  have hGhom : G.IsHomogeneous d := by
    have := hFd.aeval (S := ℂ) (n := 1) L (fun ν => IsHomogeneous.sum _ _ _
      (fun μ _ => isHomogeneous_C_mul_X _ _))
    rw [one_mul] at this
    exact this
  have hGne : G ≠ 0 := by
    intro h0
    apply hne
    have h1 := hval (fun μ => coeff μ h)
    have hh : (∑ μ ∈ J, monomial μ (coeff μ h)) = h := h.as_sum.symm
    rw [h0, map_zero, hh] at h1
    exact h1.symm
  obtain ⟨α, hα⟩ := MvPolynomial.ne_zero_iff.1 hGne
  set T := α.support with hT
  have hαd : Finsupp.degree α = d := by
    rw [Finsupp.degree_eq_weight_one]; exact hGhom hα
  -- the restriction of G to the variables in T is nonzero
  set GT : GCTOcc.CoordRing := aeval (fun j => if j ∈ T then (X j : GCTOcc.CoordRing) else 0) G
    with hGT
  have hGTne : GT ≠ 0 := by
    intro h0
    have := kl_coeff_restrict G T α (subset_refl _)
    rw [← hGT, h0, coeff_zero] at this
    exact hα this.symm
  obtain ⟨c, hc⟩ : ∃ c : ((ℕ × ℕ) →₀ ℕ) → ℂ, eval c GT ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hGTne (MvPolynomial.funext (fun x => by rw [hall x, map_zero]))
  set c' : ((ℕ × ℕ) →₀ ℕ) → ℂ := fun j => if j ∈ T then c j else 0 with hc'
  have hc'G : eval c' G ≠ 0 := by
    have : eval c GT = eval c' G := by
      rw [hGT, kl_eval_aeval]
      have hfun : (fun j => eval c (if j ∈ T then (X j : GCTOcc.CoordRing) else 0)) = c' := by
        funext j
        rw [hc']
        by_cases hj : j ∈ T <;> simp [hj]
      rw [hfun]
    rwa [← this]
  refine ⟨∑ μ ∈ J, monomial μ (c' μ), ?_, ?_, by rw [← hval]; exact hc'G⟩
  · intro μ hμ
    have := support_sum hμ
    simp only [Finset.mem_biUnion] at this
    obtain ⟨ρ, hρ, hρμ⟩ := this
    have := support_monomial_subset hρμ
    rw [Finset.mem_singleton] at this
    rw [this]; exact hρ
  · calc (∑ μ ∈ J, monomial μ (c' μ)).support.card ≤ T.card := by
          apply Finset.card_le_card
          intro μ hμ
          have := support_sum hμ
          simp only [Finset.mem_biUnion] at this
          obtain ⟨ρ, hρ, hρμ⟩ := this
          have hsub := support_monomial_subset hρμ
          rw [Finset.mem_singleton] at hsub
          subst hsub
          by_contra hnot
          have : c' μ = 0 := by rw [hc']; simp [hnot]
          rw [this, monomial_zero] at hρμ
          simp at hρμ
      _ ≤ d := hαd ▸ kl_card_support_le α


theorem gct_orbit_mem_closure (n : ℕ) (p₀ : GCTOcc.PolyR)
    (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hg : IsUnit g.det) :
    GCTOcc.substLin n g p₀ ∈ GCTOcc.orbitClosure n p₀ :=
  ⟨fun _ => g, fun _ => hg, fun _ => tendsto_const_nhds⟩


/-- Every linear substitution of `p₀` (invertible or not) lies in the orbit closure. -/
theorem gct_mem_orbitClosure_of_subst (n : ℕ) (p₀ : GCTOcc.PolyR)
    (A : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    GCTOcc.substLin n A p₀ ∈ GCTOcc.orbitClosure n p₀ := by
  classical
  have hP : A.charpoly ≠ 0 := (Matrix.charpoly_monic A).ne_zero
  have hZ : {t : ℂ | A.charpoly.eval t = 0}.Finite := by
    apply (Polynomial.finite_setOfPred_isRoot hP).subset
    intro t ht
    exact ht
  have hinj : Function.Injective (fun k : ℕ => ((1 / ((k : ℝ) + 1) : ℝ) : ℂ)) := by
    intro a b h
    simp only [Complex.ofReal_inj, one_div, inv_inj, add_left_inj, Nat.cast_inj] at h
    exact h
  have hev : ∀ᶠ k : ℕ in atTop, A.charpoly.eval (((1 / ((k : ℝ) + 1) : ℝ) : ℂ)) ≠ 0 := by
    have h1 := (hZ.preimage hinj.injOn).eventually_cofinite_notMem
    rw [Nat.cofinite_eq_atTop] at h1
    exact h1.mono fun k hk => hk
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  set t : ℕ → ℂ := fun k => ((1 / (((k + K : ℕ) : ℝ) + 1) : ℝ) : ℂ) with ht_def
  refine ⟨fun k => A + t k • (-1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ), ?_, ?_⟩
  · intro k
    have hEq : A + t k • (-1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
        = -(Matrix.scalar (Fin n × Fin n) (t k) - A) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.sub_apply,
        Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> ring
    show IsUnit (A + t k • (-1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)).det
    rw [hEq, Matrix.det_neg, isUnit_iff_ne_zero, ← Matrix.eval_charpoly]
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    exact hK (k + K) (by omega)
  · intro m
    have hcont := gctPF_continuous (gct_coeff_substLin_line n A (-1) p₀ m)
    have ht : Tendsto t atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => (1 / (((k + K : ℕ) : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat).comp (tendsto_add_atTop_nat K)
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      rw [Complex.ofReal_zero] at h2
      exact h2
    have h3 := (hcont.tendsto 0).comp ht
    have h4 : (A + (0 : ℂ) • (-1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)) = A := by simp
    rw [h4] at h3
    exact h3

/-- `substLin` of the determinant is the determinant of the substituted matrix. -/
theorem gct_substLin_detPoly (n : ℕ) (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    GCTOcc.substLin n g (GCTOcc.detPoly n)
      = (Matrix.of fun i j : Fin n =>
          ∑ w : Fin n × Fin n, C (g (i, j) w) * (X ((w.1 : ℕ), (w.2 : ℕ)) : GCTOcc.PolyR)).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  simp only [GCTOcc.detPoly, GCTOcc.substLin, map_sum, map_zsmul, map_prod, aeval_X,
    Matrix.transpose_apply, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Units.smul_def]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [dif_pos ⟨i.2, (σ i).2⟩]

theorem gct_deg1 (x : (ℕ × ℕ) →₀ ℕ) (h : (x.sum fun _ e => e) ≤ 1) :
    x = 0 ∨ ∃ v, x = Finsupp.single v 1 := by
  classical
  by_cases hx : x = 0
  · exact Or.inl hx
  right
  obtain ⟨v, hv⟩ := Finsupp.support_nonempty_iff.2 hx
  refine ⟨v, ?_⟩
  have key : ∀ u ∈ x.support, ∀ w ∈ x.support, u ≠ w → False := by
    intro u hu w hw huw
    have hle : x u + x w ≤ x.sum fun _ e => e := by
      unfold Finsupp.sum
      have hsub : ({u, w} : Finset (ℕ × ℕ)) ⊆ x.support := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact hu
        · exact hw
      have := Finset.sum_le_sum_of_subset (f := fun y => x y) hsub
      rwa [Finset.sum_pair huw] at this
    have h1 := Finsupp.mem_support_iff.1 hu
    have h2 := Finsupp.mem_support_iff.1 hw
    omega
  have hv1 : x v = 1 := by
    have hle : x v ≤ x.sum fun _ e => e := by
      unfold Finsupp.sum
      exact Finset.single_le_sum (f := fun y => x y) (fun _ _ => Nat.zero_le _) hv
    have := Finsupp.mem_support_iff.1 hv
    omega
  ext u
  by_cases huv : u = v
  · subst huv
    simp [hv1]
  · rw [Finsupp.single_apply, if_neg (Ne.symm huv)]
    by_contra hne
    exact key u (Finsupp.mem_support_iff.2 hne) v hv huv

/-- The block-restricting, scaling substitution. -/
noncomputable def gctRho (n : ℕ) (u : ℂ) : GCTOcc.PolyR →ₐ[ℂ] GCTOcc.PolyR :=
  aeval (fun v : ℕ × ℕ => if v.1 < n ∧ v.2 < n then C u * X v else 0)

/-- Affine-linear structure under the restricting scaling substitution. -/
def gctAff (n : ℕ) (q : GCTOcc.PolyR) : Prop :=
  ∃ c : ℂ, ∃ a : Fin n × Fin n → ℂ, ∀ u : ℂ,
    gctRho n u q = C c + C u * ∑ w : Fin n × Fin n, C (a w) * X ((w.1 : ℕ), (w.2 : ℕ))

theorem gctAff_add {n : ℕ} {p q : GCTOcc.PolyR} (hp : gctAff n p) (hq : gctAff n q) :
    gctAff n (p + q) := by
  obtain ⟨c₁, a₁, h₁⟩ := hp
  obtain ⟨c₂, a₂, h₂⟩ := hq
  refine ⟨c₁ + c₂, fun w => a₁ w + a₂ w, fun u => ?_⟩
  rw [map_add, h₁, h₂]
  simp only [map_add, add_mul, Finset.sum_add_distrib]
  ring

theorem gctAff_monomial {n : ℕ} (x : (ℕ × ℕ) →₀ ℕ) (hx : (x.sum fun _ e => e) ≤ 1) (b : ℂ) :
    gctAff n (monomial x b) := by
  classical
  rcases gct_deg1 x hx with rfl | ⟨v, rfl⟩
  · refine ⟨b, fun _ => 0, fun u => ?_⟩
    simp [gctRho]
  · by_cases hv : v.1 < n ∧ v.2 < n
    · set w₀ : Fin n × Fin n := (⟨v.1, hv.1⟩, ⟨v.2, hv.2⟩)
      refine ⟨0, fun w => if w = w₀ then b else 0, fun u => ?_⟩
      have hs : ∑ w : Fin n × Fin n, C (if w = w₀ then b else 0) * (X ((w.1 : ℕ), (w.2 : ℕ)) : GCTOcc.PolyR)
          = C b * X v := by
        rw [Finset.sum_eq_single w₀]
        · simp [w₀]
        · intro w _ hw
          simp [hw]
        · intro h
          exact absurd (Finset.mem_univ w₀) h
      rw [hs]
      simp only [gctRho, aeval_monomial, algebraMap_eq, Finsupp.prod_single_index, pow_one,
        if_pos hv, map_zero, zero_add, pow_zero]
      ring
    · refine ⟨0, fun _ => 0, fun u => ?_⟩
      rw [gctRho, aeval_monomial]
      simp [hv]

theorem gctAff_of_totalDegree {n : ℕ} (p : GCTOcc.PolyR) (hp : p.totalDegree ≤ 1) :
    gctAff n p := by
  classical
  have key : ∀ s : Finset ((ℕ × ℕ) →₀ ℕ), (∀ x ∈ s, (x.sum fun _ e => e) ≤ 1) →
      gctAff n (∑ x ∈ s, monomial x (coeff x p)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨0, fun _ => 0, fun u => ?_⟩
      simp
    | insert a s ha ih =>
      intro h
      rw [Finset.sum_insert ha]
      exact gctAff_add (gctAff_monomial a (h a (Finset.mem_insert_self a s)) _)
        (ih (fun x hx => h x (Finset.mem_insert_of_mem hx)))
  have := key p.support (fun x hx => (le_totalDegree hx).trans hp)
  rwa [← p.as_sum] at this

theorem gctRho_monomial {n : ℕ} (u : ℂ) (μ : (ℕ × ℕ) →₀ ℕ) (c : ℂ)
    (hμ : ∀ v ∈ μ.support, v.1 < n ∧ v.2 < n) :
    gctRho n u (monomial μ c) = C (u ^ (μ.sum fun _ e => e)) * monomial μ c := by
  rw [gctRho, aeval_monomial, algebraMap_eq, monomial_eq]
  have h1 : (μ.prod fun v e => ((if v.1 < n ∧ v.2 < n then C u * X v else 0 : GCTOcc.PolyR)) ^ e)
      = μ.prod fun v e => (C u * X v : GCTOcc.PolyR) ^ e :=
    Finsupp.prod_congr (fun v hv => by rw [if_pos (hμ v hv)])
  rw [h1]
  unfold Finsupp.prod Finsupp.sum
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_pow]
  ring

theorem gctRho_form {n s : ℕ} (u : ℂ) (f : GCTOcc.PolyR) (hf : f.IsHomogeneous s)
    (hfv : ∀ μ ∈ f.support, ∀ v ∈ μ.support, v.1 < n ∧ v.2 < n) :
    gctRho n u f = C (u ^ s) * f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum, Finset.mul_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [gctRho_monomial u μ _ (hfv μ hμ)]
  have hdeg := hf (mem_support_iff.1 hμ)
  rw [Finsupp.weight_apply] at hdeg
  congr 3
  rw [← hdeg]
  unfold Finsupp.sum
  simp

/-- Homogenisation for a general form `f` of degree `s`. -/
theorem gct_homogenize_form (n s : ℕ) (hsn : s ≤ n) (f : GCTOcc.PolyR) (c : Fin n → Fin n → ℂ)
    (ℓ : Fin n → Fin n → GCTOcc.PolyR)
    (h : ∀ u : ℂ, (Matrix.of fun i j => C (c i j) + C u * ℓ i j).det = C (u ^ s) * f) :
    (Matrix.of fun i j => ℓ i j + C (c i j) * (X (0, 0) : GCTOcc.PolyR)).det
      = (X (0, 0) : GCTOcc.PolyR) ^ (n - s) * f := by
  have hs : ∀ t : ℂ, t ≠ 0 →
      (Matrix.of fun i j => ℓ i j + C (c i j) * C t).det = C (t ^ (n - s)) * f := by
    intro t ht0
    have h1 := h t⁻¹
    have hmat : (Matrix.of fun i j => C (c i j) + C t⁻¹ * ℓ i j)
        = (C t⁻¹ : GCTOcc.PolyR) • (Matrix.of fun i j => ℓ i j + C (c i j) * C t) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
      rw [mul_add, ← mul_assoc, mul_comm (C t⁻¹) (C (c i j)), mul_assoc, ← map_mul,
        inv_mul_cancel₀ ht0, map_one, mul_one, add_comm]
    rw [hmat, Matrix.det_smul, Fintype.card_fin] at h1
    have h2 : (C t : GCTOcc.PolyR) ^ n * (C t⁻¹) ^ n = 1 := by
      rw [← mul_pow, ← map_mul, mul_inv_cancel₀ ht0, map_one, one_pow]
    calc (Matrix.of fun i j => ℓ i j + C (c i j) * C t).det
        = (C t) ^ n * ((C t⁻¹) ^ n * (Matrix.of fun i j => ℓ i j + C (c i j) * C t).det) := by
          rw [← mul_assoc, h2, one_mul]
      _ = (C t) ^ n * (C (t⁻¹ ^ s) * f) := by rw [h1]
      _ = C (t ^ (n - s)) * f := by
          rw [← mul_assoc, ← map_pow, ← map_mul]
          congr 2
          have hn : n = (n - s) + s := (Nat.sub_add_cancel hsn).symm
          conv_lhs => rw [hn, pow_add]
          rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ ht0, one_pow, mul_one]
  set Q : Polynomial GCTOcc.PolyR :=
    (Matrix.of fun i j => Polynomial.C (ℓ i j) + Polynomial.C (C (c i j)) * Polynomial.X).det
    with hQ
  have heval : ∀ r : GCTOcc.PolyR,
      Q.eval r = (Matrix.of fun i j => ℓ i j + C (c i j) * r).det := by
    intro r
    rw [hQ, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp
  set R : Polynomial GCTOcc.PolyR := Q - Polynomial.X ^ (n - s) * Polynomial.C f with hR
  have hroot : ∀ t : ℂ, t ≠ 0 → R.IsRoot (C t) := by
    intro t ht0
    simp only [Polynomial.IsRoot, hR, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, heval, hs t ht0, map_pow]
    ring
  have hR0 : R = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hinf : ({0}ᶜ : Set ℂ).Infinite := (Set.finite_singleton (0 : ℂ)).infinite_compl
    apply Set.Infinite.mono _ (hinf.image (C_injective (σ := ℕ × ℕ) (R := ℂ)).injOn)
    rintro _ ⟨t, ht, rfl⟩
    exact hroot t ht
  have hfin := congrArg (Polynomial.eval (X (0, 0) : GCTOcc.PolyR)) hR0
  simp only [hR, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_zero, heval] at hfin
  exact sub_eq_zero.1 hfin

open GCTOcc in
/-- G2-iii-a. -/
theorem padded_mem_orbitClosure_of_symbolicDet (n s : ℕ) (hsn : s ≤ n) (f : PolyR)
    (hf : f.IsHomogeneous s) (hfv : ∀ μ ∈ f.support, ∀ v ∈ μ.support, v.1 < n ∧ v.2 < n)
    (h : IsSymbolicDet f n) :
    X (0, 0) ^ (n - s) * f ∈ orbitClosure n (detPoly n) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hs : s = 0 := by omega
    subst hs
    obtain ⟨L, _, hL⟩ := h
    rw [← hL, Matrix.det_isEmpty]
    have h1 : (X (0, 0) : PolyR) ^ (0 - 0) * 1 = substLin 0 1 (detPoly 0) := by
      simp [detPoly, substLin]
    rw [h1]
    exact gct_mem_orbitClosure_of_subst 0 _ 1
  obtain ⟨L, hdeg, hdet⟩ := h
  have haff : ∀ i j, gctAff n (L i j) := fun i j => gctAff_of_totalDegree _ (hdeg i j)
  choose c a ha using haff
  set ℓ : Fin n → Fin n → PolyR := fun i j =>
    ∑ w : Fin n × Fin n, C (a i j w) * X ((w.1 : ℕ), (w.2 : ℕ)) with hℓ
  have hscal : ∀ u : ℂ, (Matrix.of fun i j => C (c i j) + C u * ℓ i j).det
      = C (u ^ s) * f := by
    intro u
    have h1 := congrArg (gctRho n u) hdet
    have h2 : gctRho n u L.det = (Matrix.of fun i j => gctRho n u (L i j)).det := by
      rw [← AlgHom.coe_toRingHom, RingHom.map_det]
      rfl
    rw [h2, gctRho_form u f hf hfv] at h1
    rw [← h1]
    congr 1
    ext i j
    simp only [Matrix.of_apply]
    rw [ha i j u]
  have hhom := gct_homogenize_form n s hsn f c ℓ hscal
  set w00 : Fin n × Fin n := (⟨0, hn⟩, ⟨0, hn⟩)
  set g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
    fun v w => a v.1 v.2 w + if w = w00 then c v.1 v.2 else 0 with hg
  have hsum : ∀ i j : Fin n, ∑ w : Fin n × Fin n, C (g (i, j) w) * (X ((w.1 : ℕ), (w.2 : ℕ)) : PolyR)
      = ℓ i j + C (c i j) * X (0, 0) := by
    intro i j
    have e : ∑ w : Fin n × Fin n, C (if w = w00 then c i j else 0) * (X ((w.1 : ℕ), (w.2 : ℕ)) : PolyR)
        = C (c i j) * X (0, 0) := by
      rw [Finset.sum_eq_single w00]
      · simp [w00]
      · intro w _ hw
        simp [hw]
      · intro hh
        exact absurd (Finset.mem_univ w00) hh
    simp only [hg, map_add, add_mul, Finset.sum_add_distrib, e]
    rfl
  have hsub : substLin n g (detPoly n) = X (0, 0) ^ (n - s) * f := by
    rw [gct_substLin_detPoly, ← hhom]
    refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
    simp only [Matrix.of_apply]
    exact hsum i j
  rw [← hsub]
  exact gct_mem_orbitClosure_of_subst n _ g


/-- Pad an affine matrix on any finite index type to size `n`. -/
theorem sd_pad {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (L : Matrix ι ι GCTOcc.PolyR)
    (haff : ∀ i j, (L i j).totalDegree ≤ 1) (hcard : Fintype.card ι ≤ n) :
    GCTOcc.IsSymbolicDet L.det n := by
  classical
  set N := Fintype.card ι with hN
  let e : ι ≃ Fin N := Fintype.equivFin ι
  let M : Matrix (Fin N ⊕ Fin (n - N)) (Fin N ⊕ Fin (n - N)) GCTOcc.PolyR :=
    Matrix.fromBlocks (L.submatrix e.symm e.symm) 0 0 1
  let e2 : Fin N ⊕ Fin (n - N) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
  refine ⟨M.submatrix e2.symm e2.symm, ?_, ?_⟩
  · intro i j
    simp only [Matrix.submatrix_apply]
    generalize e2.symm i = a
    generalize e2.symm j = b
    rcases a with a | a <;> rcases b with b | b
    · simpa [M] using haff _ _
    · simp [M]
    · simp [M]
    · simp only [M, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      split_ifs <;> simp
  · rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
      Matrix.det_submatrix_equiv_self]

/-- Path edges inside the blocks. -/
noncomputable def sdN (k t : ℕ) (y : Fin k → Fin (t + 2) → GCTOcc.PolyR) :
    Matrix (Fin k × Fin (t + 1)) (Fin k × Fin (t + 1)) GCTOcc.PolyR :=
  fun x x' => if x'.1 = x.1 ∧ (x'.2 : ℕ) = x.2 + 1 then y x.1 (Fin.castSucc x'.2) else 0

noncomputable def sdV (k t : ℕ) (y : Fin k → Fin (t + 2) → GCTOcc.PolyR)
    (x : Fin k × Fin (t + 1)) : GCTOcc.PolyR :=
  ∏ l ∈ Finset.univ.filter (fun l : Fin (t + 2) => (x.2 : ℕ) < l), y x.1 l

noncomputable def sdC (k t : ℕ) (y : Fin k → Fin (t + 2) → GCTOcc.PolyR) :
    Matrix (Fin k × Fin (t + 1)) Unit GCTOcc.PolyR :=
  fun x _ => if x.2 = Fin.last t then y x.1 (Fin.last (t + 1)) else 0

noncomputable def sdB (k t : ℕ) (y : Fin k → Fin (t + 2) → GCTOcc.PolyR) :
    Matrix Unit (Fin k × Fin (t + 1)) GCTOcc.PolyR :=
  fun _ x => if x.2 = 0 then y x.1 0 else 0

theorem sd_D_mul_V (k t : ℕ) (y : Fin k → Fin (t + 2) → GCTOcc.PolyR) :
    (1 - sdN k t y) * (Matrix.of fun x (_ : Unit) => sdV k t y x) = sdC k t y := by
  classical
  refine Matrix.ext fun x u => ?_
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.mul_apply]
  by_cases h : (x.2 : ℕ) + 1 < t + 1
  · set x' : Fin k × Fin (t + 1) := (x.1, ⟨x.2 + 1, h⟩) with hx'
    rw [Finset.sum_eq_single x']
    · have hC : sdC k t y x u = 0 := by
        simp only [sdC]
        rw [if_neg]
        intro hl
        have := congrArg Fin.val hl
        simp at this
        omega
      rw [hC, sub_eq_zero]
      simp only [sdN, hx', and_self, if_true, Matrix.of_apply]
      have hset : Finset.univ.filter (fun l : Fin (t + 2) => (x.2 : ℕ) < l)
          = insert (Fin.castSucc (⟨x.2 + 1, h⟩ : Fin (t + 1)))
              (Finset.univ.filter (fun l : Fin (t + 2) => (x.2 : ℕ) + 1 < l)) := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hl
          by_cases hl2 : (x.2 : ℕ) + 1 < l
          · exact Or.inr hl2
          · left
            ext
            simp
            omega
        · rintro (hl | hl)
          · subst hl
            simp
          · omega
      simp only [sdV]
      rw [hset, Finset.prod_insert]
      simp
    · intro b _ hb
      simp only [sdN]
      rw [if_neg, zero_mul]
      rintro ⟨h1, h2⟩
      apply hb
      ext
      · simp [hx', h1]
      · simp [hx', h2]
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  · have hlast : x.2 = Fin.last t := by
      ext
      simp
      omega
    rw [Finset.sum_eq_zero]
    · simp only [sdC, sdV, hlast, if_true, sub_zero, Matrix.of_apply]
      have hset : Finset.univ.filter (fun l : Fin (t + 2) => ((Fin.last t : Fin (t + 1)) : ℕ) < l)
          = {Fin.last (t + 1)} := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Fin.val_last]
        constructor
        · intro hl
          ext
          simp
          omega
        · rintro rfl
          simp
      rw [hset, Finset.prod_singleton]
    · intro b _
      simp only [sdN]
      rw [if_neg, zero_mul]
      rintro ⟨_, h2⟩
      have := b.2.2
      omega

theorem sd_det_D (k t : ℕ) (y : Fin k → Fin (t + 2) → GCTOcc.PolyR) :
    (1 - sdN k t y).det = 1 := by
  classical
  have hbt : (1 - sdN k t y).BlockTriangular (fun x => x.2) := by
    intro x x' hlt
    simp only [Matrix.sub_apply, sdN]
    have hne : x ≠ x' := by
      rintro rfl
      exact lt_irrefl _ hlt
    rw [Matrix.one_apply_ne hne, if_neg]
    · simp
    · rintro ⟨_, h2⟩
      have : (x'.2 : ℕ) < x.2 := hlt
      omega
  rw [hbt.det]
  apply Finset.prod_eq_one
  intro a _
  have h1 : (1 - sdN k t y).toSquareBlock (fun x => x.2) a = 1 := by
    refine Matrix.ext fun ⟨x, hx⟩ ⟨x', hx'⟩ => ?_
    simp only [Matrix.toSquareBlock_def, Matrix.sub_apply, sdN, Matrix.of_apply]
    rw [if_neg]
    · simp only [sub_zero]
      by_cases hxx : x = x'
      · subst hxx
        simp
      · rw [Matrix.one_apply_ne hxx, Matrix.one_apply_ne]
        intro hh
        exact hxx (congrArg Subtype.val hh)
    · rintro ⟨_, h2⟩
      have hx2 : x.2 = a := hx
      have hx2' : x'.2 = a := hx'
      rw [hx2, hx2'] at h2
      omega
  rw [h1, Matrix.det_one]

theorem sd_totalDegree_ite {c : Prop} [Decidable c] (p : GCTOcc.PolyR) (hp : p.totalDegree ≤ 1) :
    (if c then p else 0).totalDegree ≤ 1 := by
  split_ifs
  · exact hp
  · simp

/-- Core: `a - Σ_i ∏_l y i l` is the determinant of an affine matrix of size `1 + k (t+1)`. -/
theorem sd_core (k t : ℕ) (a : GCTOcc.PolyR) (ha : a.totalDegree ≤ 1)
    (y : Fin k → Fin (t + 2) → GCTOcc.PolyR) (hy : ∀ i l, (y i l).totalDegree ≤ 1) :
    ∃ L : Matrix (Unit ⊕ (Fin k × Fin (t + 1))) (Unit ⊕ (Fin k × Fin (t + 1))) GCTOcc.PolyR,
      (∀ i j, (L i j).totalDegree ≤ 1) ∧ L.det = a - ∑ i, ∏ l, y i l := by
  classical
  refine ⟨Matrix.fromBlocks (Matrix.of fun _ _ => a) (sdB k t y) (sdC k t y) (1 - sdN k t y),
    ?_, ?_⟩
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · simpa using ha
    · simp only [Matrix.fromBlocks_apply₁₂, sdB]
      exact sd_totalDegree_ite _ (hy _ _)
    · simp only [Matrix.fromBlocks_apply₂₁, sdC]
      exact sd_totalDegree_ite _ (hy _ _)
    · simp only [Matrix.fromBlocks_apply₂₂, Matrix.sub_apply, sdN]
      refine (totalDegree_sub _ _).trans (max_le ?_ (sd_totalDegree_ite _ (hy _ _)))
      rw [Matrix.one_apply]
      split_ifs <;> simp
  · have hD := sd_det_D k t y
    letI : Invertible (1 - sdN k t y).det := hD ▸ invertibleOne
    letI : Invertible (1 - sdN k t y) := Matrix.invertibleOfDetInvertible _
    rw [Matrix.det_fromBlocks₂₂, hD, one_mul, Matrix.det_unique]
    have hV : ⅟(1 - sdN k t y) * sdC k t y = Matrix.of fun x (_ : Unit) => sdV k t y x := by
      rw [← sd_D_mul_V k t y, Matrix.invOf_mul_cancel_left]
    rw [Matrix.mul_assoc, hV, Matrix.sub_apply, Matrix.of_apply, Matrix.mul_apply]
    congr 1
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single (0 : Fin (t + 1))]
    · simp only [sdB, if_true, sdV, Matrix.of_apply, Fin.val_zero]
      rw [← Finset.mul_prod_erase Finset.univ (y i) (Finset.mem_univ (0 : Fin (t + 2)))]
      congr 1
      apply Finset.prod_congr _ (fun _ _ => rfl)
      ext l
      rw [Finset.mem_erase]
      constructor
      · intro hl
        have h2 : (0 : ℕ) < (l : ℕ) := (Finset.mem_filter.1 hl).2
        exact ⟨fun h0 => by subst h0; simp at h2, Finset.mem_univ _⟩
      · rintro ⟨hl, -⟩
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Nat.pos_of_ne_zero (fun h => hl (Fin.ext h))⟩
    · intro b _ hb
      simp [sdB, hb]
    · intro hh
      exact absurd (Finset.mem_univ _) hh

/-- Every monomial of degree `s` is a product of `s` variables. -/
theorem sd_factors (s : ℕ) : ∀ μ : (ℕ × ℕ) →₀ ℕ, Finsupp.degree μ = s →
    ∃ w : Fin s → ℕ × ℕ, ∏ j, (X (w j) : GCTOcc.PolyR) = monomial μ 1 := by
  induction s with
  | zero =>
    intro μ hμ
    have : μ = 0 := (Finsupp.degree_eq_zero_iff μ).1 hμ
    subst this
    exact ⟨Fin.elim0, by simp⟩
  | succ s ih =>
    intro μ hμ
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      simp at hμ
    obtain ⟨v, hv⟩ := Finsupp.support_nonempty_iff.2 hμ0
    have hle : Finsupp.single v 1 ≤ μ := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hv)
    set μ' := μ - Finsupp.single v 1 with hμ'
    have hsplit : μ = Finsupp.single v 1 + μ' := (add_tsub_cancel_of_le hle).symm
    have hdeg : Finsupp.degree μ' = s := by
      have h1 := congrArg Finsupp.degree hsplit
      rw [map_add, Finsupp.degree_single, hμ] at h1
      omega
    obtain ⟨w', hw'⟩ := ih μ' hdeg
    refine ⟨Fin.cons v w', ?_⟩
    rw [Fin.prod_univ_succ, Fin.cons_zero]
    simp only [Fin.cons_succ]
    rw [hw', hsplit, monomial_single_add, pow_one]

open GCTOcc in
/-- G2-iii-b. -/
theorem symbolicDet_of_few_monomials (n s : ℕ) (hn : 1 ≤ n) (f : PolyR)
    (hf : ∀ μ ∈ f.support, Finsupp.degree μ = s) (hcard : f.support.card * s ≤ n) :
    IsSymbolicDet f n := by
  classical
  rcases Nat.lt_or_ge s 2 with hs | hs
  · -- affine: a `1 × 1` matrix
    have hdeg : f.totalDegree ≤ 1 := by
      rw [totalDegree]
      apply Finset.sup_le
      intro μ hμ
      have h1 := hf μ hμ
      rw [Finsupp.degree_apply] at h1
      show (μ.sum fun _ e => e) ≤ 1
      unfold Finsupp.sum
      change (∑ a ∈ μ.support, μ a) ≤ 1
      omega
    have := sd_pad n (Matrix.of fun (_ : Unit) (_ : Unit) => f) (fun _ _ => by simpa using hdeg)
      (by simpa using hn)
    simpa [Matrix.det_unique] using this
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
  set k := f.support.card with hk
  let e : f.support ≃ Fin k := f.support.equivFin
  let μ : Fin k → (ℕ × ℕ) →₀ ℕ := fun i => (e.symm i).1
  have hμ : ∀ i, Finsupp.degree (μ i) = t + 2 := fun i => hf _ (e.symm i).2
  choose w hw using fun i => sd_factors (t + 2) (μ i) (hμ i)
  let y : Fin k → Fin (t + 2) → PolyR := fun i l =>
    (if l = 0 then -C (coeff (μ i) f) else 1) * X (w i l)
  have hy : ∀ i l, (y i l).totalDegree ≤ 1 := by
    intro i l
    simp only [y]
    split_ifs
    · refine (totalDegree_mul _ _).trans ?_
      simp
    · simp
  obtain ⟨L, hL, hdet⟩ := sd_core k t 0 (by simp) y hy
  have hval : (0 : PolyR) - ∑ i, ∏ l, y i l = f := by
    have hprod : ∀ i, ∏ l, y i l = -monomial (μ i) (coeff (μ i) f) := by
      intro i
      simp only [y]
      rw [Finset.prod_mul_distrib, hw i, Finset.prod_ite_eq' Finset.univ (0 : Fin (t + 2))]
      simp only [Finset.mem_univ, if_true]
      rw [neg_mul, C_mul_monomial, mul_one]
    simp only [hprod, Finset.sum_neg_distrib, sub_neg_eq_add, zero_add]
    conv_rhs => rw [f.as_sum]
    rw [← Finset.sum_coe_sort f.support]
    exact Fintype.sum_equiv e.symm _ _ (fun i => rfl)
  rw [← hval, ← hdet]
  apply sd_pad n L hL
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_prod, Fintype.card_fin]
  have h2 : k * (t + 2) = k * (t + 1) + k := by ring
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rw [hk0]
    omega
  · omega



open MvPolynomial

/-! G3 (a3397022 row_extended_rectangle_occurs), part A: Cayley's hyperdeterminant. -/

/-- Cayley's combinatorial hyperdeterminant of an `l`-tensor over `Fin k`. -/
noncomputable def g3hd {R : Type} [CommRing R] (k l : ℕ) (T : (Fin l → Fin k) → R) : R :=
  ∑ π : Fin l → Equiv.Perm (Fin k),
    (((∏ t, (Equiv.Perm.sign (π t) : ℤ)) : ℤ) : R) * ∏ j : Fin k, T (fun t => π t j)

theorem g3_det_submatrix_eq {R : Type} [CommRing R] (k : ℕ) (G : Matrix (Fin k) (Fin k) R)
    (c : Fin k → Fin k) :
    (G.submatrix c id).det =
      ∑ σ : Equiv.Perm (Fin k),
        if (⇑σ = c) then ((Equiv.Perm.sign σ : ℤ) : R) * G.det else 0 := by
  classical
  by_cases hc : Function.Injective c
  · have hb : Function.Bijective c := Finite.injective_iff_bijective.1 hc
    have hσ0 : (⇑(Equiv.ofBijective c hb) : Fin k → Fin k) = c := rfl
    rw [Finset.sum_eq_single (Equiv.ofBijective c hb)]
    · rw [if_pos hσ0]
      conv_lhs => rw [← hσ0]
      rw [Matrix.det_permute]
    · intro σ _ hne
      rw [if_neg]
      intro h
      apply hne
      apply Equiv.ext
      intro x
      rw [h, hσ0]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have : ∃ i j, i ≠ j ∧ c i = c j := by
      by_contra hcon
      push Not at hcon
      exact hc (fun i j h => by
        by_contra hne
        exact hcon i j hne h)
    obtain ⟨i, j, hij, hcij⟩ := this
    rw [Matrix.det_zero_of_row_eq hij]
    · symm
      apply Finset.sum_eq_zero
      intro σ _
      rw [if_neg]
      intro h
      apply hij
      apply σ.injective
      rw [h]
      exact hcij
    · ext x
      simp [Matrix.submatrix_apply, hcij]

theorem g3_inner {R : Type} [CommRing R] (k : ℕ) (G : Matrix (Fin k) (Fin k) R)
    (c : Fin k → Fin k) :
    (∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : R) * ∏ j, G (c j) (σ j)) =
      ∑ σ : Equiv.Perm (Fin k),
        if (⇑σ = c) then ((Equiv.Perm.sign σ : ℤ) : R) * G.det else 0 := by
  rw [← g3_det_submatrix_eq, ← Matrix.det_transpose, Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [Matrix.transpose_apply, Matrix.submatrix_apply]

theorem g3_perA {R : Type} [CommRing R] (k l : ℕ) (G : Matrix (Fin k) (Fin k) R)
    (A : Fin k → Fin l → Fin k) :
    (∑ π : Fin l → Equiv.Perm (Fin k),
        (((∏ t, (Equiv.Perm.sign (π t) : ℤ)) : ℤ) : R) * ∏ t, ∏ j, G (A j t) (π t j)) =
      ∑ π : Fin l → Equiv.Perm (Fin k),
        if A = (fun j t => π t j) then
          (((∏ t, (Equiv.Perm.sign (π t) : ℤ)) : ℤ) : R) * G.det ^ l else 0 := by
  classical
  have h1 : ∀ π : Fin l → Equiv.Perm (Fin k),
      (((∏ t, (Equiv.Perm.sign (π t) : ℤ)) : ℤ) : R) * ∏ t, ∏ j, G (A j t) (π t j) =
        ∏ t, (((Equiv.Perm.sign (π t) : ℤ) : R) * ∏ j, G (A j t) (π t j)) := by
    intro π
    rw [Int.cast_prod, ← Finset.prod_mul_distrib]
  simp_rw [h1]
  have h2 := (Finset.prod_univ_sum (fun _ : Fin l => (Finset.univ : Finset (Equiv.Perm (Fin k))))
    (fun t σ => ((Equiv.Perm.sign σ : ℤ) : R) * ∏ j, G (A j t) (σ j)))
  rw [Fintype.piFinset_univ] at h2
  rw [← h2]
  simp_rw [g3_inner]
  have h3 := (Finset.prod_univ_sum (fun _ : Fin l => (Finset.univ : Finset (Equiv.Perm (Fin k))))
    (fun t σ => if (⇑σ = fun j => A j t) then ((Equiv.Perm.sign σ : ℤ) : R) * G.det else 0))
  rw [Fintype.piFinset_univ] at h3
  rw [h3]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Fintype.prod_ite_zero]
  have hiff : (∀ t, (⇑(π t) = fun j => A j t)) ↔ A = (fun j t => π t j) := by
    constructor
    · intro h
      funext j t
      exact (congrFun (h t) j).symm
    · intro h t
      funext j
      rw [h]
  by_cases hA : A = (fun j t => π t j)
  · rw [if_pos (hiff.2 hA), if_pos hA, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Int.cast_prod]
  · rw [if_neg (fun h => hA (hiff.1 h)), if_neg hA]

theorem g3_hd_transform {R : Type} [CommRing R] (k l : ℕ) (G : Matrix (Fin k) (Fin k) R)
    (T : (Fin l → Fin k) → R) :
    g3hd k l (fun s => ∑ a : Fin l → Fin k, (∏ t, G (a t) (s t)) * T a) = G.det ^ l * g3hd k l T := by
  classical
  unfold g3hd
  have step : ∀ π : Fin l → Equiv.Perm (Fin k),
      ∏ j : Fin k, ∑ a : Fin l → Fin k, (∏ t, G (a t) (π t j)) * T a =
      ∑ A : Fin k → Fin l → Fin k, (∏ t, ∏ j, G (A j t) (π t j)) * ∏ j, T (A j) := by
    intro π
    rw [Finset.prod_univ_sum (fun _ => Finset.univ) (fun j a => (∏ t, G (a t) (π t j)) * T a),
      Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_comm]
  simp only [step]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h4 : ∀ A : Fin k → Fin l → Fin k,
      (∑ π : Fin l → Equiv.Perm (Fin k),
        (((∏ t, (Equiv.Perm.sign (π t) : ℤ)) : ℤ) : R) * ((∏ t, ∏ j, G (A j t) (π t j)) *
          ∏ j, T (A j))) =
      ∑ π : Fin l → Equiv.Perm (Fin k),
        (if A = (fun j t => π t j) then
          (((∏ t, (Equiv.Perm.sign (π t) : ℤ)) : ℤ) : R) * G.det ^ l else 0) * ∏ j, T (A j) := by
    intro A
    rw [← Finset.sum_mul, ← g3_perA, Finset.sum_mul]
    refine Finset.sum_congr rfl fun π _ => ?_
    ring
  simp only [h4]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  ring

/-! G3 part B -/

/-- iterated partial derivative along the variables `(0, s t)`. -/
noncomputable def g3D (k : ℕ) : (l : ℕ) → (Fin l → Fin k) → GCTOcc.PolyR → GCTOcc.PolyR
  | 0, _, p => p
  | l + 1, s, p => pderiv ((0 : ℕ), ((s 0 : Fin k) : ℕ)) (g3D k l (Fin.tail s) p)

/-- the weight factor produced by `g3D` on a coefficient. -/
noncomputable def g3w (k : ℕ) : (l : ℕ) → (Fin l → Fin k) → ((ℕ × ℕ) →₀ ℕ) → ℂ
  | 0, _, _ => 1
  | l + 1, s, m => ((m ((0 : ℕ), ((s 0 : Fin k) : ℕ)) : ℂ) + 1) *
      g3w k l (Fin.tail s) (m + Finsupp.single ((0 : ℕ), ((s 0 : Fin k) : ℕ)) 1)

/-- the exponent shift produced by `g3D`. -/
noncomputable def g3S (k l : ℕ) (s : Fin l → Fin k) : (ℕ × ℕ) →₀ ℕ :=
  ∑ t, Finsupp.single ((0 : ℕ), ((s t : Fin k) : ℕ)) 1

theorem g3S_succ (k l : ℕ) (s : Fin (l + 1) → Fin k) :
    g3S k (l + 1) s = Finsupp.single ((0 : ℕ), ((s 0 : Fin k) : ℕ)) 1 + g3S k l (Fin.tail s) := by
  unfold g3S
  rw [Fin.sum_univ_succ]
  rfl

theorem g3_coeff_D (k : ℕ) : ∀ (l : ℕ) (s : Fin l → Fin k) (p : GCTOcc.PolyR) (m : (ℕ × ℕ) →₀ ℕ),
    coeff m (g3D k l s p) = g3w k l s m * coeff (m + g3S k l s) p := by
  intro l
  induction l with
  | zero =>
    intro s p m
    simp [g3D, g3w, g3S]
  | succ l ih =>
    intro s p m
    rw [g3D, coeff_pderiv, ih, g3w, g3S_succ, add_assoc]
    ring

theorem g3w_ne_zero (k : ℕ) : ∀ (l : ℕ) (s : Fin l → Fin k) (m : (ℕ × ℕ) →₀ ℕ), g3w k l s m ≠ 0 := by
  intro l
  induction l with
  | zero => intro s m; simp [g3w]
  | succ l ih =>
    intro s m
    rw [g3w]
    exact mul_ne_zero (Nat.cast_add_one_ne_zero _) (ih _ _)

theorem g3_D_homog (k n : ℕ) : ∀ (l : ℕ) (s : Fin l → Fin k) (p : GCTOcc.PolyR),
    p.IsHomogeneous n → (g3D k l s p).IsHomogeneous (n - l) := by
  intro l
  induction l with
  | zero => intro s p hp; simpa [g3D] using hp
  | succ l ih =>
    intro s p hp
    rw [g3D]
    have := (ih (Fin.tail s) p hp).pderiv (i := ((0 : ℕ), ((s 0 : Fin k) : ℕ)))
    rwa [Nat.sub_sub] at this

/-- kill every variable except `X (0,0)`. -/
noncomputable def g3phi : GCTOcc.PolyR →ₐ[ℂ] GCTOcc.PolyR :=
  aeval (fun v : ℕ × ℕ => if v = (0, 0) then X (0, 0) else 0)

theorem g3phi_monomial (m : (ℕ × ℕ) →₀ ℕ) (c : ℂ) :
    g3phi (monomial m c) =
      if m = Finsupp.single (0, 0) (m (0, 0)) then monomial m c else 0 := by
  classical
  rw [g3phi, aeval_monomial]
  split_ifs with h
  · generalize ha : m (0, 0) = a at h
    subst h
    rw [Finsupp.prod_single_index (by simp), if_pos rfl, ← C_mul_X_pow_eq_monomial]
    rfl
  · have hv : ∃ v ∈ m.support, v ≠ (0, 0) := by
      by_contra hcon
      push Not at hcon
      apply h
      ext w
      by_cases hw : w = (0, 0)
      · subst hw; simp
      · rw [Finsupp.single_apply, if_neg (Ne.symm hw)]
        by_contra hmw
        exact hw (hcon w (Finsupp.mem_support_iff.2 hmw))
    obtain ⟨v, hvs, hv0⟩ := hv
    rw [Finsupp.prod, Finset.prod_eq_zero hvs, mul_zero]
    rw [if_neg hv0]
    exact zero_pow (Finsupp.mem_support_iff.1 hvs)

theorem g3_weight_eq (μ : (ℕ × ℕ) →₀ ℕ) : Finsupp.weight 1 μ = μ.sum fun _ k => k := by
  simp [Finsupp.weight_apply, Finsupp.sum]

theorem g3phi_homog (N : ℕ) (H : GCTOcc.PolyR) (hH : H.IsHomogeneous N) :
    g3phi H = C (coeff (Finsupp.single (0, 0) N) H) * X (0, 0) ^ N := by
  classical
  conv_lhs => rw [H.as_sum]
  rw [map_sum]
  simp_rw [g3phi_monomial]
  have hcond : ∀ m ∈ H.support,
      (m = Finsupp.single (0, 0) (m (0, 0))) ↔ m = Finsupp.single (0, 0) N := by
    intro m hm
    have hdeg := hH (mem_support_iff.1 hm)
    rw [g3_weight_eq] at hdeg
    constructor
    · intro h
      have : m (0, 0) = N := by
        rw [← hdeg, h, Finsupp.sum_single_index rfl]
        simp
      rw [h, this]
    · intro h
      rw [h]
      simp
  rw [Finset.sum_congr rfl (fun m hm => by rw [if_congr (hcond m hm) rfl rfl])]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rw [C_mul_X_pow_eq_monomial]
  · rw [notMem_support_iff.1 h, C_0, zero_mul]

theorem g3_coeff_C_mul_X_pow (a : ℂ) (N : ℕ) :
    coeff (Finsupp.single (0, 0) N) (C a * X (0, 0) ^ N : GCTOcc.PolyR) = a := by
  rw [C_mul_X_pow_eq_monomial, coeff_monomial, if_pos rfl]

theorem g3_coeff_prod (k e : ℕ) (H : Fin k → GCTOcc.PolyR) (hH : ∀ j, (H j).IsHomogeneous e) :
    coeff (Finsupp.single (0, 0) (k * e)) (∏ j, H j) = ∏ j, coeff (Finsupp.single (0, 0) e) (H j) := by
  classical
  have hP : (∏ j, H j).IsHomogeneous (k * e) := by
    have := IsHomogeneous.prod Finset.univ H (fun _ => e) (fun j _ => hH j)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using this
  have h1 := g3phi_homog (k * e) _ hP
  have h2 : g3phi (∏ j, H j) = C (∏ j, coeff (Finsupp.single (0, 0) e) (H j)) * X (0, 0) ^ (k * e) := by
    rw [map_prod]
    simp_rw [g3phi_homog e _ (hH _)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_prod,
      ← pow_mul, mul_comm e k]
  have := congrArg (coeff (Finsupp.single (0, 0) (k * e))) (h1.symm.trans h2)
  rwa [g3_coeff_C_mul_X_pow, g3_coeff_C_mul_X_pow] at this

/-- `substLin` as an algebra map. -/
noncomputable def g3SL (n : ℕ) (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    GCTOcc.PolyR →ₐ[ℂ] GCTOcc.PolyR :=
  aeval (fun v : ℕ × ℕ =>
    if h : v.1 < n ∧ v.2 < n then
      ∑ w : Fin n × Fin n,
        C (g (⟨v.1, h.1⟩, ⟨v.2, h.2⟩) w) * X (((w.1 : ℕ)), ((w.2 : ℕ)))
    else X v)

theorem g3SL_eq (n : ℕ) (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (p : GCTOcc.PolyR) :
    GCTOcc.substLin n g p = g3SL n g p := rfl

theorem g3SL_X_block (n : ℕ) (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (a : Fin n × Fin n) :
    g3SL n g (X ((a.1 : ℕ), (a.2 : ℕ))) =
      ∑ w : Fin n × Fin n, C (g a w) * X (((w.1 : ℕ)), ((w.2 : ℕ))) := by
  simp [g3SL, a.1.isLt, a.2.isLt]

theorem g3SL_X_nonblock (n : ℕ) (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (a : ℕ × ℕ)
    (ha : ¬ (a.1 < n ∧ a.2 < n)) : g3SL n g (X a) = X a := by
  simp [g3SL, dif_neg ha]

theorem g3SL_homog (n N : ℕ) (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (H : GCTOcc.PolyR)
    (hH : H.IsHomogeneous N) : (g3SL n g H).IsHomogeneous N := by
  have := hH.aeval (S := ℂ) (n := 1)
    (fun v : ℕ × ℕ => if h : v.1 < n ∧ v.2 < n then
      ∑ w : Fin n × Fin n, C (g (⟨v.1, h.1⟩, ⟨v.2, h.2⟩) w) * X (((w.1 : ℕ)), ((w.2 : ℕ)))
      else X v) ?_
  · simpa [g3SL] using this
  · intro v
    by_cases hv : v.1 < n ∧ v.2 < n
    · simp only [dif_pos hv]
      exact IsHomogeneous.sum _ _ _ (fun w _ => (isHomogeneous_C_mul_X _ _))
    · simp only [dif_neg hv]
      exact isHomogeneous_X _ _

theorem g3_top_substLin (n N : ℕ) (hn : 0 < n) (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hg : GCTOcc.IsUpperTri n g) (H : GCTOcc.PolyR) (hH : H.IsHomogeneous N) :
    coeff (Finsupp.single (0, 0) N) (g3SL n g H) =
      g (⟨0, hn⟩, ⟨0, hn⟩) (⟨0, hn⟩, ⟨0, hn⟩) ^ N * coeff (Finsupp.single (0, 0) N) H := by
  classical
  set g00 := g (⟨0, hn⟩, ⟨0, hn⟩) (⟨0, hn⟩, ⟨0, hn⟩) with hg00
  let ψ : GCTOcc.PolyR →ₐ[ℂ] GCTOcc.PolyR :=
    aeval (fun v : ℕ × ℕ => if v = (0, 0) then C g00 * X (0, 0) else 0)
  have hcomm : g3phi.comp (g3SL n g) = ψ.comp g3phi := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply]
    by_cases hv : v.1 < n ∧ v.2 < n
    · have hvx : v = (((⟨v.1, hv.1⟩ : Fin n) : ℕ), ((⟨v.2, hv.2⟩ : Fin n) : ℕ)) := rfl
      rw [hvx, g3SL_X_block n g (⟨v.1, hv.1⟩, ⟨v.2, hv.2⟩)]
      rw [map_sum]
      simp only [map_mul, g3phi, aeval_C, aeval_X, algebraMap_eq]
      rw [Finset.sum_eq_single (⟨0, hn⟩, ⟨0, hn⟩)]
      · simp only [ψ, aeval_X, if_pos rfl]
        by_cases h0 : v = (0, 0)
        · have h1 : v.1 = 0 := by rw [h0]
          have h2 : v.2 = 0 := by rw [h0]
          have he : ((⟨v.1, hv.1⟩ : Fin n), (⟨v.2, hv.2⟩ : Fin n)) = (⟨0, hn⟩, ⟨0, hn⟩) := by
            ext <;> simp [h1, h2]
          rw [he]
          simp [h0, g00]
        · have hidx : GCTOcc.idx n (⟨0, hn⟩, ⟨0, hn⟩) <
              GCTOcc.idx n ((⟨v.1, hv.1⟩ : Fin n), (⟨v.2, hv.2⟩ : Fin n)) := by
            unfold GCTOcc.idx
            simp only
            rcases Nat.eq_zero_or_pos v.1 with h1 | h1
            · have h2 : v.2 ≠ 0 := by
                intro h2; apply h0; ext <;> simp [h1, h2]
              rw [h1]; simp; omega
            · have : n ≤ v.1 * n := Nat.le_mul_of_pos_left n h1
              omega
          rw [hg _ _ hidx]
          have : ¬ ((v.1, v.2) = ((0 : ℕ), (0 : ℕ))) := by
            intro h; apply h0; exact h
          simp [this]
      · intro w _ hw
        have : ¬ (((w.1 : ℕ), (w.2 : ℕ)) = ((0 : ℕ), (0 : ℕ))) := by
          intro h
          apply hw
          simp only [Prod.mk.injEq] at h
          ext
          · simp [h.1]
          · simp [h.2]
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [g3SL_X_nonblock n g v hv]
      have h0 : v ≠ (0, 0) := by
        intro h; apply hv; rw [h]; exact ⟨hn, hn⟩
      simp [g3phi, ψ, h0]
  have hSH := g3SL_homog n N g H hH
  have e1 := g3phi_homog N _ hSH
  have e2 : g3phi (g3SL n g H) = ψ (g3phi H) := by
    rw [← AlgHom.comp_apply, hcomm, AlgHom.comp_apply]
  rw [e2, g3phi_homog N H hH] at e1
  have e3 : ψ (C (coeff (Finsupp.single (0, 0) N) H) * X (0, 0) ^ N) =
      C (g00 ^ N * coeff (Finsupp.single (0, 0) N) H) * X (0, 0) ^ N := by
    simp only [ψ, map_mul, map_pow, aeval_C, aeval_X, algebraMap_eq, ite_true, if_true, mul_pow,
      C_pow]
    ring
  rw [e3] at e1
  have := congrArg (coeff (Finsupp.single (0, 0) N)) e1
  rw [g3_coeff_C_mul_X_pow, g3_coeff_C_mul_X_pow] at this
  exact this.symm

/-- chain rule for `substLin` along a block variable. -/
theorem g3_pderiv_SL (n : ℕ) (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (u : Fin n × Fin n)
    (p : GCTOcc.PolyR) :
    pderiv ((u.1 : ℕ), (u.2 : ℕ)) (g3SL n g p) =
      ∑ v : Fin n × Fin n, C (g v u) * g3SL n g (pderiv ((v.1 : ℕ), (v.2 : ℕ)) p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p a hp =>
    have hX : pderiv ((u.1 : ℕ), (u.2 : ℕ)) (g3SL n g (X a)) =
        ∑ v : Fin n × Fin n, C (g v u) * g3SL n g (pderiv ((v.1 : ℕ), (v.2 : ℕ)) (X a)) := by
      by_cases ha : a.1 < n ∧ a.2 < n
      · have hax : a = (((⟨a.1, ha.1⟩ : Fin n) : ℕ), ((⟨a.2, ha.2⟩ : Fin n) : ℕ)) := rfl
        rw [hax, g3SL_X_block n g (⟨a.1, ha.1⟩, ⟨a.2, ha.2⟩)]
        simp only [map_sum, pderiv_C_mul, pderiv_X, Pi.single_apply]
        rw [Finset.sum_eq_single u, Finset.sum_eq_single (⟨a.1, ha.1⟩, ⟨a.2, ha.2⟩)]
        · simp
        · intro v _ hv
          have : ¬ ((((⟨a.1, ha.1⟩ : Fin n) : ℕ), ((⟨a.2, ha.2⟩ : Fin n) : ℕ)) =
              ((v.1 : ℕ), (v.2 : ℕ))) := by
            intro h
            apply hv
            simp only [Prod.mk.injEq] at h
            ext
            · simp [h.1]
            · simp [h.2]
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h
        · intro w _ hw
          have : ¬ (((w.1 : ℕ), (w.2 : ℕ)) = ((u.1 : ℕ), (u.2 : ℕ))) := by
            intro h
            apply hw
            simp only [Prod.mk.injEq] at h
            ext
            · exact h.1
            · exact h.2
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [g3SL_X_nonblock n g a ha]
        have hne : ∀ v : Fin n × Fin n, a ≠ ((v.1 : ℕ), (v.2 : ℕ)) := by
          intro v h
          apply ha
          rw [h]
          exact ⟨v.1.isLt, v.2.isLt⟩
        simp only [pderiv_X, Pi.single_apply, if_neg (hne u)]
        symm
        apply Finset.sum_eq_zero
        intro v _
        simp [hne v]
    rw [map_mul, Derivation.leibniz, hp, hX, smul_eq_mul, smul_eq_mul, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
    ring

/-! G3 part C: restriction to the first `k` variables, covariance, the HWV. -/

/-- the embedding of `Fin k` into the first row of variables. -/
def g3e (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) (b : Fin k) : Fin n × Fin n :=
  (⟨0, hn⟩, ⟨b, lt_of_lt_of_le b.2 hk⟩)

theorem g3e_idx (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) (b : Fin k) :
    GCTOcc.idx n (g3e n k hn hk b) = b := by
  simp [GCTOcc.idx, g3e]

theorem g3e_inj (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) : Function.Injective (g3e n k hn hk) := by
  intro a b h
  have := congrArg (fun v : Fin n × Fin n => (v.2 : ℕ)) h
  simp only [g3e] at this
  exact Fin.ext this

theorem g3e_le_idx (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) (v : Fin n × Fin n)
    (hv : v ∉ Set.range (g3e n k hn hk)) : k ≤ GCTOcc.idx n v := by
  by_contra hlt
  push Not at hlt
  apply hv
  unfold GCTOcc.idx at hlt
  have h1 : (v.1 : ℕ) = 0 := by
    by_contra h1
    have : n ≤ (v.1 : ℕ) * n := Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero h1)
    omega
  have h2 : (v.2 : ℕ) < k := by rw [h1] at hlt; simpa using hlt
  refine ⟨⟨v.2, h2⟩, ?_⟩
  ext
  · simp [g3e, h1]
  · simp [g3e]

theorem g3_pderiv_SL_k (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)
    (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hg : GCTOcc.IsUpperTri n g) (i : Fin k)
    (p : GCTOcc.PolyR) :
    pderiv ((0 : ℕ), ((i : Fin k) : ℕ)) (g3SL n g p) =
      ∑ b : Fin k, C (g (g3e n k hn hk b) (g3e n k hn hk i)) *
        g3SL n g (pderiv ((0 : ℕ), ((b : Fin k) : ℕ)) p) := by
  have h := g3_pderiv_SL n g (g3e n k hn hk i) p
  rw [show ((0 : ℕ), ((i : Fin k) : ℕ)) =
    ((((g3e n k hn hk i).1 : Fin n) : ℕ), (((g3e n k hn hk i).2 : Fin n) : ℕ)) from rfl, h]
  symm
  refine Fintype.sum_of_injective (g3e n k hn hk) (g3e_inj n k hn hk) _ _ ?_ (fun b => rfl)
  intro v hv
  have hkv := g3e_le_idx n k hn hk v hv
  have hlt : GCTOcc.idx n (g3e n k hn hk i) < GCTOcc.idx n v := by
    rw [g3e_idx]; omega
  rw [hg _ _ hlt, C_0, zero_mul]

theorem g3_D_SL (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)
    (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hg : GCTOcc.IsUpperTri n g) :
    ∀ (l : ℕ) (s : Fin l → Fin k) (p : GCTOcc.PolyR),
    g3D k l s (g3SL n g p) = ∑ a : Fin l → Fin k,
      C (∏ t, g (g3e n k hn hk (a t)) (g3e n k hn hk (s t))) * g3SL n g (g3D k l a p) := by
  intro l
  induction l with
  | zero =>
    intro s p
    simp [g3D]
  | succ l ih =>
    intro s p
    rw [g3D, ih, map_sum]
    simp_rw [pderiv_C_mul, g3_pderiv_SL_k n k hn hk g hg, Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [← (Fin.consEquiv (fun _ : Fin (l + 1) => Fin k)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      g3D, Fin.tail_cons, Fin.tail]
    rw [map_mul]
    ring

/-- the `k × k` block of `g` on the variables `(0, i)`. -/
noncomputable def g3Gm (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)
    (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun b i => g (g3e n k hn hk b) (g3e n k hn hk i)

theorem g3_hd_D_SL (n k l : ℕ) (hn : 0 < n) (hk : k ≤ n)
    (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hg : GCTOcc.IsUpperTri n g)
    (p : GCTOcc.PolyR) :
    g3hd k l (fun s => g3D k l s (g3SL n g p)) =
      C ((g3Gm n k hn hk g).det ^ l) * g3SL n g (g3hd k l (fun s => g3D k l s p)) := by
  have h1 : (fun s => g3D k l s (g3SL n g p)) = fun s => ∑ a : Fin l → Fin k,
      (∏ t, ((g3Gm n k hn hk g).map C) (a t) (s t)) * g3SL n g (g3D k l a p) := by
    funext s
    rw [g3_D_SL n k hn hk g hg]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_prod]
    rfl
  rw [h1, g3_hd_transform]
  have h2 : ((g3Gm n k hn hk g).map (C : ℂ →+* GCTOcc.PolyR)).det =
      (C : ℂ →+* GCTOcc.PolyR) (g3Gm n k hn hk g).det := by
    rw [RingHom.map_det]
    rfl
  rw [h2, ← map_pow]
  congr 1
  unfold g3hd
  rw [map_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [map_mul, map_prod, map_intCast]

theorem g3_hd_homog (n k l : ℕ) (p : GCTOcc.PolyR) (hp : p.IsHomogeneous n) :
    (g3hd k l (fun s => g3D k l s p)).IsHomogeneous (k * (n - l)) := by
  unfold g3hd
  apply IsHomogeneous.sum
  intro π _
  have h0 : ((((∏ t, (Equiv.Perm.sign (π t) : ℤ)) : ℤ) : GCTOcc.PolyR)).IsHomogeneous 0 := by
    rw [← map_intCast (C : ℂ →+* GCTOcc.PolyR)]
    exact isHomogeneous_C _ _
  have := h0.mul (IsHomogeneous.prod (Finset.univ : Finset (Fin k))
    (fun j => g3D k l (fun t => π t j) p) (fun _ => n - l)
    (fun j _ => g3_D_homog k n l _ p hp))
  simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using this

/-- The highest weight vector for the row-extended rectangle. -/
noncomputable def g3F (n k l : ℕ) : GCTOcc.CoordRing :=
  ∑ π : Fin l → Equiv.Perm (Fin k),
    C ((((∏ t, (Equiv.Perm.sign (π t) : ℤ)) : ℤ) : ℂ)) *
      ∏ j : Fin k, (C (g3w k l (fun t => π t j) (Finsupp.single (0, 0) (n - l))) *
        X (Finsupp.single (0, 0) (n - l) + g3S k l (fun t => π t j)))

theorem g3_eval_F (n k l : ℕ) (p : GCTOcc.PolyR) (hp : p.IsHomogeneous n) :
    GCTOcc.evalCoeff p (g3F n k l) =
      coeff (Finsupp.single (0, 0) (k * (n - l))) (g3hd k l (fun s => g3D k l s p)) := by
  unfold GCTOcc.evalCoeff g3F g3hd
  rw [coeff_sum, map_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← map_intCast (C : ℂ →+* GCTOcc.PolyR), coeff_C_mul,
    g3_coeff_prod k (n - l) _ (fun j => g3_D_homog k n l _ p hp)]
  simp only [map_mul, map_prod, eval_C, eval_X]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [g3_coeff_D]

theorem g3_weight (n k l : ℕ) (hk1 : 1 ≤ k) (hn : 0 < n) (hk : k ≤ n)
    (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hg : GCTOcc.IsUpperTri n g) :
    (g3Gm n k hn hk g).det ^ l * g (⟨0, hn⟩, ⟨0, hn⟩) (⟨0, hn⟩, ⟨0, hn⟩) ^ (k * (n - l)) =
      ∏ v : Fin n × Fin n, (g v v) ^
        ((fun i => if i = 0 then l + (n * k - k * l) else if i < k then l else 0) (GCTOcc.idx n v)) := by
  classical
  set lam : ℕ → ℕ := fun i => if i = 0 then l + (n * k - k * l) else if i < k then l else 0
    with hlam
  have hdet : (g3Gm n k hn hk g).det = ∏ i, g (g3e n k hn hk i) (g3e n k hn hk i) := by
    rw [Matrix.det_of_isUpperTriangular]
    · rfl
    · intro i j hij
      show g (g3e n k hn hk i) (g3e n k hn hk j) = 0
      apply hg
      rw [g3e_idx, g3e_idx]
      exact hij
  have hprod : ∏ v : Fin n × Fin n, (g v v) ^ lam (GCTOcc.idx n v) =
      ∏ i : Fin k, (g (g3e n k hn hk i) (g3e n k hn hk i)) ^ lam i := by
    symm
    refine Fintype.prod_of_injective (g3e n k hn hk) (g3e_inj n k hn hk) _ _ ?_ ?_
    · intro v hv
      have hkv := g3e_le_idx n k hn hk v hv
      have : lam (GCTOcc.idx n v) = 0 := by
        rw [hlam]
        simp only
        rw [if_neg (by omega), if_neg (by omega)]
      rw [this, pow_zero]
    · intro i
      rw [g3e_idx]
  rw [hprod, hdet]
  have hN : k * (n - l) = n * k - k * l := by
    rw [mul_tsub, mul_comm k n]
  have hterm : ∀ i : Fin k, (g (g3e n k hn hk i) (g3e n k hn hk i)) ^ lam i =
      (g (g3e n k hn hk i) (g3e n k hn hk i)) ^ l *
        (if (i : ℕ) = 0 then (g (g3e n k hn hk i) (g3e n k hn hk i)) ^ (n * k - k * l) else 1) := by
    intro i
    rw [hlam]
    simp only
    by_cases hi : (i : ℕ) = 0
    · rw [if_pos hi, if_pos hi, pow_add]
    · rw [if_neg hi, if_pos i.isLt, if_neg hi, mul_one]
  have hite : ∏ i : Fin k, (if (i : ℕ) = 0 then
      (g (g3e n k hn hk i) (g3e n k hn hk i)) ^ (n * k - k * l) else 1) =
      g (⟨0, hn⟩, ⟨0, hn⟩) (⟨0, hn⟩, ⟨0, hn⟩) ^ (n * k - k * l) := by
    rw [Finset.prod_eq_single (⟨0, hk1⟩ : Fin k)]
    · rw [if_pos rfl]
      rfl
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Fin.ext h)
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.prod_congr rfl (fun i _ => hterm i), Finset.prod_mul_distrib, Finset.prod_pow, hite, hN]

theorem g3_hwv (n k l : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ n) :
    GCTOcc.IsHWV n k (fun i => if i = 0 then l + (n * k - k * l) else if i < k then l else 0)
      (g3F n k l) := by
  have hn : 0 < n := by omega
  refine ⟨?_, ?_⟩
  · unfold g3F
    apply IsHomogeneous.sum
    intro π _
    have := (isHomogeneous_C (σ := (ℕ × ℕ) →₀ ℕ) (R := ℂ)
        ((((∏ t, (Equiv.Perm.sign (π t) : ℤ)) : ℤ) : ℂ))).mul
      (IsHomogeneous.prod (Finset.univ : Finset (Fin k))
        (fun j => (C (g3w k l (fun t => π t j) (Finsupp.single (0, 0) (n - l))) *
          X (Finsupp.single (0, 0) (n - l) + g3S k l (fun t => π t j)) : GCTOcc.CoordRing))
        (fun _ => 1) (fun j _ => isHomogeneous_C_mul_X _ _))
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using this
  · intro g hg _ p hp
    have hpn := hp.1
    rw [g3SL_eq, g3_eval_F n k l _ (g3SL_homog n n g p hpn), g3_eval_F n k l p hpn,
      g3_hd_D_SL n k l hn hk g hg p, coeff_C_mul,
      g3_top_substLin n _ hn g hg _ (g3_hd_homog n k l p hpn), ← mul_assoc,
      g3_weight n k l hk1 hn hk g hg]

/-! G3 part D: nonvanishing on the determinant orbit closure, and the theorem. -/

theorem g3_single_eq_S (k l : ℕ) (hl : 1 ≤ l) (s : Fin l → Fin k) (i : Fin k) :
    Finsupp.single ((0 : ℕ), ((i : Fin k) : ℕ)) l = g3S k l s ↔ ∀ t, s t = i := by
  constructor
  · intro h t
    have h1 : 1 ≤ g3S k l s ((0 : ℕ), ((s t : Fin k) : ℕ)) := by
      unfold g3S
      rw [Finsupp.finset_sum_apply]
      calc 1 = Finsupp.single ((0 : ℕ), ((s t : Fin k) : ℕ)) 1 ((0 : ℕ), ((s t : Fin k) : ℕ)) := by
            simp
        _ ≤ _ := Finset.single_le_sum
            (f := fun t' => Finsupp.single ((0 : ℕ), ((s t' : Fin k) : ℕ)) 1
              ((0 : ℕ), ((s t : Fin k) : ℕ)))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    rw [← h, Finsupp.single_apply] at h1
    split_ifs at h1 with hh
    · apply Fin.ext
      simp only [Prod.mk.injEq, true_and] at hh
      exact hh.symm
    · omega
  · intro h
    unfold g3S
    simp only [h]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finsupp.smul_single, smul_eq_mul,
      mul_one]

/-- the test form `X₀₀^(n-l) · ∑_{i<k} X₀ᵢ^l`. -/
noncomputable def g3q0 (n k l : ℕ) : GCTOcc.PolyR :=
  X (0, 0) ^ (n - l) * ∑ i : Fin k, X ((0 : ℕ), ((i : Fin k) : ℕ)) ^ l

theorem g3_coeff_q0 (n k l : ℕ) (hl : 1 ≤ l) (s : Fin l → Fin k) :
    coeff (Finsupp.single (0, 0) (n - l) + g3S k l s) (g3q0 n k l) =
      ∑ i : Fin k, if (∀ t, s t = i) then (1 : ℂ) else 0 := by
  classical
  unfold g3q0
  rw [Finset.mul_sum, coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul, coeff_monomial]
  by_cases h : ∀ t, s t = i
  · rw [if_pos h, if_pos]
    rw [(g3_single_eq_S k l hl s i).2 h]
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    apply (g3_single_eq_S k l hl s i).1
    exact add_left_cancel h'

theorem g3_nonvanish (n k l : ℕ) (hl : 1 ≤ l) (hle : Even l) :
    GCTOcc.evalCoeff (g3q0 n k l) (g3F n k l) ≠ 0 := by
  classical
  have t0 : Fin l := ⟨0, hl⟩
  unfold GCTOcc.evalCoeff g3F
  simp only [map_sum, map_mul, map_prod, eval_C, eval_X, g3_coeff_q0 n k l hl]
  have hinj : Function.Injective (fun σ : Equiv.Perm (Fin k) => fun _ : Fin l => σ) := by
    intro a b h
    exact congrFun h t0
  rw [← Finset.sum_subset (Finset.subset_univ
    (Finset.univ.image (fun σ : Equiv.Perm (Fin k) => fun _ : Fin l => σ))) ?_]
  · rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    have hterm : ∀ σ : Equiv.Perm (Fin k),
        (((∏ _t : Fin l, ((Equiv.Perm.sign σ : ℤ))) : ℤ) : ℂ) *
          ∏ j : Fin k, (g3w k l (fun _ => σ j) (Finsupp.single (0, 0) (n - l)) *
            ∑ i : Fin k, if (∀ _t : Fin l, σ j = i) then (1 : ℂ) else 0)
          = ∏ i : Fin k, g3w k l (fun _ => i) (Finsupp.single (0, 0) (n - l)) := by
      intro σ
      have hs : (∏ _t : Fin l, ((Equiv.Perm.sign σ : ℤ))) = 1 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
        · simp
        · simp [hle.neg_one_pow]
      rw [hs, Int.cast_one, one_mul]
      have h1 : ∀ j : Fin k, (∑ i : Fin k, if (∀ _t : Fin l, σ j = i) then (1 : ℂ) else 0) = 1 := by
        intro j
        rw [Finset.sum_eq_single (σ j)]
        · rw [if_pos (fun _ => rfl)]
        · intro b _ hb
          rw [if_neg]
          intro h
          exact hb (h t0).symm
        · intro h; exact absurd (Finset.mem_univ _) h
      simp only [h1, mul_one]
      exact Equiv.prod_comp σ (fun i => g3w k l (fun _ => i) (Finsupp.single (0, 0) (n - l)))
    rw [Finset.sum_congr rfl (fun σ _ => hterm σ), Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero k)
      (Finset.prod_ne_zero_iff.2 (fun i _ => g3w_ne_zero k l _ _))
  · intro π _ hπ
    have hnc : ∃ t j, π t j ≠ π t0 j := by
      by_contra hcon
      push Not at hcon
      apply hπ
      rw [Finset.mem_image]
      refine ⟨π t0, Finset.mem_univ _, ?_⟩
      funext t
      apply Equiv.ext
      intro j
      exact (hcon t j).symm
    obtain ⟨t, j, htj⟩ := hnc
    rw [Finset.prod_eq_zero (Finset.mem_univ j), mul_zero]
    rw [Finset.sum_eq_zero, mul_zero]
    intro i _
    rw [if_neg]
    intro h
    exact htj ((h t).trans (h t0).symm)

open GCTOcc in
theorem g3_q0_mem (n k l : ℕ) (hk1 : 1 ≤ k) (hl : 1 ≤ l) (hkl : k * l ≤ n) :
    g3q0 n k l ∈ orbitClosure n (detPoly n) := by
  classical
  have hln : l ≤ n := le_trans (Nat.le_mul_of_pos_left l hk1) hkl
  have hkn : k ≤ n := le_trans (Nat.le_mul_of_pos_right k hl) hkl
  have hn1 : 1 ≤ n := le_trans hk1 hkn
  have hsupp : (∑ i : Fin k, X ((0 : ℕ), ((i : Fin k) : ℕ)) ^ l : PolyR).support ⊆
      Finset.univ.image (fun i : Fin k => Finsupp.single ((0 : ℕ), ((i : Fin k) : ℕ)) l) := by
    intro μ hμ
    have := support_sum hμ
    rw [Finset.mem_biUnion] at this
    obtain ⟨i, _, hi⟩ := this
    rw [X_pow_eq_monomial, support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hi
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi.symm⟩
  have hhom : (∑ i : Fin k, X ((0 : ℕ), ((i : Fin k) : ℕ)) ^ l : PolyR).IsHomogeneous l :=
    IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_X_pow _ _)
  have hfv : ∀ μ ∈ (∑ i : Fin k, X ((0 : ℕ), ((i : Fin k) : ℕ)) ^ l : PolyR).support,
      ∀ v ∈ μ.support, v.1 < n ∧ v.2 < n := by
    intro μ hμ v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 (hsupp hμ)
    rw [Finsupp.support_single_ne_zero _ (by omega), Finset.mem_singleton] at hv
    subst hv
    have hi := i.isLt
    constructor
    · show (0 : ℕ) < n
      omega
    · show (i : ℕ) < n
      omega
  have hdeg : ∀ μ ∈ (∑ i : Fin k, X ((0 : ℕ), ((i : Fin k) : ℕ)) ^ l : PolyR).support,
      Finsupp.degree μ = l := by
    intro μ hμ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 (hsupp hμ)
    exact Finsupp.degree_single _ _
  have hcard : (∑ i : Fin k, X ((0 : ℕ), ((i : Fin k) : ℕ)) ^ l : PolyR).support.card * l ≤ n := by
    have h1 := Finset.card_le_card hsupp
    have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin k)))
      (f := fun i : Fin k => Finsupp.single ((0 : ℕ), ((i : Fin k) : ℕ)) l)
    rw [Finset.card_univ, Fintype.card_fin] at h2
    calc _ ≤ k * l := Nat.mul_le_mul_right l (h1.trans h2)
      _ ≤ n := hkl
  have hsd := symbolicDet_of_few_monomials n l hn1 _ hdeg hcard
  exact padded_mem_orbitClosure_of_symbolicDet n l hln _ hhom hfv hsd

open GCTOcc in
/-- G3 = a3397022 `row_extended_rectangle_occurs`. -/
theorem g3_row_extended_rectangle_occurs (n k l : ℕ) (hk : 1 ≤ k) (hn : k * l ≤ n)
    (hl : Even l) :
    Occurs n k (fun i => if i = 0 then l + (n * k - k * l) else if i < k then l else 0)
      (orbitClosure n (detPoly n)) := by
  classical
  rcases Nat.eq_zero_or_pos l with rfl | hl1
  · refine ⟨X (Finsupp.single (0, 0) n) ^ k, ⟨isHomogeneous_X_pow _ _, ?_⟩, X (0, 0) ^ n, ?_, ?_⟩
    · intro g hg _ p hp
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · have : substLin 0 g p = p := by
          simp [substLin, aeval_X_left_apply]
        rw [this]
        simp
      · unfold evalCoeff
        simp only [map_pow, eval_X]
        rw [g3SL_eq, g3_top_substLin n n hn0 g hg p hp.1]
        rw [Finset.prod_eq_single (⟨0, hn0⟩, ⟨0, hn0⟩)]
        · simp only [idx, Fin.val_mk, zero_mul, add_zero, if_true, zero_add, mul_zero,
            Nat.sub_zero]
          rw [mul_pow, ← pow_mul]
        · intro v _ hv
          have h0 : idx n v ≠ 0 := by
            intro h
            apply hv
            unfold idx at h
            have h2 : (v.2 : ℕ) = 0 := by omega
            have h1 : (v.1 : ℕ) * n = 0 := by omega
            have h1' : (v.1 : ℕ) = 0 := by
              rcases mul_eq_zero.1 h1 with h | h
              · exact h
              · omega
            ext
            · simp [h1']
            · simp [h2]
          simp [h0]
        · intro h; exact absurd (Finset.mem_univ _) h
    · have h1 : IsSymbolicDet (1 : PolyR) n := by
        refine ⟨1, ?_, Matrix.det_one⟩
        intro i j
        rw [Matrix.one_apply]
        split_ifs <;> simp
      have := padded_mem_orbitClosure_of_symbolicDet n 0 (Nat.zero_le _) 1 (isHomogeneous_one _ _)
        (by
          intro μ hμ v hv
          rw [support_one, Finset.mem_singleton] at hμ
          subst hμ
          simp at hv) h1
      simpa using this
    · unfold evalCoeff
      simp [coeff_X_pow]
  · have hkn : k ≤ n := le_trans (Nat.le_mul_of_pos_right k hl1) hn
    exact ⟨g3F n k l, g3_hwv n k l hk hkn, g3q0 n k l, g3_q0_mem n k l hk hl1 hn,
      g3_nonvanish n k l hl1 hl⟩

open GCTOcc in
theorem solution (n k l : ℕ) (hk : 1 ≤ k) (hn : k * l ≤ n) (hl : Even l) :
    Occurs n k (fun i => if i = 0 then l + (n * k - k * l) else if i < k then l else 0)
      (orbitClosure n (detPoly n)) := by
  exact g3_row_extended_rectangle_occurs n k l hk hn hl
