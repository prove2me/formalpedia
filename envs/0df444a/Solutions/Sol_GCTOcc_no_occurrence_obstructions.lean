-- Prove2me | solution 1 for GCTOcc.no_occurrence_obstructions
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T05:42:48.312977+00:00
-- url     : https://prove2.me/submissions/44ced246-af29-4469-ad8d-3444b8fd851c

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


namespace TD

variable {R : Type} [CommRing R]

/-- Variable index of a cell under a column-wise permutation `σ`. -/
def var {w K : ℕ} {c : Fin w → ℕ} (hc : ∀ j, c j ≤ K)
    (σ : (j : Fin w) → Equiv.Perm (Fin (c j))) (x : Σ j : Fin w, Fin (c j)) : Fin K :=
  Fin.castLE (hc x.1) (σ x.1 x.2)

/-- The tableau alternant. -/
noncomputable def td {w K t : ℕ} (c : Fin w → ℕ) (hc : ∀ j, c j ≤ K) (a : Fin t → ℕ)
    (e : (Σ s : Fin t, Fin (a s)) ≃ (Σ j : Fin w, Fin (c j)))
    (f : (s : Fin t) → (Fin (a s) → Fin K) → R) : R :=
  ∑ σ : (j : Fin w) → Equiv.Perm (Fin (c j)),
    (((∏ j, (Equiv.Perm.sign (σ j) : ℤ)) : ℤ) : R) * ∏ s, f s (fun k => var hc σ (e ⟨s, k⟩))

/-- Upper-left `c × c` block. -/
def blk {K c : ℕ} (h : c ≤ K) (G : Matrix (Fin K) (Fin K) R) : Matrix (Fin c) (Fin c) R :=
  G.submatrix (Fin.castLE h) (Fin.castLE h)

theorem sum_sign_prod {c : ℕ} (M : Matrix (Fin c) (Fin c) R) :
    ∑ τ : Equiv.Perm (Fin c), ((Equiv.Perm.sign τ : ℤ) : R) * ∏ i, M i (τ i) = M.det := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Units.smul_def, zsmul_eq_mul]
  rfl

theorem td_transform {w K t : ℕ} (c : Fin w → ℕ) (hc : ∀ j, c j ≤ K) (a : Fin t → ℕ)
    (e : (Σ s : Fin t, Fin (a s)) ≃ (Σ j : Fin w, Fin (c j)))
    (G : Matrix (Fin K) (Fin K) R) (hG : ∀ b y : Fin K, y < b → G b y = 0)
    (f : (s : Fin t) → (Fin (a s) → Fin K) → R) :
    td c hc a e (fun s y => ∑ b : Fin (a s) → Fin K, (∏ k, G (b k) (y k)) * f s b)
      = (∏ j, (blk (hc j) G).det) * td c hc a e f := by
  classical
  -- the matrix seen by column `j` for a choice `B` of new directions
  let Bf : ((s : Fin t) → Fin (a s) → Fin K) → (Σ s : Fin t, Fin (a s)) → Fin K :=
    fun B z => B z.1 z.2
  let M : ((s : Fin t) → Fin (a s) → Fin K) → (j : Fin w) → Matrix (Fin (c j)) (Fin (c j)) R :=
    fun B j i i' => G (Bf B (e.symm ⟨j, i⟩)) (Fin.castLE (hc j) i')
  -- step 1: expand the product of sums
  have step1 : td c hc a e (fun s y => ∑ b : Fin (a s) → Fin K, (∏ k, G (b k) (y k)) * f s b)
      = ∑ B : (s : Fin t) → Fin (a s) → Fin K,
          (∏ j, (M B j).det) * ∏ s, f s (B s) := by
    unfold td
    have h1 : ∀ σ : (j : Fin w) → Equiv.Perm (Fin (c j)),
        (∏ s, ∑ b : Fin (a s) → Fin K,
          (∏ k, G (b k) (var hc σ (e ⟨s, k⟩))) * f s b)
        = ∑ B : (s : Fin t) → Fin (a s) → Fin K,
            (∏ s, ∏ k, G (B s k) (var hc σ (e ⟨s, k⟩))) * ∏ s, f s (B s) := by
      intro σ
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      refine Finset.sum_congr rfl (fun B _ => ?_)
      rw [Finset.prod_mul_distrib]
    simp_rw [h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun B _ => ?_)
    -- regroup the G-product by cells, then by columns
    have h2 : ∀ σ : (j : Fin w) → Equiv.Perm (Fin (c j)),
        (∏ s, ∏ k, G (B s k) (var hc σ (e ⟨s, k⟩)))
          = ∏ j, ∏ i, M B j i (σ j i) := by
      intro σ
      have hz : (∏ s, ∏ k, G (B s k) (var hc σ (e ⟨s, k⟩)))
          = ∏ z : (Σ s : Fin t, Fin (a s)), G (Bf B z) (var hc σ (e z)) := by
        rw [← Finset.univ_sigma_univ, Finset.prod_sigma]
      rw [hz, ← Equiv.prod_comp e.symm]
      have hx : ∀ x : (Σ j : Fin w, Fin (c j)),
          G (Bf B (e.symm x)) (var hc σ (e (e.symm x))) = M B x.1 x.2 (σ x.1 x.2) := by
        intro x
        rw [Equiv.apply_symm_apply]
        rfl
      simp_rw [hx]
      rw [← Finset.univ_sigma_univ, Finset.prod_sigma]
    have h3 : ∑ σ : (j : Fin w) → Equiv.Perm (Fin (c j)),
        (((∏ j, (Equiv.Perm.sign (σ j) : ℤ)) : ℤ) : R) * ∏ j, ∏ i, M B j i (σ j i)
        = ∏ j, (M B j).det := by
      have h4 : ∀ σ : (j : Fin w) → Equiv.Perm (Fin (c j)),
          (((∏ j, (Equiv.Perm.sign (σ j) : ℤ)) : ℤ) : R) * ∏ j, ∏ i, M B j i (σ j i)
            = ∏ j, (((Equiv.Perm.sign (σ j) : ℤ) : R) * ∏ i, M B j i (σ j i)) := by
        intro σ
        rw [Finset.prod_mul_distrib, Int.cast_prod]
      simp_rw [h4]
      have h5 : ∏ j, (M B j).det = ∏ j, ∑ τ : Equiv.Perm (Fin (c j)),
          ((Equiv.Perm.sign τ : ℤ) : R) * ∏ i, M B j i (τ i) :=
        Finset.prod_congr rfl (fun j _ => (sum_sign_prod (M B j)).symm)
      rw [h5, Finset.prod_univ_sum, Fintype.piFinset_univ]
    rw [← h3, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [h2 σ]
    ring
  rw [step1]
  -- step 2: only permutation choices survive
  unfold td
  rw [Finset.mul_sum]
  let φ : ((j : Fin w) → Equiv.Perm (Fin (c j))) → ((s : Fin t) → Fin (a s) → Fin K) :=
    fun π s k => var hc π (e ⟨s, k⟩)
  have hφinj : Function.Injective φ := by
    intro π π' h
    funext j
    apply Equiv.ext
    intro i
    have hx := congrFun (congrFun h (e.symm ⟨j, i⟩).1) (e.symm ⟨j, i⟩).2
    simp only [φ, var] at hx
    have hx' : Fin.castLE (hc j) (π j i) = Fin.castLE (hc j) (π' j i) := by
      have e1 : (⟨(e.symm ⟨j, i⟩).1, (e.symm ⟨j, i⟩).2⟩ : Σ s : Fin t, Fin (a s)) = e.symm ⟨j, i⟩ :=
        rfl
      rw [e1, Equiv.apply_symm_apply] at hx
      exact hx
    exact Fin.castLE_injective _ hx'
  symm
  refine Fintype.sum_of_injective φ hφinj _ _ ?_ ?_
  · -- non-permutation choices vanish
    intro B hB
    by_contra hne
    have hdet : ∀ j, (M B j).det ≠ 0 := by
      intro j hj
      apply hne
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hj, zero_mul]
    apply hB
    -- every column map is a permutation
    have hlt : ∀ j (i : Fin (c j)), (Bf B (e.symm ⟨j, i⟩) : ℕ) < c j := by
      intro j i
      by_contra hge
      push Not at hge
      apply hdet j
      apply Matrix.det_eq_zero_of_row_eq_zero i
      intro i'
      show G (Bf B (e.symm ⟨j, i⟩)) (Fin.castLE (hc j) i') = 0
      apply hG
      rw [Fin.lt_def]
      simp only [Fin.val_castLE]
      omega
    let τ : (j : Fin w) → Fin (c j) → Fin (c j) := fun j i => ⟨Bf B (e.symm ⟨j, i⟩), hlt j i⟩
    have hτ : ∀ j, Function.Injective (τ j) := by
      intro j i i' hii
      by_contra hne'
      apply hdet j
      apply Matrix.det_zero_of_row_eq hne'
      funext i''
      show G (Bf B (e.symm ⟨j, i⟩)) (Fin.castLE (hc j) i'') =
        G (Bf B (e.symm ⟨j, i'⟩)) (Fin.castLE (hc j) i'')
      have : (Bf B (e.symm ⟨j, i⟩)) = (Bf B (e.symm ⟨j, i'⟩)) := by
        apply Fin.ext
        have := congrArg Fin.val hii
        simpa [τ] using this
      rw [this]
    refine ⟨fun j => Equiv.ofBijective (τ j) (Finite.injective_iff_bijective.1 (hτ j)), ?_⟩
    funext s k
    simp only [φ, var, Equiv.ofBijective_apply]
    apply Fin.ext
    simp only [Fin.val_castLE, τ]
    have e2 : e.symm (e ⟨s, k⟩) = ⟨s, k⟩ := Equiv.symm_apply_apply e _
    have e3 : (⟨(e ⟨s, k⟩).1, (e ⟨s, k⟩).2⟩ : Σ j : Fin w, Fin (c j)) = e ⟨s, k⟩ := rfl
    rw [e3, e2]
  · -- permutation choices give the sign times the block determinants
    intro π
    have hM : ∀ j, M (φ π) j = (blk (hc j) G).submatrix (π j) id := by
      intro j
      funext i i'
      simp only [M, Bf, φ, var, blk, Matrix.submatrix_apply, id]
      have e3 : (⟨(e.symm ⟨j, i⟩).1, (e.symm ⟨j, i⟩).2⟩ : Σ s : Fin t, Fin (a s)) = e.symm ⟨j, i⟩ :=
        rfl
      rw [e3, Equiv.apply_symm_apply]
    simp_rw [hM, Matrix.det_permute]
    rw [Finset.prod_mul_distrib, Int.cast_prod]
    simp only [φ]
    ring

end TD


/-! ===== P2 (a586c963 session 7): tableau highest weight vectors ===== -/

theorem p2_coeff_prod {ι : Type} [Fintype ι] (e : ι → ℕ) (H : ι → GCTOcc.PolyR)
    (hH : ∀ j, (H j).IsHomogeneous (e j)) :
    coeff (Finsupp.single (0, 0) (∑ j, e j)) (∏ j, H j) =
      ∏ j, coeff (Finsupp.single (0, 0) (e j)) (H j) := by
  classical
  have hP : (∏ j, H j).IsHomogeneous (∑ j, e j) :=
    IsHomogeneous.prod Finset.univ H e (fun j _ => hH j)
  have h1 := g3phi_homog (∑ j, e j) _ hP
  have h2 : g3phi (∏ j, H j) =
      C (∏ j, coeff (Finsupp.single (0, 0) (e j)) (H j)) * X (0, 0) ^ (∑ j, e j) := by
    rw [map_prod]
    simp_rw [g3phi_homog _ _ (hH _)]
    rw [Finset.prod_mul_distrib, map_prod, Finset.prod_pow_eq_pow_sum]
  have := congrArg (coeff (Finsupp.single (0, 0) (∑ j, e j))) (h1.symm.trans h2)
  rwa [g3_coeff_C_mul_X_pow, g3_coeff_C_mul_X_pow] at this

/-- The tableau polynomial: the alternant of the derivative tensors of `p`. -/
noncomputable def p2H (w K t : ℕ) (c : Fin w → ℕ) (hc : ∀ j, c j ≤ K) (a : Fin t → ℕ)
    (e : (Σ s : Fin t, Fin (a s)) ≃ (Σ j : Fin w, Fin (c j))) (p : GCTOcc.PolyR) : GCTOcc.PolyR :=
  TD.td c hc a e (fun s y => g3D K (a s) y p)

theorem p2_H_SL (n w K t : ℕ) (hn : 0 < n) (hK : K ≤ n) (c : Fin w → ℕ) (hc : ∀ j, c j ≤ K)
    (a : Fin t → ℕ) (e : (Σ s : Fin t, Fin (a s)) ≃ (Σ j : Fin w, Fin (c j)))
    (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hg : GCTOcc.IsUpperTri n g)
    (p : GCTOcc.PolyR) :
    p2H w K t c hc a e (g3SL n g p) =
      C (∏ j, (TD.blk (hc j) (g3Gm n K hn hK g)).det) * g3SL n g (p2H w K t c hc a e p) := by
  have h1 : (fun s y => g3D K (a s) y (g3SL n g p)) = fun s (y : Fin (a s) → Fin K) =>
      ∑ b : Fin (a s) → Fin K,
        (∏ k, ((g3Gm n K hn hK g).map (C : ℂ →+* GCTOcc.PolyR)) (b k) (y k)) *
          g3SL n g (g3D K (a s) b p) := by
    funext s y
    rw [g3_D_SL n K hn hK g hg]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_prod]
    rfl
  unfold p2H
  rw [h1, TD.td_transform]
  · have h2 : ∀ j, (TD.blk (hc j) ((g3Gm n K hn hK g).map (C : ℂ →+* GCTOcc.PolyR))).det =
        C ((TD.blk (hc j) (g3Gm n K hn hK g)).det) := by
      intro j
      rw [show TD.blk (hc j) ((g3Gm n K hn hK g).map (C : ℂ →+* GCTOcc.PolyR)) =
        (TD.blk (hc j) (g3Gm n K hn hK g)).map C from rfl, RingHom.map_det]
      rfl
    simp_rw [h2]
    rw [← map_prod]
    congr 1
    unfold TD.td
    rw [map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [map_mul, map_prod, map_intCast]
  · intro b y hyb
    simp only [Matrix.map_apply]
    rw [show g3Gm n K hn hK g b y = 0 from ?_, C_0]
    show g (g3e n K hn hK b) (g3e n K hn hK y) = 0
    apply hg
    rw [g3e_idx, g3e_idx]
    exact hyb

theorem p2_H_homog (n w K t : ℕ) (c : Fin w → ℕ) (hc : ∀ j, c j ≤ K) (a : Fin t → ℕ)
    (e : (Σ s : Fin t, Fin (a s)) ≃ (Σ j : Fin w, Fin (c j))) (p : GCTOcc.PolyR)
    (hp : p.IsHomogeneous n) :
    (p2H w K t c hc a e p).IsHomogeneous (∑ s, (n - a s)) := by
  unfold p2H TD.td
  apply IsHomogeneous.sum
  intro σ _
  have h0 : ((((∏ j, (Equiv.Perm.sign (σ j) : ℤ)) : ℤ) : GCTOcc.PolyR)).IsHomogeneous 0 := by
    rw [← map_intCast (C : ℂ →+* GCTOcc.PolyR)]
    exact isHomogeneous_C _ _
  have := h0.mul (IsHomogeneous.prod (Finset.univ : Finset (Fin t))
    (fun s => g3D K (a s) (fun k => TD.var hc σ (e ⟨s, k⟩)) p) (fun s => n - a s)
    (fun s _ => g3_D_homog K n (a s) (fun k => TD.var hc σ (e ⟨s, k⟩)) p hp))
  simpa using this

/-- The tableau highest weight vector as a polynomial in the coefficients. -/
noncomputable def p2F (n w K t : ℕ) (c : Fin w → ℕ) (hc : ∀ j, c j ≤ K) (a : Fin t → ℕ)
    (e : (Σ s : Fin t, Fin (a s)) ≃ (Σ j : Fin w, Fin (c j))) : GCTOcc.CoordRing :=
  ∑ σ : (j : Fin w) → Equiv.Perm (Fin (c j)),
    C ((((∏ j, (Equiv.Perm.sign (σ j) : ℤ)) : ℤ) : ℂ)) *
      ∏ s : Fin t, (C (g3w K (a s) (fun k => TD.var hc σ (e ⟨s, k⟩))
          (Finsupp.single (0, 0) (n - a s))) *
        X (Finsupp.single (0, 0) (n - a s) + g3S K (a s) (fun k => TD.var hc σ (e ⟨s, k⟩))))

theorem p2_eval_F (n w K t : ℕ) (c : Fin w → ℕ) (hc : ∀ j, c j ≤ K) (a : Fin t → ℕ)
    (e : (Σ s : Fin t, Fin (a s)) ≃ (Σ j : Fin w, Fin (c j))) (p : GCTOcc.PolyR)
    (hp : p.IsHomogeneous n) :
    GCTOcc.evalCoeff p (p2F n w K t c hc a e) =
      coeff (Finsupp.single (0, 0) (∑ s, (n - a s))) (p2H w K t c hc a e p) := by
  unfold GCTOcc.evalCoeff p2F p2H TD.td
  rw [coeff_sum, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← map_intCast (C : ℂ →+* GCTOcc.PolyR), coeff_C_mul,
    p2_coeff_prod (fun s => n - a s) _ (fun s => g3_D_homog K n (a s) _ p hp)]
  simp only [map_mul, map_prod, eval_C, eval_X]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [g3_coeff_D]

/-- Weight of a tableau HWV: column heights `c`, plus `N` on the first row. -/
def p2lam (N w : ℕ) (c : Fin w → ℕ) : ℕ → ℕ := fun i =>
  (if i = 0 then N else 0) + (Finset.univ.filter (fun j : Fin w => i < c j)).card

theorem p2_blk_det (n K : ℕ) (hn : 0 < n) (hK : K ≤ n)
    (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hg : GCTOcc.IsUpperTri n g) {c : ℕ}
    (h : c ≤ K) :
    (TD.blk h (g3Gm n K hn hK g)).det =
      ∏ i : Fin c, g (g3e n K hn hK (Fin.castLE h i)) (g3e n K hn hK (Fin.castLE h i)) := by
  rw [Matrix.det_of_isUpperTriangular]
  · rfl
  · intro i j hij
    show g (g3e n K hn hK (Fin.castLE h i)) (g3e n K hn hK (Fin.castLE h j)) = 0
    apply hg
    rw [g3e_idx, g3e_idx]
    simpa using hij

theorem p2_prod_cols {M : Type} [CommMonoid M] (w K : ℕ) (c : Fin w → ℕ) (hc : ∀ j, c j ≤ K)
    (f : Fin K → M) :
    ∏ j, ∏ i : Fin (c j), f (Fin.castLE (hc j) i) =
      ∏ i : Fin K, f i ^ (Finset.univ.filter (fun j : Fin w => (i : ℕ) < c j)).card := by
  classical
  have h1 : ∀ j, ∏ i : Fin (c j), f (Fin.castLE (hc j) i) =
      ∏ i : Fin K, (if (i : ℕ) < c j then f i else 1) := by
    intro j
    refine Fintype.prod_of_injective (Fin.castLE (hc j)) (Fin.castLE_injective _) _ _ ?_ ?_
    · intro i hi
      rw [if_neg]
      intro hlt
      exact hi ⟨⟨i, hlt⟩, Fin.ext rfl⟩
    · intro i
      rw [if_pos (by simp)]
  simp_rw [h1]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]

theorem p2_weight (n w K : ℕ) (hK1 : 1 ≤ K) (hn : 0 < n) (hK : K ≤ n) (c : Fin w → ℕ)
    (hc : ∀ j, c j ≤ K) (N : ℕ) (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hg : GCTOcc.IsUpperTri n g) :
    (∏ j, (TD.blk (hc j) (g3Gm n K hn hK g)).det) * g (⟨0, hn⟩, ⟨0, hn⟩) (⟨0, hn⟩, ⟨0, hn⟩) ^ N =
      ∏ v : Fin n × Fin n, (g v v) ^ (p2lam N w c (GCTOcc.idx n v)) := by
  classical
  simp_rw [p2_blk_det n K hn hK g hg]
  rw [p2_prod_cols w K c hc (fun i => g (g3e n K hn hK i) (g3e n K hn hK i))]
  have hprod : ∏ v : Fin n × Fin n, (g v v) ^ (p2lam N w c (GCTOcc.idx n v)) =
      ∏ i : Fin K, (g (g3e n K hn hK i) (g3e n K hn hK i)) ^ (p2lam N w c i) := by
    symm
    refine Fintype.prod_of_injective (g3e n K hn hK) (g3e_inj n K hn hK) _ _ ?_ ?_
    · intro v hv
      have hkv := g3e_le_idx n K hn hK v hv
      have : p2lam N w c (GCTOcc.idx n v) = 0 := by
        unfold p2lam
        rw [if_neg (by omega)]
        simp only [zero_add, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j _
        have := hc j
        omega
      rw [this, pow_zero]
    · intro i
      rw [g3e_idx]
  rw [hprod]
  unfold p2lam
  simp_rw [pow_add]
  rw [Finset.prod_mul_distrib, mul_comm]
  congr 1
  rw [Finset.prod_eq_single (⟨0, hK1⟩ : Fin K)]
  · rw [if_pos rfl]; rfl
  · intro b _ hb
    rw [if_neg, pow_zero]
    intro h; exact hb (Fin.ext h)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem p2_hwv (n w K t : ℕ) (hK1 : 1 ≤ K) (hK : K ≤ n) (c : Fin w → ℕ) (hc : ∀ j, c j ≤ K)
    (a : Fin t → ℕ) (e : (Σ s : Fin t, Fin (a s)) ≃ (Σ j : Fin w, Fin (c j))) :
    GCTOcc.IsHWV n t (p2lam (∑ s, (n - a s)) w c) (p2F n w K t c hc a e) := by
  have hn : 0 < n := by omega
  refine ⟨?_, ?_⟩
  · unfold p2F
    apply IsHomogeneous.sum
    intro σ _
    have := (isHomogeneous_C (σ := (ℕ × ℕ) →₀ ℕ) (R := ℂ)
        ((((∏ j, (Equiv.Perm.sign (σ j) : ℤ)) : ℤ) : ℂ))).mul
      (IsHomogeneous.prod (Finset.univ : Finset (Fin t))
        (fun s => (C (g3w K (a s) (fun k => TD.var hc σ (e ⟨s, k⟩))
          (Finsupp.single (0, 0) (n - a s))) *
          X (Finsupp.single (0, 0) (n - a s) + g3S K (a s) (fun k => TD.var hc σ (e ⟨s, k⟩))) :
            GCTOcc.CoordRing)) (fun _ => 1)
        (fun s _ => isHomogeneous_C_mul_X _ _))
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using this
  · intro g hg _ p hp
    have hpn := hp.1
    rw [g3SL_eq, p2_eval_F n w K t c hc a e _ (g3SL_homog n n g p hpn),
      p2_eval_F n w K t c hc a e p hpn, p2_H_SL n w K t hn hK c hc a e g hg p, coeff_C_mul,
      g3_top_substLin n _ hn g hg _ (p2_H_homog n w K t c hc a e p hpn), ← mul_assoc,
      p2_weight n w K hK1 hn hK c hc _ g hg]

/-! ===== P2g: nonvanishing ===== -/

/-- `X00`-component of a derivative shift. -/
theorem p2_g3S_00 (K l : ℕ) (y : Fin l → Fin K) :
    (g3S K l y) (0, 0) = (Finset.univ.filter (fun k => ((y k : Fin K) : ℕ) = 0)).card := by
  classical
  unfold g3S
  rw [Finsupp.finsetSum_apply, Finset.card_filter]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finsupp.single_apply]
  by_cases h : ((y k : Fin K) : ℕ) = 0
  · rw [if_pos (by rw [h]), if_pos h]
  · rw [if_neg (by intro h'; apply h; exact (Prod.mk.inj h').2), if_neg h]

/-- Row-sum functional. -/
noncomputable def p2psi : ((ℕ × ℕ) →₀ ℕ) →+ ℕ :=
  Finsupp.liftAddHom (fun v => AddMonoidHom.mulRight v.2)

theorem p2_psi_g3S (K l : ℕ) (y : Fin l → Fin K) : p2psi (g3S K l y) = ∑ k, ((y k : Fin K) : ℕ) := by
  unfold g3S
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [p2psi]

theorem p2_perm_le {c : ℕ} (τ : Equiv.Perm (Fin c)) (i : Fin c)
    (h : ∀ i', i < i' → τ i' = i') : τ i ≤ i := by
  by_contra hlt
  push Not at hlt
  have h1 := h (τ i) hlt
  have h2 : τ i = i := τ.injective h1
  rw [h2] at hlt
  exact lt_irrefl _ hlt

theorem p2_nonvanish (n w K t : ℕ) (hn : 1 ≤ n) (c : Fin w → ℕ) (hc : ∀ j, c j ≤ K)
    (a : Fin t → ℕ) (e : (Σ s : Fin t, Fin (a s)) ≃ (Σ j : Fin w, Fin (c j)))
    (hcol : ∀ j (i i' : Fin (c j)), i < i' → (e.symm ⟨j, i⟩).1 < (e.symm ⟨j, i'⟩).1)
    (hrow0 : ∀ j (i : Fin (c j)), (i : ℕ) = 0 → a (e.symm ⟨j, i⟩).1 = 1)
    (hbody : ∀ j (i : Fin (c j)), (i : ℕ) ≠ 0 → 2 ≤ a (e.symm ⟨j, i⟩).1)
    (hdist : ∀ s s', 2 ≤ a s → 2 ≤ a s' → a s = a s' → s = s')
    (han : ∀ s, a s ≤ n) (hpos : ∀ s, 1 ≤ a s) :
    GCTOcc.evalCoeff
      (monomial (Finsupp.single (0, 0) n) 1 + ∑ s ∈ Finset.univ.filter (fun s => 2 ≤ a s),
        monomial (Finsupp.single (0, 0) (n - a s) +
          g3S K (a s) (fun k => TD.var hc (fun _ => 1) (e ⟨s, k⟩))) 1)
      (p2F n w K t c hc a e) ≠ 0 := by
  classical
  set idv : (j : Fin w) → Equiv.Perm (Fin (c j)) := fun _ => 1 with hidv
  set body := Finset.univ.filter (fun s : Fin t => 2 ≤ a s) with hbodyS
  set mon : ((j : Fin w) → Equiv.Perm (Fin (c j))) → Fin t → ((ℕ × ℕ) →₀ ℕ) := fun σ s =>
    Finsupp.single (0, 0) (n - a s) + g3S K (a s) (fun k => TD.var hc σ (e ⟨s, k⟩)) with hmon
  set p0 : GCTOcc.PolyR := monomial (Finsupp.single (0, 0) n) 1 +
    ∑ s ∈ body, monomial (mon idv s) 1 with hp0
  -- cells of a factor
  have hfac : ∀ s (k : Fin (a s)), (e.symm (e ⟨s, k⟩)).1 = s := fun s k => by
    rw [Equiv.symm_apply_apply]
  -- a factor of content >= 2 has only body cells; content 1 only the row-0 cell
  have hcellrow : ∀ s (k : Fin (a s)), 2 ≤ a s → ((e ⟨s, k⟩).2 : ℕ) ≠ 0 := by
    intro s k hs h0
    have := hrow0 (e ⟨s, k⟩).1 (e ⟨s, k⟩).2 h0
    have e1 : (⟨(e ⟨s, k⟩).1, (e ⟨s, k⟩).2⟩ : Σ j : Fin w, Fin (c j)) = e ⟨s, k⟩ := rfl
    rw [e1, hfac] at this
    omega
  have hcell0 : ∀ s (k : Fin (a s)), a s < 2 → ((e ⟨s, k⟩).2 : ℕ) = 0 := by
    intro s k hs
    by_contra h0
    have := hbody (e ⟨s, k⟩).1 (e ⟨s, k⟩).2 h0
    have e1 : (⟨(e ⟨s, k⟩).1, (e ⟨s, k⟩).2⟩ : Σ j : Fin w, Fin (c j)) = e ⟨s, k⟩ := rfl
    rw [e1, hfac] at this
    omega
  -- X00-components
  have hmon00 : ∀ σ s, (mon σ s) (0, 0) = (n - a s) +
      (Finset.univ.filter (fun k : Fin (a s) => ((σ (e ⟨s, k⟩).1 (e ⟨s, k⟩).2 : Fin _) : ℕ) = 0)).card := by
    intro σ s
    simp only [hmon, Finsupp.add_apply, Finsupp.single_eq_same, p2_g3S_00]
    rfl
  have hid00 : ∀ s ∈ body, (mon idv s) (0, 0) = n - a s := by
    intro s hs
    rw [hmon00]
    have hs2 : 2 ≤ a s := (Finset.mem_filter.1 hs).2
    have : (Finset.univ.filter (fun k : Fin (a s) =>
        ((idv (e ⟨s, k⟩).1 (e ⟨s, k⟩).2 : Fin _) : ℕ) = 0)) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro k _
      simp only [hidv, Equiv.Perm.coe_one, id]
      exact hcellrow s k hs2
    rw [this, Finset.card_empty, add_zero]
  have hsingle00 : (Finsupp.single (0, 0) n : (ℕ × ℕ) →₀ ℕ) (0, 0) = n := Finsupp.single_eq_same
  -- coefficients of p0
  have hcoeff : ∀ m, coeff m p0 = (if Finsupp.single (0, 0) n = m then 1 else 0) +
      ∑ s ∈ body, (if mon idv s = m then 1 else 0) := by
    intro m
    rw [hp0, coeff_add, coeff_monomial, coeff_sum]
    simp only [coeff_monomial]
  -- if a monomial of X00-degree < n has nonzero coefficient, it is the monomial of a body factor
  have hsupp : ∀ m, coeff m p0 ≠ 0 → m (0, 0) < n → ∃ s ∈ body, mon idv s = m := by
    intro m hm hlt
    rw [hcoeff, if_neg (by intro h; rw [← h, hsingle00] at hlt; exact lt_irrefl _ hlt), zero_add] at hm
    by_contra hno
    push Not at hno
    apply hm
    apply Finset.sum_eq_zero
    intro s hs
    rw [if_neg (hno s hs)]
  -- step A: row-0 cells are fixed
  have hA : ∀ σ : (j : Fin w) → Equiv.Perm (Fin (c j)), (∀ s, coeff (mon σ s) p0 ≠ 0) →
      ∀ x : Σ j : Fin w, Fin (c j), (x.2 : ℕ) = 0 → ((σ x.1 x.2 : Fin _) : ℕ) = 0 := by
    intro σ hall x hx
    set s := (e.symm x).1 with hs
    have has : a s = 1 := hrow0 x.1 x.2 hx
    set k0 := (e.symm x).2 with hk0
    have hek : e ⟨s, k0⟩ = x := by
      rw [show (⟨s, k0⟩ : Σ s : Fin t, Fin (a s)) = e.symm x from rfl, Equiv.apply_symm_apply]
    have hall_k : ∀ k : Fin (a s), k = k0 := by
      intro k
      apply Fin.ext
      have h1 : (k : ℕ) < 1 := has ▸ k.isLt
      have h2 : (k0 : ℕ) < 1 := has ▸ k0.isLt
      omega
    by_contra hne
    have hcnt : (Finset.univ.filter (fun k : Fin (a s) =>
        ((σ (e ⟨s, k⟩).1 (e ⟨s, k⟩).2 : Fin _) : ℕ) = 0)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _
      rw [hall_k k, hek]
      exact hne
    have h00 : (mon σ s) (0, 0) < n := by
      rw [hmon00, hcnt, has]; omega
    obtain ⟨s', hs', heq⟩ := hsupp _ (hall s) h00
    have h1 := hid00 s' hs'
    rw [heq, hmon00, hcnt, has] at h1
    have : 2 ≤ a s' := (Finset.mem_filter.1 hs').2
    have := han s'
    omega
  -- step B: body cells are not sent to row 0
  have hB : ∀ σ : (j : Fin w) → Equiv.Perm (Fin (c j)), (∀ s, coeff (mon σ s) p0 ≠ 0) →
      ∀ x : Σ j : Fin w, Fin (c j), (x.2 : ℕ) ≠ 0 → ((σ x.1 x.2 : Fin _) : ℕ) ≠ 0 := by
    intro σ hall x hx h0
    have hc0 : 0 < c x.1 := by have := x.2.isLt; omega
    have hfix := hA σ hall ⟨x.1, ⟨0, hc0⟩⟩ rfl
    have : σ x.1 x.2 = σ x.1 ⟨0, hc0⟩ := Fin.ext (by rw [h0]; exact hfix.symm)
    have := (σ x.1).injective this
    rw [this] at hx
    exact hx rfl
  -- step C: each body factor hits its own monomial
  have hC : ∀ σ : (j : Fin w) → Equiv.Perm (Fin (c j)), (∀ s, coeff (mon σ s) p0 ≠ 0) →
      ∀ s ∈ body, mon σ s = mon idv s := by
    intro σ hall s hs
    have hs2 : 2 ≤ a s := (Finset.mem_filter.1 hs).2
    have hcnt : (Finset.univ.filter (fun k : Fin (a s) =>
        ((σ (e ⟨s, k⟩).1 (e ⟨s, k⟩).2 : Fin _) : ℕ) = 0)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _
      exact hB σ hall (e ⟨s, k⟩) (hcellrow s k hs2)
    have h00 : (mon σ s) (0, 0) < n := by
      rw [hmon00, hcnt]; have := han s; omega
    obtain ⟨s', hs', heq⟩ := hsupp _ (hall s) h00
    have h1 := hid00 s' hs'
    rw [heq, hmon00, hcnt] at h1
    have hs'2 : 2 ≤ a s' := (Finset.mem_filter.1 hs').2
    have hss : s = s' := hdist s s' hs2 hs'2 (by have := han s; have := han s'; omega)
    subst hss; exact heq.symm
  -- the key: only the identity assignment survives
  have hkey : ∀ σ : (j : Fin w) → Equiv.Perm (Fin (c j)), (∀ s, coeff (mon σ s) p0 ≠ 0) →
      σ = idv := by
    intro σ hall
    -- row sums per body factor
    have hsum : ∀ s ∈ body, ∑ k : Fin (a s), ((σ (e ⟨s, k⟩).1 (e ⟨s, k⟩).2 : Fin _) : ℕ) =
        ∑ k : Fin (a s), ((e ⟨s, k⟩).2 : ℕ) := by
      intro s hs
      have h := congrArg p2psi (hC σ hall s hs)
      simp only [hmon, map_add, p2_psi_g3S] at h
      have h0 : p2psi (Finsupp.single (0, 0) (n - a s)) = 0 := by
        simp only [p2psi, Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_mulRight]; rfl
      rw [h0, zero_add, zero_add] at h
      simpa [TD.var, hidv] using h
    by_contra hne
    have hbad : ∃ x : Σ j : Fin w, Fin (c j), σ x.1 x.2 ≠ x.2 := by
      by_contra hno
      push Not at hno
      apply hne
      funext j
      apply Equiv.ext
      intro i
      exact hno ⟨j, i⟩
    obtain ⟨x, hxbad, hxmax⟩ := Finset.exists_max_image
      (Finset.univ.filter (fun x : Σ j : Fin w, Fin (c j) => σ x.1 x.2 ≠ x.2))
      (fun x => (e.symm x).1) (by
        obtain ⟨x, hx⟩ := hbad
        exact ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩⟩)
    have hxb : σ x.1 x.2 ≠ x.2 := (Finset.mem_filter.1 hxbad).2
    set s := (e.symm x).1 with hs
    have hx0 : (x.2 : ℕ) ≠ 0 := by
      intro h0
      apply hxb
      apply Fin.ext
      rw [hA σ hall x h0, h0]
    have hs2 : 2 ≤ a s := hbody x.1 x.2 hx0
    have hsb : s ∈ body := Finset.mem_filter.2 ⟨Finset.mem_univ _, hs2⟩
    -- every cell of s is sent weakly upward
    have hle : ∀ k : Fin (a s), ((σ (e ⟨s, k⟩).1 (e ⟨s, k⟩).2 : Fin _) : ℕ) ≤ ((e ⟨s, k⟩).2 : ℕ) := by
      intro k
      have := p2_perm_le (σ (e ⟨s, k⟩).1) (e ⟨s, k⟩).2 (by
        intro i' hi'
        by_contra hb
        have hmem : (⟨(e ⟨s, k⟩).1, i'⟩ : Σ j : Fin w, Fin (c j)) ∈
            Finset.univ.filter (fun x : Σ j : Fin w, Fin (c j) => σ x.1 x.2 ≠ x.2) :=
          Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩
        have h1 := hxmax _ hmem
        have h2 := hcol (e ⟨s, k⟩).1 (e ⟨s, k⟩).2 i' hi'
        have e1 : (⟨(e ⟨s, k⟩).1, (e ⟨s, k⟩).2⟩ : Σ j : Fin w, Fin (c j)) = e ⟨s, k⟩ := rfl
        rw [e1, hfac] at h2
        exact absurd (lt_of_lt_of_le h2 h1) (lt_irrefl _))
      exact this
    have heq := (Finset.sum_eq_sum_iff_of_le (fun k _ => hle k)).1 (hsum s hsb)
    set k0 := (e.symm x).2 with hk0
    have hek : e ⟨s, k0⟩ = x := by
      rw [show (⟨s, k0⟩ : Σ s : Fin t, Fin (a s)) = e.symm x from rfl, Equiv.apply_symm_apply]
    have := heq k0 (Finset.mem_univ _)
    rw [hek] at this
    exact hxb (Fin.ext this)
  -- evaluate
  unfold GCTOcc.evalCoeff p2F
  rw [map_sum]
  simp only [map_mul, map_prod, eval_C, eval_X]
  rw [Finset.sum_eq_single idv]
  · -- the identity term
    have hsign : ((((∏ j, (Equiv.Perm.sign (idv j) : ℤ)) : ℤ) : ℂ)) = 1 := by
      simp [hidv]
    rw [hsign, one_mul]
    rw [Finset.prod_ne_zero_iff]
    intro s _
    refine mul_ne_zero (g3w_ne_zero _ _ _ _) ?_
    show coeff (mon idv s) p0 ≠ 0
    rw [hcoeff]
    by_cases hs2 : 2 ≤ a s
    · have hsb : s ∈ body := Finset.mem_filter.2 ⟨Finset.mem_univ _, hs2⟩
      rw [if_neg (by
        intro h
        have := congrArg (fun m : (ℕ × ℕ) →₀ ℕ => m (0, 0)) h
        rw [hsingle00, hid00 s hsb] at this
        have := han s
        omega)]
      rw [zero_add, Finset.sum_eq_single s]
      · rw [if_pos rfl]; exact one_ne_zero
      · intro s' hs' hne
        rw [if_neg]
        intro h
        have h1 := congrArg (fun m : (ℕ × ℕ) →₀ ℕ => m (0, 0)) h
        rw [hid00 s' hs', hid00 s hsb] at h1
        have := han s; have := han s'
        exact hne (hdist s' s (Finset.mem_filter.1 hs').2 hs2 (by omega))
      · intro h; exact absurd hsb h
    · -- content 1: the monomial is X00^n
      have has : a s = 1 := by have := hpos s; omega
      have hm : mon idv s = Finsupp.single (0, 0) n := by
        ext v
        simp only [hmon, Finsupp.add_apply]
        unfold g3S
        rw [Finsupp.finsetSum_apply]
        have hk : ∀ k : Fin (a s), ((TD.var hc idv (e ⟨s, k⟩) : Fin K) : ℕ) = 0 := by
          intro k
          simp only [TD.var, hidv, Equiv.Perm.coe_one, id, Fin.val_castLE]
          exact hcell0 s k (by omega)
        have hsum1 : ∑ k : Fin (a s), (Finsupp.single ((0 : ℕ), ((TD.var hc idv (e ⟨s, k⟩) : Fin K) : ℕ)) 1 : (ℕ × ℕ) →₀ ℕ) v
            = (Finsupp.single (0, 0) 1 : (ℕ × ℕ) →₀ ℕ) v * (a s) := by
          simp_rw [hk]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
        rw [hsum1, has, mul_one, ← Finsupp.add_apply, ← Finsupp.single_add]
        congr 2
        omega
      rw [hm, if_pos rfl]
      have hz : ∑ s' ∈ body, (if mon idv s' = Finsupp.single (0, 0) n then (1 : ℂ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro s' hs'
        rw [if_neg]
        intro h
        have h1 := congrArg (fun m : (ℕ × ℕ) →₀ ℕ => m (0, 0)) h
        rw [hid00 s' hs', hsingle00] at h1
        have : 2 ≤ a s' := (Finset.mem_filter.1 hs').2
        have := han s'
        omega
      rw [hz, add_zero]; exact one_ne_zero
  · intro σ _ hσ
    by_contra hne
    apply hσ
    apply hkey σ
    intro s
    have hne' := (mul_ne_zero_iff.1 hne).2
    have := (Finset.prod_ne_zero_iff.1 hne') s (Finset.mem_univ _)
    exact (mul_ne_zero_iff.1 this).2
  · intro h; exact absurd (Finset.mem_univ _) h


theorem p2_degree_g3S (K l : ℕ) (y : Fin l → Fin K) : Finsupp.degree (g3S K l y) = l := by
  unfold g3S
  rw [map_sum]
  simp

open GCTOcc in
/-- P2: a tableau weight occurs in the determinant orbit closure. -/
theorem p2_occurs (n w K t S : ℕ) (hK1 : 1 ≤ K) (hK : K ≤ n) (c : Fin w → ℕ)
    (hc : ∀ j, c j ≤ K) (a : Fin t → ℕ) (e : (Σ s : Fin t, Fin (a s)) ≃ (Σ j : Fin w, Fin (c j)))
    (hcol : ∀ j (i i' : Fin (c j)), i < i' → (e.symm ⟨j, i⟩).1 < (e.symm ⟨j, i'⟩).1)
    (hrow0 : ∀ j (i : Fin (c j)), (i : ℕ) = 0 → a (e.symm ⟨j, i⟩).1 = 1)
    (hbody : ∀ j (i : Fin (c j)), (i : ℕ) ≠ 0 → 2 ≤ a (e.symm ⟨j, i⟩).1)
    (hdist : ∀ s s', 2 ≤ a s → 2 ≤ a s' → a s = a s' → s = s')
    (hpos : ∀ s, 1 ≤ a s) (hS : ∀ s, a s ≤ S) (hSn : (1 + t) * S ≤ n) :
    Occurs n t (p2lam (∑ s, (n - a s)) w c) (orbitClosure n (detPoly n)) := by
  classical
  have hn1 : 1 ≤ n := le_trans hK1 hK
  have hSle : S ≤ n := le_trans (Nat.le_mul_of_pos_left S (by omega)) hSn
  have han : ∀ s, a s ≤ n := fun s => le_trans (hS s) hSle
  set body := Finset.univ.filter (fun s : Fin t => 2 ≤ a s) with hbodyS
  set β : Fin t → ((ℕ × ℕ) →₀ ℕ) := fun s => g3S K (a s) (fun k => TD.var hc (fun _ => 1) (e ⟨s, k⟩))
    with hβ
  set h0 : PolyR := monomial (Finsupp.single (0, 0) S) 1 +
    ∑ s ∈ body, monomial (Finsupp.single (0, 0) (S - a s) + β s) 1 with hh0
  have hp0 : X (0, 0) ^ (n - S) * h0 = monomial (Finsupp.single (0, 0) n) 1 +
      ∑ s ∈ body, monomial (Finsupp.single (0, 0) (n - a s) + β s) 1 := by
    rw [hh0, mul_add, Finset.mul_sum, X_pow_eq_monomial, monomial_mul, one_mul,
      ← Finsupp.single_add, show n - S + S = n by omega]
    congr 1
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [monomial_mul, one_mul, ← add_assoc, ← Finsupp.single_add,
      show n - S + (S - a s) = n - a s by have := hS s; omega]
  -- support of h0
  have hsupp : h0.support ⊆ insert (Finsupp.single (0, 0) S)
      (body.image (fun s => Finsupp.single (0, 0) (S - a s) + β s)) := by
    intro m hm
    rw [hh0] at hm
    rcases Finset.mem_union.1 (support_add hm) with h1 | h1
    · have := support_monomial_subset h1
      rw [Finset.mem_singleton] at this
      exact Finset.mem_insert.2 (Or.inl this)
    · have := support_sum h1
      simp only [Finset.mem_biUnion] at this
      obtain ⟨s, hs, hms⟩ := this
      have := support_monomial_subset hms
      rw [Finset.mem_singleton] at this
      exact Finset.mem_insert.2 (Or.inr (Finset.mem_image.2 ⟨s, hs, this.symm⟩))
  have hdeg : ∀ μ ∈ h0.support, Finsupp.degree μ = S := by
    intro μ hμ
    rcases Finset.mem_insert.1 (hsupp hμ) with h1 | h1
    · rw [h1, Finsupp.degree_single]
    · obtain ⟨s, _, hs⟩ := Finset.mem_image.1 h1
      rw [← hs, map_add, Finsupp.degree_single, hβ, p2_degree_g3S]
      have := hS s
      omega
  have hhom : h0.IsHomogeneous S := by
    intro μ hμ
    have := hdeg μ (mem_support_iff.2 hμ)
    rwa [Finsupp.degree_eq_weight_one] at this
  have hcard : h0.support.card * S ≤ n := by
    have h1 : h0.support.card ≤ 1 + t := by
      calc h0.support.card ≤ (insert (Finsupp.single (0, 0) S)
            (body.image (fun s => Finsupp.single (0, 0) (S - a s) + β s))).card :=
            Finset.card_le_card hsupp
        _ ≤ (body.image (fun s => Finsupp.single (0, 0) (S - a s) + β s)).card + 1 :=
            Finset.card_insert_le _ _
        _ ≤ body.card + 1 := by
            have := Finset.card_image_le (s := body) (f := fun s => Finsupp.single (0, 0) (S - a s) + β s)
            omega
        _ ≤ t + 1 := by
            have := Finset.card_le_univ body
            simp only [Fintype.card_fin] at this
            omega
        _ = 1 + t := by ring
    calc h0.support.card * S ≤ (1 + t) * S := Nat.mul_le_mul_right _ h1
      _ ≤ n := hSn
  have hblock : ∀ μ ∈ h0.support, ∀ v ∈ μ.support, v.1 < n ∧ v.2 < n := by
    intro μ hμ v hv
    rcases Finset.mem_insert.1 (hsupp hμ) with h1 | h1
    · rw [h1] at hv
      have := Finsupp.support_single_subset hv
      rw [Finset.mem_singleton] at this
      rw [this]; exact ⟨by omega, by omega⟩
    · obtain ⟨s, _, hs⟩ := Finset.mem_image.1 h1
      rw [← hs] at hv
      rcases Finset.mem_union.1 (Finsupp.support_add hv) with h2 | h2
      · have := Finsupp.support_single_subset h2
        rw [Finset.mem_singleton] at this
        rw [this]; exact ⟨by omega, by omega⟩
      · rw [hβ] at h2
        unfold g3S at h2
        have := Finsupp.support_finset_sum h2
        simp only [Finset.mem_biUnion] at this
        obtain ⟨k, _, hk⟩ := this
        have := Finsupp.support_single_subset hk
        rw [Finset.mem_singleton] at this
        rw [this]
        refine ⟨by simp; omega, ?_⟩
        simp only
        have := (TD.var hc (fun _ => 1) (e ⟨s, k⟩)).isLt
        omega
  have hsd : IsSymbolicDet h0 n := symbolicDet_of_few_monomials n S hn1 h0 hdeg hcard
  have hmem := padded_mem_orbitClosure_of_symbolicDet n S hSle h0 hhom hblock hsd
  rw [hp0] at hmem
  exact ⟨p2F n w K t c hc a e, p2_hwv n w K t hK1 hK c hc a e, _, hmem,
    p2_nonvanish n w K t hn1 c hc a e hcol hrow0 hbody hdist han hpos⟩

/-! ===== G1-only part (kl_shape_pos) ===== -/

/-- Rows half of G1 at orbit points: if `lam` is positive on `0, …, m*m` then every HWV of weight
`lam` vanishes at every `g`-substitution of the padded permanent. -/
theorem kl_rows_vanish (n d m : ℕ) (hm : 0 < m) (hmn : m < n) (lam : ℕ → ℕ)
    (F : GCTOcc.CoordRing) (hF : GCTOcc.IsHWV n d lam F) (hpos : ∀ k ≤ m * m, 0 < lam k)
    (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    GCTOcc.evalCoeff (GCTOcc.substLin n g (GCTOcc.paddedPerm m n)) F = 0 := by
  classical
  set e : Fin n × Fin n ≃ Fin (n * n) := finProdFinEquiv with he_def
  have hMN : m * m < n * n := Nat.mul_self_lt_mul_self hmn
  let col : ℕ → (Fin m × Fin m → ℂ) := fun k ab =>
    if hk : k < n * n then
      g (⟨ab.1, lt_trans ab.1.isLt hmn⟩, ⟨ab.2, lt_trans ab.2.isLt hmn⟩) (e.symm ⟨k, hk⟩)
    else 0
  obtain ⟨k, hkM, hspan⟩ := kl_exists_dep col (m * m) (by simp [Module.finrank_fintype_fun_eq_card])
  have hkN : k < n * n := lt_of_le_of_lt hkM hMN
  set wk : Fin n × Fin n := e.symm ⟨k, hkN⟩ with hwk
  have hidxwk : GCTOcc.idx n wk = k := by
    rw [← kl_idx_eq, hwk, he_def]; simp; exact Nat.mod_add_div k n
  obtain ⟨l, hl, hlc⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).1 hspan
  have hl0 : ∀ i, k ≤ i → l i = 0 := by
    intro i hi
    by_contra hne
    have := hl (Finsupp.mem_support_iff.2 hne)
    simp at this
    omega
  let b : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ := fun x y =>
    (if x = y then 1 else 0) - (if y = wk then l (GCTOcc.idx n x) else 0)
  have hb1 : ∀ v, b v v = 1 := by
    intro v
    by_cases hv : v = wk
    · subst hv; simp [b, hidxwk, hl0 k le_rfl]
    · simp [b, hv]
  have hbup : GCTOcc.IsUpperTri n b := by
    intro x y hxy
    have hne : x ≠ y := by rintro rfl; exact lt_irrefl _ hxy
    by_cases hy : y = wk
    · subst hy
      have hk' : k ≤ GCTOcc.idx n x := by rw [hidxwk] at hxy; omega
      simp [b, hne, hl0 _ hk']
    · simp [b, hne, hy]
  have hzero : ∀ v : Fin n × Fin n, (v.1 : ℕ) < m → (v.2 : ℕ) < m → (g * b) v wk = 0 := by
    intro v hv1 hv2
    have hab := congrFun hlc ((⟨v.1, hv1⟩ : Fin m), (⟨v.2, hv2⟩ : Fin m))
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset l (s := Finset.range (n * n)) (by
        intro i hi
        have := hl hi
        simp at this ⊢
        omega) _ (by simp)] at hab
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hab
    rw [Finset.sum_range (fun i => l i * col i _)] at hab
    rw [← e.sum_comp] at hab
    simp only [col, Fin.is_lt, dif_pos, Fin.eta, Equiv.symm_apply_apply, kl_idx_eq, hkN] at hab
    simp only [Prod.mk.eta] at hab
    have hab' : ∑ x, g v x * l (GCTOcc.idx n x) = g v wk := by
      rw [hwk, ← hab]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [he_def, kl_idx_eq, mul_comm]
    rw [Matrix.mul_apply]
    simp only [b, ↓reduceIte, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ]
    rw [hab', sub_self]
  have hform0 := kl_isForm_paddedPerm m n hm hmn.le
  have hform1 := kl_isForm_substLin n g _ hform0
  have h1 : GCTOcc.evalCoeff (GCTOcc.substLin n (g * b) (GCTOcc.paddedPerm m n)) F
      = GCTOcc.evalCoeff (GCTOcc.substLin n g (GCTOcc.paddedPerm m n)) F := by
    rw [← kl_substLin_mul]
    exact kl_hwv_unipotent hF b hbup hb1 _ hform1
  have h2 : GCTOcc.evalCoeff (GCTOcc.substLin n (g * b) (GCTOcc.paddedPerm m n)) F = 0 := by
    apply kl_hwv_kill hF wk (by rw [hidxwk]; exact hpos k hkM) _ (kl_isForm_substLin n _ _ hform0)
    rw [kl_substLin_mul]
    apply kl_substLin_congr n m hmn.le _ (kl_paddedPerm_supported m n hm)
    intro v hv1 hv2
    funext y
    simp only [klDiag, Matrix.mul_diagonal]
    by_cases hy : y = wk
    · subst hy; simp [hzero v hv1 hv2]
    · simp [hy]
  rw [← h1, h2]

/-- The elementary matrix with a single `1` at `(v0, v0)`. -/
noncomputable def klE (n : ℕ) (v0 : Fin n × Fin n) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun x y => if x = v0 ∧ y = v0 then 1 else 0

theorem kl_diag_line (n : ℕ) (v0 : Fin n × Fin n) (t : ℂ) :
    klDiag n v0 t = klDiag n v0 0 + t • klE n v0 := by
  ext x y
  simp only [klDiag, klE, Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy; by_cases hx : x = v0 <;> simp [hx]
  · simp [hxy]
    intro h1 h2
    exact absurd (h1.trans h2.symm) hxy

theorem kl_gctPF_coeff_mul_line (n : ℕ) (A B : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (P Q : GCTOcc.PolyR) (μ : (ℕ × ℕ) →₀ ℕ) :
    gctPF (fun t => coeff μ (P * GCTOcc.substLin n (A + t • B) Q)) := by
  classical
  simp only [coeff_mul]
  exact gctPF_sum _ _ (fun x _ => gctPF_mul (gctPF_const _) (gct_coeff_substLin_line n A B Q x.2))

/-- Body half of G1 at an orbit point with `g v0 v0 ≠ 0`. -/
theorem kl_body_core (n d m : ℕ) (hm : 0 < m) (hmn : m ≤ n) (lam : ℕ → ℕ)
    (F : GCTOcc.CoordRing) (hF : GCTOcc.IsHWV n d lam F)
    (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hg0 : g (⟨0, lt_of_lt_of_le hm hmn⟩, ⟨0, lt_of_lt_of_le hm hmn⟩)
      (⟨0, lt_of_lt_of_le hm hmn⟩, ⟨0, lt_of_lt_of_le hm hmn⟩) ≠ 0)
    (hg : GCTOcc.evalCoeff (GCTOcc.substLin n g (GCTOcc.paddedPerm m n)) F ≠ 0) :
    (n - m) * d ≤ lam 0 := by
  classical
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  set v0 : Fin n × Fin n := (⟨0, hn⟩, ⟨0, hn⟩) with hv0
  have hidx0 : GCTOcc.idx n v0 = 0 := by simp [GCTOcc.idx, hv0]
  set c := g v0 v0 with hc
  let b : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ := fun x y =>
    (if x = y then 1 else 0) + (if y = v0 then 0 else if x = v0 then -(g v0 y / c) else 0)
  have hb1 : ∀ v, b v v = 1 := by
    intro v
    by_cases hv : v = v0 <;> simp [b, hv]
  have hbup : GCTOcc.IsUpperTri n b := by
    intro x y hxy
    have hne : x ≠ y := by rintro rfl; exact lt_irrefl _ hxy
    have hx : x ≠ v0 := by rintro rfl; rw [hidx0] at hxy; exact Nat.not_lt_zero _ hxy
    simp [b, hne, hx]
  set h := g * b with hh
  have hrow : ∀ y, h v0 y = if y = v0 then c else 0 := by
    intro y
    rw [hh, Matrix.mul_apply]
    simp only [b, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    by_cases hy : y = v0
    · subst hy; simp [hc]
    · simp only [hy, if_false, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      field_simp
      ring
  have hform0 := kl_isForm_paddedPerm m n hm hmn
  have hFh : GCTOcc.evalCoeff (GCTOcc.substLin n h (GCTOcc.paddedPerm m n)) F ≠ 0 := by
    rw [hh, ← kl_substLin_mul, kl_hwv_unipotent hF b hbup hb1 _ (kl_isForm_substLin n g _ hform0)]
    exact hg
  set Q := GCTOcc.substLin n h (GCTOcc.permPoly m) with hQ
  have hX : ∀ M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ, (∀ y, y ≠ v0 → M v0 y = 0) →
      GCTOcc.substLin n M (X (0, 0)) = C (M v0 v0) * X (0, 0) := by
    intro M hM
    have := kl_substLin_X_block n M ⟨0, hn⟩ ⟨0, hn⟩
    simp only [Fin.val_mk] at this
    rw [this, Finset.sum_eq_single v0]
    · intro y _ hy; rw [hM y hy]; simp
    · simp
  have hp0h : GCTOcc.substLin n h (GCTOcc.paddedPerm m n) = (C c * X (0, 0)) ^ (n - m) * Q := by
    rw [hQ, GCTOcc.paddedPerm, GCTOcc.substLin, map_mul, map_pow, ← GCTOcc.substLin,
      ← GCTOcc.substLin, hX h (fun y hy => by rw [hrow y, if_neg hy])]
    rw [hrow v0, if_pos rfl]
  -- the scaling identity
  have hscale : ∀ t : ℂ, t ≠ 0 →
      t ^ lam 0 * GCTOcc.evalCoeff (GCTOcc.substLin n h (GCTOcc.paddedPerm m n)) F
        = t ^ ((n - m) * d) * GCTOcc.evalCoeff ((C c * X (0, 0)) ^ (n - m) *
            GCTOcc.substLin n (klDiag n v0 0 + t • klE n v0) Q) F := by
    intro t ht
    have h1 := kl_hwv_diag hF v0 t ht _ (kl_isForm_substLin n h _ hform0)
    rw [hidx0] at h1
    rw [← h1, hp0h, GCTOcc.substLin, map_mul, map_pow, map_mul, aeval_C, ← GCTOcc.substLin,
      ← GCTOcc.substLin, hX (klDiag n v0 t) (fun y hy => by simp [klDiag, Matrix.diagonal_apply_ne _ (Ne.symm hy)]),
      ← kl_diag_line]
    have : (algebraMap ℂ GCTOcc.PolyR c * (C (klDiag n v0 t v0 v0) * X (0, 0))) ^ (n - m) *
        GCTOcc.substLin n (klDiag n v0 t) Q
        = C (t ^ (n - m)) * ((C c * X (0, 0)) ^ (n - m) * GCTOcc.substLin n (klDiag n v0 t) Q) := by
      simp only [klDiag, Matrix.diagonal_apply_eq, if_pos rfl, algebraMap_eq, map_pow, if_true,
        ↓reduceIte]
      ring
    rw [this, kl_evalCoeff_C_mul F d hF.1, ← pow_mul]
  set K := GCTOcc.evalCoeff (GCTOcc.substLin n h (GCTOcc.paddedPerm m n)) F with hK
  by_contra hlt
  push_neg at hlt
  set k := (n - m) * d - lam 0 with hk
  have hk1 : 1 ≤ k := by omega
  have hφ : gctPF (fun t => t ^ k * GCTOcc.evalCoeff ((C c * X (0, 0)) ^ (n - m) *
      GCTOcc.substLin n (klDiag n v0 0 + t • klE n v0) Q) F - K) := by
    have hpow : gctPF (fun t : ℂ => t ^ k) := by
      simpa using gctPF_prod (Finset.range k) (fun _ t => t) (fun _ _ => gctPF_id)
    have hev : gctPF (fun t => GCTOcc.evalCoeff ((C c * X (0, 0)) ^ (n - m) *
        GCTOcc.substLin n (klDiag n v0 0 + t • klE n v0) Q) F) := by
      unfold GCTOcc.evalCoeff
      exact gctPF_evalF F _ (fun μ => kl_gctPF_coeff_mul_line n _ _ _ _ μ)
    simpa [sub_eq_add_neg] using gctPF_add (gctPF_mul hpow hev) (gctPF_const (-K))
  have hz := gctPF_finite_zeros hφ (t₀ := 0) (by
    simp only [zero_pow (by omega : k ≠ 0), zero_mul, zero_sub, neg_ne_zero]
    exact hFh)
  apply (Set.finite_singleton (0 : ℂ)).infinite_compl
  refine hz.subset (fun t ht => ?_)
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
  simp only [Set.mem_setOf_eq, sub_eq_zero]
  have e1 := hscale t ht
  have e2 : (n - m) * d = lam 0 + k := by omega
  rw [e2, pow_add, mul_assoc] at e1
  exact (mul_left_cancel₀ (pow_ne_zero _ ht) e1).symm

/-- Body half of G1 at any orbit point where the HWV does not vanish. -/
theorem kl_body_bound (n d m : ℕ) (hm : 0 < m) (hmn : m ≤ n) (lam : ℕ → ℕ)
    (F : GCTOcc.CoordRing) (hF : GCTOcc.IsHWV n d lam F)
    (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hg : GCTOcc.evalCoeff (GCTOcc.substLin n g (GCTOcc.paddedPerm m n)) F ≠ 0) :
    (n - m) * d ≤ lam 0 := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  set v0 : Fin n × Fin n := (⟨0, hn⟩, ⟨0, hn⟩) with hv0
  have z := gctPF_finite_zeros (gctPF_evalCoeff_line n g (klE n v0) (GCTOcc.paddedPerm m n) F)
    (t₀ := 0) (by simpa using hg)
  obtain ⟨t, -, ht⟩ := Set.infinite_univ.exists_notMem_finite
    (z.union (Set.finite_singleton (-g v0 v0)))
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff, not_or] at ht
  refine kl_body_core n d m hm hmn lam F hF (g + t • klE n v0) ?_ ht.1
  have : (g + t • klE n v0) v0 v0 = g v0 v0 + t := by simp [klE]
  rw [this]
  intro h0
  exact ht.2 (by linear_combination h0)

/-- G1: Kadish–Landsberg shape restriction, corrected to `0 < m`. -/
theorem kl_shape_pos (n d m : ℕ) (hm : 0 < m) (hmn : m ≤ n) (lam : ℕ → ℕ)
    (hlam : GCTOcc.IsPartitionOf lam (n * n) (n * d))
    (h : GCTOcc.Occurs n d lam (GCTOcc.orbitClosure n (GCTOcc.paddedPerm m n))) :
    (∀ i, m * m ≤ i → lam i = 0) ∧ (∑ i ∈ Finset.range (n * n), lam (i + 1)) ≤ m * d := by
  obtain ⟨F, hF, p, hp, hne⟩ := h
  obtain ⟨g, -, hg⟩ := gct_orbit_of_closure hp F hne
  have hanti : Antitone lam := antitone_nat_of_succ_le hlam.1
  refine ⟨fun i hi => ?_, ?_⟩
  · by_contra hpos
    rcases lt_or_eq_of_le hmn with hlt | heq
    · exact hg (kl_rows_vanish n d m hm hlt lam F hF
        (fun k hk => lt_of_lt_of_le (Nat.pos_of_ne_zero hpos) (hanti (le_trans hk hi))) g)
    · subst heq
      exact hpos (hlam.2.1 i hi)
  · have hb := kl_body_bound n d m hm hmn lam F hF g hg
    have h1 := Finset.sum_range_succ' lam (n * n)
    have h2 := Finset.sum_range_succ lam (n * n)
    have h0 := hlam.2.2
    have hN := hlam.2.1 (n * n) le_rfl
    have h3 : (n - m) * d + m * d = n * d := by rw [← Nat.add_mul, Nat.sub_add_cancel hmn]
    omega

/-! ===== P1 (a586c963 session 7): an HWV with small body is nonvanishing on Omega_n,
in any degree. The X00-weight bounds the number of distinct monomials by body + 1. ===== -/

theorem p1_coeff_aeval_scale {σ : Type} (c : σ → ℂ) (G : MvPolynomial σ ℂ) (α : σ →₀ ℕ) :
    coeff α (aeval (fun v => C (c v) * X v) G) = (α.prod fun v k => c v ^ k) * coeff α G := by
  classical
  have key : ∀ (s : σ →₀ ℕ) (a : ℂ), aeval (fun v => C (c v) * X v) (monomial s a)
      = monomial s (a * s.prod fun v k => c v ^ k) := by
    intro s a
    rw [aeval_monomial, monomial_eq]
    simp only [mul_pow, Finsupp.prod_mul, algebraMap_eq, C_mul, ← map_pow]
    rw [map_finsuppProd C]
    ring
  conv_lhs => rw [G.as_sum]
  simp only [map_sum, key, coeff_sum, coeff_monomial]
  rw [Finset.sum_eq_single α]
  · simp [mul_comm]
  · intro b _ hb; simp [hb]
  · intro hα
    simp only [if_pos rfl]
    rw [notMem_support_iff.1 hα]; simp

theorem p1_weight_of_scale {σ : Type} (G : MvPolynomial σ ℂ) (w : σ → ℕ) (L : ℕ)
    (h : ∀ c : σ → ℂ, eval (fun v => (2 : ℂ) ^ w v * c v) G = (2 : ℂ) ^ L * eval c G)
    (α : σ →₀ ℕ) (hα : coeff α G ≠ 0) : (α.sum fun v k => w v * k) = L := by
  classical
  set G2 := aeval (fun v => C ((2 : ℂ) ^ w v) * X v) G with hG2
  have hG2' : G2 = C ((2 : ℂ) ^ L) * G := by
    apply MvPolynomial.funext
    intro c
    rw [hG2, kl_eval_aeval, map_mul, eval_C, ← h c]
    rw [show (fun j => eval c (C ((2 : ℂ) ^ w j) * X j)) = (fun v => (2 : ℂ) ^ w v * c v) from
      funext fun v => by simp]
  have hc := congrArg (coeff α) hG2'
  rw [hG2, p1_coeff_aeval_scale, coeff_C_mul] at hc
  have h1 : (α.prod fun v k => ((2 : ℂ) ^ w v) ^ k) = (2 : ℂ) ^ L := mul_right_cancel₀ hα hc
  have h2 : (α.prod fun v k => ((2 : ℂ) ^ w v) ^ k) = (2 : ℂ) ^ (α.sum fun v k => w v * k) := by
    rw [Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    rw [← pow_mul]
  rw [h2] at h1
  have h3 : ((2 ^ (α.sum fun v k => w v * k) : ℕ) : ℂ) = ((2 ^ L : ℕ) : ℂ) := by
    push_cast; exact h1
  exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective h3)

theorem p1_two_le_deg (μ : (ℕ × ℕ) →₀ ℕ) (v w : ℕ × ℕ) (hvw : v ≠ w) :
    μ v + μ w ≤ Finsupp.degree μ := by
  classical
  rw [Finsupp.degree_apply, ← Finset.sum_pair (f := fun i => μ i) hvw]
  calc ({v, w} : Finset (ℕ × ℕ)).sum (fun i => μ i)
      ≤ (μ.support ∪ {v, w}).sum (fun i => μ i) :=
        Finset.sum_le_sum_of_subset Finset.subset_union_right
    _ = μ.support.sum (fun i => μ i) := by
        symm
        apply Finset.sum_subset Finset.subset_union_left
        intro x _ hx
        exact Finsupp.notMem_support_iff.1 hx

theorem p1_lt_of_ne (μ : (ℕ × ℕ) →₀ ℕ) (s : ℕ) (hd : Finsupp.degree μ = s)
    (hne : μ ≠ Finsupp.single (0, 0) s) : μ (0, 0) < s := by
  have hle : μ (0, 0) ≤ s := hd ▸ Finsupp.le_degree (0, 0) μ
  by_contra hlt
  apply hne
  ext v
  by_cases hv : v = (0, 0)
  · subst hv; simp; omega
  · have := p1_two_le_deg μ v (0, 0) hv
    rw [Finsupp.single_apply, if_neg (Ne.symm hv)]
    omega

theorem p1_aeval_supported {σ : Type} (L : σ → MvPolynomial σ ℂ) (J : Set σ)
    (hL : ∀ ν, L ν ∈ supported ℂ J) (F : MvPolynomial σ ℂ) : aeval L F ∈ supported ℂ J := by
  induction F using MvPolynomial.induction_on with
  | C a => rw [aeval_C]; exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
  | mul_X p j hp => rw [map_mul, aeval_X]; exact Subalgebra.mul_mem _ hp (hL j)

theorem p1_few_monomials_w (n d s b : ℕ) (F : GCTOcc.CoordRing) (hFd : F.IsHomogeneous d)
    (L0 : ℕ) (hL0 : L0 + b = n * d) (hsn : s ≤ n) (h : GCTOcc.PolyR) (hh : h.IsHomogeneous s)
    (hscale : ∀ c : ((ℕ × ℕ) →₀ ℕ) → ℂ,
      GCTOcc.evalCoeff (X (0, 0) ^ (n - s) * ∑ μ ∈ h.support,
          monomial μ ((2 : ℂ) ^ ((n - s) + μ (0, 0)) * c μ)) F
        = (2 : ℂ) ^ L0 *
          GCTOcc.evalCoeff (X (0, 0) ^ (n - s) * ∑ μ ∈ h.support, monomial μ (c μ)) F)
    (hne : GCTOcc.evalCoeff (X (0, 0) ^ (n - s) * h) F ≠ 0) :
    ∃ h' : GCTOcc.PolyR, h'.support ⊆ h.support ∧ h'.support.card ≤ b + 1 ∧
      GCTOcc.evalCoeff (X (0, 0) ^ (n - s) * h') F ≠ 0 := by
  classical
  set P : GCTOcc.PolyR := X (0, 0) ^ (n - s) with hP
  set J := h.support with hJ
  let L : ((ℕ × ℕ) →₀ ℕ) → GCTOcc.CoordRing := fun ν =>
    ∑ μ ∈ J, C (coeff ν (P * monomial μ 1)) * X μ
  set G : GCTOcc.CoordRing := aeval L F with hG
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
    have hh' : (∑ μ ∈ J, monomial μ (coeff μ h)) = h := h.as_sum.symm
    rw [h0, map_zero, hh'] at h1
    exact h1.symm
  obtain ⟨α, hα⟩ := MvPolynomial.ne_zero_iff.1 hGne
  set T := α.support with hT
  have hαd : Finsupp.degree α = d := by
    rw [Finsupp.degree_eq_weight_one]; exact hGhom hα
  -- the X00-weight of α
  have hw : (α.sum fun μ k => ((n - s) + μ (0, 0)) * k) = L0 := by
    apply p1_weight_of_scale G (fun μ => (n - s) + μ (0, 0)) L0 _ α hα
    intro c
    rw [hval, hval]
    exact hscale c
  -- α only involves the monomials of h
  have hTJ : T ⊆ J := by
    have hsupp : G ∈ supported ℂ (J : Set ((ℕ × ℕ) →₀ ℕ)) := by
      rw [hG]
      apply p1_aeval_supported
      intro ν
      exact Subalgebra.sum_mem _ (fun μ hμ => Subalgebra.mul_mem _
        (Subalgebra.algebraMap_mem _ _) ((X_mem_supported (R := ℂ)).2 hμ))
    intro μ hμ
    have hv : μ ∈ G.vars := (mem_vars μ).2 ⟨α, Finsupp.mem_support_iff.2 hα, hμ⟩
    exact (mem_supported.1 hsupp) hv
  have hdegJ : ∀ μ ∈ J, Finsupp.degree μ = s := fun μ hμ => by
    rw [Finsupp.degree_eq_weight_one]; exact hh (mem_support_iff.1 hμ)
  have hle00 : ∀ μ ∈ J, μ (0, 0) ≤ s := fun μ hμ =>
    (hdegJ μ hμ) ▸ Finsupp.le_degree (0, 0) μ
  have hsum_d : ∑ μ ∈ T, α μ = d := by rw [← hαd, Finsupp.degree_apply]
  have hbsum : ∑ μ ∈ T, α μ * (s - μ (0, 0)) = b := by
    have e1 : ∑ μ ∈ T, α μ * ((n - s) + μ (0, 0)) = L0 := by
      rw [← hw, Finsupp.sum]
      exact Finset.sum_congr rfl (fun μ _ => mul_comm _ _)
    have e2 : ∑ μ ∈ T, (α μ * ((n - s) + μ (0, 0)) + α μ * (s - μ (0, 0))) = n * d := by
      rw [← hsum_d, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun μ hμ => ?_)
      have := hle00 μ (hTJ hμ)
      rw [← mul_add, mul_comm]
      congr 1; omega
    rw [Finset.sum_add_distrib, e1] at e2
    omega
  have hcardT : T.card ≤ b + 1 := by
    set x0 : (ℕ × ℕ) →₀ ℕ := Finsupp.single (0, 0) s with hx0
    have h1 : (T.erase x0).card ≤ b := by
      rw [← hbsum]
      calc (T.erase x0).card = ∑ μ ∈ T.erase x0, 1 := by rw [Finset.card_eq_sum_ones]
        _ ≤ ∑ μ ∈ T.erase x0, α μ * (s - μ (0, 0)) := by
            apply Finset.sum_le_sum
            intro μ hμ
            have hμT := Finset.mem_of_mem_erase hμ
            have hne0 := Finset.ne_of_mem_erase hμ
            have hαμ : 1 ≤ α μ := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hμT)
            have hlt : μ (0, 0) < s := p1_lt_of_ne μ s (hdegJ μ (hTJ hμT)) hne0
            have h2 : 1 ≤ s - μ (0, 0) := by omega
            nlinarith
        _ ≤ ∑ μ ∈ T, α μ * (s - μ (0, 0)) :=
            Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
    by_cases hx : x0 ∈ T
    · rw [← Finset.card_erase_add_one hx]; omega
    · rw [Finset.erase_eq_of_notMem hx] at h1; omega
  -- restrict G to the variables in T
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
      _ ≤ b + 1 := hcardT

/-- `X00^k * Σ monomial μ (a μ)` as a single sum of monomials. -/
theorem p1_mul_sum (k : ℕ) (J : Finset ((ℕ × ℕ) →₀ ℕ)) (a : ((ℕ × ℕ) →₀ ℕ) → ℂ) :
    (X (0, 0) ^ k * ∑ μ ∈ J, monomial μ (a μ) : GCTOcc.PolyR)
      = ∑ μ ∈ J, monomial (Finsupp.single (0, 0) k + μ) (a μ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [X_pow_eq_monomial, monomial_mul, one_mul]

theorem p1_scale_form (n s : ℕ) (hn : 0 < n) (J : Finset ((ℕ × ℕ) →₀ ℕ))
    (c : ((ℕ × ℕ) →₀ ℕ) → ℂ) :
    GCTOcc.substLin n (klDiag n (⟨0, hn⟩, ⟨0, hn⟩) 2) (X (0, 0) ^ (n - s) * ∑ μ ∈ J, monomial μ (c μ))
      = X (0, 0) ^ (n - s) * ∑ μ ∈ J, monomial μ ((2 : ℂ) ^ ((n - s) + μ (0, 0)) * c μ) := by
  classical
  ext ν
  rw [kl_coeff_substLin_diag0, p1_mul_sum, p1_mul_sum]
  simp only [coeff_sum, coeff_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  split_ifs with heq
  · subst heq
    simp
  · simp

theorem p1_isForm (n s : ℕ) (hn : 0 < n) (hsn : s ≤ n) (h : GCTOcc.PolyR)
    (hh : h.IsHomogeneous s) (hhv : ∀ μ ∈ h.support, ∀ v ∈ μ.support, v.1 < n ∧ v.2 < n)
    (c : ((ℕ × ℕ) →₀ ℕ) → ℂ) :
    GCTOcc.IsForm n (X (0, 0) ^ (n - s) * ∑ μ ∈ h.support, monomial μ (c μ)) := by
  classical
  refine ⟨?_, ?_⟩
  · have h1 : (∑ μ ∈ h.support, monomial μ (c μ) : GCTOcc.PolyR).IsHomogeneous s := by
      apply IsHomogeneous.sum
      intro μ hμ
      apply isHomogeneous_monomial
      rw [Finsupp.degree_eq_weight_one]
      exact hh (mem_support_iff.1 hμ)
    have h2 := (isHomogeneous_X_pow (R := ℂ) (0, 0) (n - s)).mul h1
    rwa [show n - s + s = n by omega] at h2
  · rw [p1_mul_sum]
    intro m hm v hv
    have := support_sum hm
    simp only [Finset.mem_biUnion] at this
    obtain ⟨μ, hμ, hmμ⟩ := this
    have hsub := support_monomial_subset hmμ
    rw [Finset.mem_singleton] at hsub
    subst hsub
    have hv' := Finsupp.support_add hv
    rcases Finset.mem_union.1 hv' with h3 | h3
    · have := Finsupp.support_single_subset h3
      rw [Finset.mem_singleton] at this
      subst this
      exact ⟨hn, hn⟩
    · exact hhv μ hμ v h3

open GCTOcc in
/-- P1 (4a-lite): an HWV that is nonvanishing on some form and has body `b` with
`b * (b + 1) ≤ n` is nonvanishing on the determinant orbit closure, in every degree `d`. -/
theorem p1_small_body (n d b : ℕ) (lam : ℕ → ℕ)
    (hlam : IsPartitionOf lam (n * n) (n * d))
    (hbody : (∑ i ∈ Finset.range (n * n), lam (i + 1)) ≤ b) (hb : b * (b + 1) ≤ n)
    (F : CoordRing) (hF : IsHWV n d lam F) (hF0 : ∃ q : PolyR, IsForm n q ∧ evalCoeff q F ≠ 0) :
    ∃ p ∈ orbitClosure n (detPoly n), evalCoeff p F ≠ 0 := by
  classical
  obtain ⟨q, hq, hne⟩ := hF0
  have hFd : F.IsHomogeneous d := hF.1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hdet : detPoly 0 = 1 := by simp [detPoly]
    have hmem : (1 : PolyR) ∈ orbitClosure 0 (detPoly 0) := by
      have h1 := gct_orbit_mem_closure 0 (detPoly 0) 1 (by simp)
      have h2 : substLin 0 (1 : Matrix (Fin 0 × Fin 0) (Fin 0 × Fin 0) ℂ) (detPoly 0) = 1 := by
        rw [hdet]; unfold substLin; exact map_one _
      rwa [h2] at h1
    refine ⟨1, hmem, ?_⟩
    have hqc : q = C (coeff 0 q) := by
      have h0 : q.totalDegree ≤ 0 := by
        by_cases hq0 : q = 0
        · simp [hq0]
        · exact (hq.1.totalDegree hq0).le
      exact (totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 h0))
    have h3 : evalCoeff (C (coeff 0 q) * 1) F = (coeff 0 q) ^ d * evalCoeff 1 F :=
      kl_evalCoeff_C_mul F d hFd _ _
    rw [mul_one, ← hqc] at h3
    intro h0
    rw [h0, mul_zero] at h3
    exact hne h3
  · set s := ∑ i ∈ Finset.range (n * n), lam (i + 1) with hs
    have hsb : s ≤ b := hbody
    have hsn : s ≤ n := by
      rcases Nat.eq_zero_or_pos b with hb0 | hb0
      · omega
      · nlinarith
    have hL0 : lam 0 + s = n * d := by
      have hnn : n * n = (n * n - 1) + 1 := by
        have : 0 < n * n := Nat.mul_pos hn hn
        omega
      have e1 : ∑ i ∈ Finset.range (n * n), lam i
          = ∑ i ∈ Finset.range (n * n - 1), lam (i + 1) + lam 0 := by
        rw [hnn, Finset.sum_range_succ']
        simp
      have e2 : s = ∑ i ∈ Finset.range (n * n - 1), lam (i + 1) + lam (n * n - 1 + 1) := by
        rw [hs, hnn, Finset.sum_range_succ]
        simp
      have e3 : lam (n * n - 1 + 1) = 0 := hlam.2.1 _ (le_of_eq hnn)
      have e4 := hlam.2.2
      omega
    obtain ⟨h, hh, hhv, hne2⟩ := hwv_truncate n d s hsn lam hlam le_rfl F hF q hq hne
    have hscale : ∀ c : ((ℕ × ℕ) →₀ ℕ) → ℂ,
        evalCoeff (X (0, 0) ^ (n - s) * ∑ μ ∈ h.support,
            monomial μ ((2 : ℂ) ^ ((n - s) + μ (0, 0)) * c μ)) F
          = (2 : ℂ) ^ lam 0 *
            evalCoeff (X (0, 0) ^ (n - s) * ∑ μ ∈ h.support, monomial μ (c μ)) F := by
      intro c
      have hdiag := kl_hwv_diag hF (⟨0, hn⟩, ⟨0, hn⟩) 2 two_ne_zero _
        (p1_isForm n s hn hsn h hh hhv c)
      have hidx : idx n (⟨0, hn⟩, ⟨0, hn⟩) = 0 := by simp [idx]
      rw [hidx, p1_scale_form] at hdiag
      exact hdiag
    obtain ⟨h', hsub, hcard, hne3⟩ :=
      p1_few_monomials_w n d s s F hFd (lam 0) hL0 hsn h hh hscale hne2
    have hdeg : ∀ μ ∈ h'.support, Finsupp.degree μ = s := by
      intro μ hμ
      rw [Finsupp.degree_eq_weight_one]
      exact hh (mem_support_iff.1 (hsub hμ))
    have hh' : h'.IsHomogeneous s := by
      intro μ hμ
      have := hdeg μ (mem_support_iff.2 hμ)
      rwa [Finsupp.degree_eq_weight_one] at this
    have hcard' : h'.support.card * s ≤ n := by
      calc h'.support.card * s ≤ (s + 1) * s := Nat.mul_le_mul_right _ hcard
        _ ≤ (b + 1) * b := Nat.mul_le_mul (by omega) hsb
        _ = b * (b + 1) := by ring
        _ ≤ n := hb
    have hsd : IsSymbolicDet h' n := symbolicDet_of_few_monomials n s hn h' hdeg hcard'
    exact ⟨_, padded_mem_orbitClosure_of_symbolicDet n s hsn h' hh'
      (fun μ hμ => hhv μ (hsub hμ)) hsd, hne3⟩

/-! ===== occurs_add (from our accepted 73ad0c8c) ===== -/

open GCTOcc in
theorem gct_occurs_add (n d₁ d₂ : ℕ) (lam mu : ℕ → ℕ)
    (h₁ : Occurs n d₁ lam (orbitClosure n (detPoly n)))
    (h₂ : Occurs n d₂ mu (orbitClosure n (detPoly n))) :
    Occurs n (d₁ + d₂) (fun i => lam i + mu i) (orbitClosure n (detPoly n)) := by
  obtain ⟨F₁, hF₁, p₁, hp₁, hne₁⟩ := h₁
  obtain ⟨F₂, hF₂, p₂, hp₂, hne₂⟩ := h₂
  obtain ⟨g₁, hg₁, hv₁⟩ := gct_orbit_of_closure hp₁ F₁ hne₁
  obtain ⟨g₂, hg₂, hv₂⟩ := gct_orbit_of_closure hp₂ F₂ hne₂
  set f₁ : ℂ → ℂ := fun t => evalCoeff (substLin n (g₁ + t • (g₂ - g₁)) (detPoly n)) F₁ with hf₁
  set f₂ : ℂ → ℂ := fun t => evalCoeff (substLin n (g₁ + t • (g₂ - g₁)) (detPoly n)) F₂ with hf₂
  set f₃ : ℂ → ℂ := fun t => (g₁ + t • (g₂ - g₁)).det with hf₃
  have z₁ : {t | f₁ t = 0}.Finite :=
    gctPF_finite_zeros (gctPF_evalCoeff_line n g₁ (g₂ - g₁) (detPoly n) F₁) (t₀ := 0)
      (by simpa [hf₁] using hv₁)
  have z₂ : {t | f₂ t = 0}.Finite :=
    gctPF_finite_zeros (gctPF_evalCoeff_line n g₁ (g₂ - g₁) (detPoly n) F₂) (t₀ := 1)
      (by simpa [hf₂] using hv₂)
  have z₃ : {t | f₃ t = 0}.Finite :=
    gctPF_finite_zeros (gctPF_det g₁ (g₂ - g₁)) (t₀ := 0)
      (by simpa [hf₃] using hg₁.ne_zero)
  obtain ⟨t, -, ht⟩ := Set.infinite_univ.exists_notMem_finite ((z₁.union z₂).union z₃)
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at ht
  obtain ⟨⟨ht₁, ht₂⟩, ht₃⟩ := ht
  refine ⟨F₁ * F₂, ⟨hF₁.1.mul hF₂.1, ?_⟩, substLin n (g₁ + t • (g₂ - g₁)) (detPoly n),
    gct_orbit_mem_closure n _ _ (isUnit_iff_ne_zero.2 ht₃), ?_⟩
  · intro g hg hdiag q hq
    have e₁ := hF₁.2 g hg hdiag q hq
    have e₂ := hF₂.2 g hg hdiag q hq
    simp only [evalCoeff, eval_mul] at e₁ e₂ ⊢
    rw [e₁, e₂]
    simp only [pow_add, Finset.prod_mul_distrib]
    ring
  · simp only [evalCoeff, eval_mul]
    exact mul_ne_zero ht₁ ht₂

/-! G4b (a586c963): even-body padding, abstract over the occurrence predicate.
`Occ d lam` stands for `Occurs n d lam (orbitClosure n (detPoly n))`; the two hypotheses are
`occurs_add_of_occurs` (73ad0c8c) and `row_extended_rectangle_occurs` (a3397022). -/

namespace G4b

/-- Sum of the body rows `1..R`. -/
def bsum (R : ℕ) (ε : ℕ → ℕ) : ℕ := ∑ i ∈ Finset.range R, ε (i + 1)

/-- The row extended rectangle weight of a3397022. -/
def rect (n k l : ℕ) : ℕ → ℕ := fun i => if i = 0 then l + (n * k - k * l) else if i < k then l else 0

/-- Degree `D` weight with body `ε` (rows `1..R`) and the first row filled up to `n * D`. -/
def Wt (n R D : ℕ) (ε : ℕ → ℕ) : ℕ → ℕ := fun i => if i = 0 then n * D - bsum R ε else ε i

theorem bsum_succ (R : ℕ) (ε : ℕ → ℕ) : bsum (R + 1) ε = bsum R ε + ε (R + 1) := by
  unfold bsum; rw [Finset.sum_range_succ]

theorem antitone_chain (ε : ℕ → ℕ) (h : ∀ i, 1 ≤ i → ε (i + 1) ≤ ε i) :
    ∀ i j, 1 ≤ i → i ≤ j → ε j ≤ ε i := by
  intro i j hi hij
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (h j (le_trans hi hij)).trans ih

theorem le_n_mul (n L D s : ℕ) (hL0 : 0 < L) (hLn : L ≤ n) (hD : s / L + 1 ≤ D) :
    s ≤ n * D := by
  have h1 : s < L * (s / L + 1) := Nat.lt_mul_div_succ s hL0
  have h2 : L * (s / L + 1) ≤ n * D := Nat.mul_le_mul hLn hD
  omega

section
variable (Occ : ℕ → (ℕ → ℕ) → Prop) (n : ℕ)
  (hadd : ∀ (d₁ d₂ : ℕ) (a b : ℕ → ℕ), Occ d₁ a → Occ d₂ b →
    Occ (d₁ + d₂) (fun i => a i + b i))
  (hrect : ∀ k l : ℕ, 1 ≤ k → k * l ≤ n → Even l → Occ k (rect n k l))
include hadd hrect

theorem base : ∀ D, 1 ≤ D → Occ D (fun i => if i = 0 then n * D else 0) := by
  intro D hD
  induction D, hD using Nat.le_induction with
  | base =>
    have h := hrect 1 0 le_rfl (by simp) (⟨0, rfl⟩ : Even 0)
    convert h using 1
    funext i
    by_cases hi : i = 0
    · simp [rect, hi]
    · simp [rect, hi]
  | succ D hD ih =>
    have h := hadd D 1 _ _ ih (hrect 1 0 le_rfl (by simp) (⟨0, rfl⟩ : Even 0))
    convert h using 1
    funext i
    by_cases hi : i = 0
    · simp [rect, hi]; ring
    · simp [rect, hi]

theorem claim (L : ℕ) (hL : Even L) :
    ∀ R, (0 < R → 2 ≤ L ∧ (R + 1) * L ≤ n) →
    ∀ ε : ℕ → ℕ, (∀ i, R + 1 ≤ i → ε i = 0) → (∀ i, 1 ≤ i → ε (i + 1) ≤ ε i) →
      (∀ i, 1 ≤ i → Even (ε i)) →
      ∀ D, (R + 1) * (R + bsum R ε / L) + 1 ≤ D → Occ D (Wt n R D ε) := by
  intro R
  induction R with
  | zero =>
    intro _ ε hz _ _ D hD
    have h := base Occ n hadd hrect D (by simpa [bsum] using hD)
    convert h using 1
    funext i
    by_cases hi : i = 0
    · simp [Wt, hi, bsum]
    · simp [Wt, hi, hz i (by omega)]
  | succ R ih =>
    intro hRL
    obtain ⟨hL2, hLn⟩ := hRL (Nat.succ_pos R)
    have hL0 : 0 < L := by omega
    have hLn1 : L ≤ n := le_trans (Nat.le_mul_of_pos_left L (by omega)) hLn
    have hRL' : 0 < R → 2 ≤ L ∧ (R + 1) * L ≤ n := fun _ =>
      ⟨hL2, le_trans (Nat.mul_le_mul_right _ (by omega)) hLn⟩
    suffices H : ∀ s, ∀ ε : ℕ → ℕ, bsum (R + 1) ε = s → (∀ i, R + 1 + 1 ≤ i → ε i = 0) →
        (∀ i, 1 ≤ i → ε (i + 1) ≤ ε i) → (∀ i, 1 ≤ i → Even (ε i)) →
        ∀ D, (R + 1 + 1) * (R + 1 + bsum (R + 1) ε / L) + 1 ≤ D →
          Occ D (Wt n (R + 1) D ε) by
      intro ε h1 h2 h3 D hD; exact H _ ε rfl h1 h2 h3 D hD
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ihs =>
    intro ε hs hz hanti hev D hD
    by_cases h0 : ε (R + 1) = 0
    · have hz' : ∀ i, R + 1 ≤ i → ε i = 0 := by
        intro i hi
        rcases Nat.eq_or_lt_of_le hi with h | h
        · rw [← h]; exact h0
        · exact hz i h
      have hb : bsum (R + 1) ε = bsum R ε := by rw [bsum_succ, h0, add_zero]
      have hD' : (R + 1) * (R + bsum R ε / L) + 1 ≤ D := by
        rw [hb] at hD
        calc (R + 1) * (R + bsum R ε / L) + 1
            ≤ (R + 1 + 1) * (R + 1 + bsum R ε / L) + 1 := by gcongr <;> omega
          _ ≤ D := hD
      have hW : Wt n (R + 1) D ε = Wt n R D ε := by
        funext i; simp [Wt, hb]
      rw [hW]; exact ih hRL' ε hz' hanti hev D hD'
    · have hevR : Even (ε (R + 1)) := hev _ (by omega)
      have hR2 : 2 ≤ ε (R + 1) := by
        obtain ⟨k, hk⟩ := hevR; omega
      set l := min (ε (R + 1)) L with hl
      have hl2 : 2 ≤ l := le_min hR2 hL2
      have hlL : l ≤ L := min_le_right _ _
      have hlR : l ≤ ε (R + 1) := min_le_left _ _
      have hevl : Even l := by
        rcases le_total (ε (R + 1)) L with h | h
        · rw [hl, min_eq_left h]; exact hevR
        · rw [hl, min_eq_right h]; exact hL
      have hge : ∀ i, 1 ≤ i → i ≤ R + 1 → l ≤ ε i := fun i hi hiR =>
        hlR.trans (antitone_chain ε hanti i (R + 1) hi hiR)
      set ε' : ℕ → ℕ := fun i => if 1 ≤ i ∧ i ≤ R + 1 then ε i - l else ε i with hε'
      have hbs : bsum (R + 1) ε' + (R + 1) * l = bsum (R + 1) ε := by
        unfold bsum
        have : ∀ i ∈ Finset.range (R + 1), ε' (i + 1) + l = ε (i + 1) := by
          intro i hi
          have hi' := Finset.mem_range.1 hi
          simp only [hε']
          rw [if_pos ⟨by omega, by omega⟩]
          have := hge (i + 1) (by omega) (by omega)
          omega
        rw [← Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_range, smul_eq_mul, mul_comm]
      have hz' : ∀ i, R + 1 + 1 ≤ i → ε' i = 0 := by
        intro i hi; simp only [hε']; rw [if_neg (by omega)]; exact hz i hi
      have hanti' : ∀ i, 1 ≤ i → ε' (i + 1) ≤ ε' i := by
        intro i hi
        simp only [hε']
        by_cases h1 : i + 1 ≤ R + 1
        · rw [if_pos ⟨by omega, h1⟩, if_pos ⟨hi, by omega⟩]
          have := hanti i hi; omega
        · rw [if_neg (by omega), hz (i + 1) (by omega)]; exact Nat.zero_le _
      have hev' : ∀ i, 1 ≤ i → Even (ε' i) := by
        intro i hi
        simp only [hε']
        split_ifs with h
        · exact (Nat.even_sub (hge i h.1 h.2)).2 (iff_of_true (hev i hi) hevl)
        · exact hev i hi
      rw [hs] at hD hbs
      obtain ⟨q, hq⟩ : ∃ q, s / L = q := ⟨_, rfl⟩
      rw [hq] at hD
      obtain ⟨s', hs'⟩ : ∃ s', bsum (R + 1) ε' = s' := ⟨_, rfl⟩
      rw [hs'] at hbs
      obtain ⟨q', hq'⟩ : ∃ q', s' / L = q' := ⟨_, rfl⟩
      have hDge : R + 1 + 1 ≤ D := by
        have : R + 1 + 1 ≤ (R + 1 + 1) * (R + 1 + q) :=
          le_mul_of_one_le_right (Nat.zero_le _) (Nat.le_add_right_of_le (Nat.le_add_left 1 R))
        omega
      obtain ⟨D', hD'⟩ : ∃ D', D = D' + (R + 1 + 1) := ⟨D - (R + 1 + 1), by omega⟩
      -- the smaller weight occurs, with D' ≥ s'/L + 1
      have hocc : Occ D' (Wt n (R + 1) D' ε') ∧ q' + 1 ≤ D' := by
        rcases le_or_gt (ε (R + 1)) L with hcase | hcase
        · -- the last row is used up: drop to R rows
          have hlE : l = ε (R + 1) := by rw [hl, min_eq_left hcase]
          have hzR : ∀ i, R + 1 ≤ i → ε' i = 0 := by
            intro i hi
            rcases Nat.eq_or_lt_of_le hi with h | h
            · rw [← h]; simp only [hε']; rw [if_pos ⟨by omega, le_rfl⟩]; omega
            · exact hz' i h
          have hb : bsum (R + 1) ε' = bsum R ε' := by
            rw [bsum_succ, hzR (R + 1) le_rfl, add_zero]
          have hbR : bsum R ε' = s' := by rw [← hb, hs']
          have hss : s' ≤ s := by omega
          have hqq : q' ≤ q := by rw [← hq, ← hq']; exact Nat.div_le_div_right hss
          have e1 : (R + 1 + 1) * (R + 1 + q) = (R + 1 + 1) * (R + q) + (R + 1 + 1) := by ring
          have e2 : (R + 1) * (R + q') ≤ (R + 1 + 1) * (R + q) := by
            apply Nat.mul_le_mul <;> omega
          have e3 : q' ≤ (R + 1) * (R + q') :=
            le_trans (Nat.le_add_left q' R) (le_mul_of_one_le_left (Nat.zero_le _) (by omega))
          have hbud : (R + 1) * (R + bsum R ε' / L) + 1 ≤ D' := by
            rw [hbR, hq']; omega
          have hW : Wt n (R + 1) D' ε' = Wt n R D' ε' := by
            funext i; simp [Wt, hb]
          exact ⟨hW ▸ ih hRL' ε' hzR hanti' hev' D' hbud, by omega⟩
        · -- a full chunk of width L is removed: same R, smaller body
          have hlE : l = L := by rw [hl, min_eq_right hcase.le]
          have hRl : L ≤ (R + 1) * l := by
            rw [hlE]; exact le_mul_of_one_le_left (Nat.zero_le _) (by omega)
          have hlt : s' < s := by omega
          have hqq : q' + 1 ≤ q := by
            have h1 : s' + L ≤ s := by omega
            have h2 : (s' + L) / L = s' / L + 1 := Nat.add_div_right s' hL0
            have h3 : (s' + L) / L ≤ s / L := Nat.div_le_div_right h1
            omega
          have e2 : (R + 1 + 1) * (R + 1 + q') + (R + 1 + 1) ≤ (R + 1 + 1) * (R + 1 + q) := by
            have : (R + 1 + 1) * (R + 1 + (q' + 1)) ≤ (R + 1 + 1) * (R + 1 + q) :=
              Nat.mul_le_mul_left _ (by omega)
            linarith
          have e3 : q' ≤ (R + 1 + 1) * (R + 1 + q') :=
            le_trans (Nat.le_add_left q' (R + 1)) (le_mul_of_one_le_left (Nat.zero_le _) (by omega))
          have hbud : (R + 1 + 1) * (R + 1 + bsum (R + 1) ε' / L) + 1 ≤ D' := by
            rw [hs', hq']; omega
          exact ⟨ihs s' hlt ε' hs' hz' hanti' hev' D' hbud, by omega⟩
      obtain ⟨hocc, hDs⟩ := hocc
      have hsn : s' ≤ n * D' := le_n_mul n L D' s' hL0 hLn1 (by rw [hq']; exact hDs)
      have hkl : (R + 1 + 1) * l ≤ n :=
        le_trans (Nat.mul_le_mul_left _ hlL) hLn
      have hr := hrect (R + 1 + 1) l (by omega) hkl hevl
      have hsum := hadd D' (R + 1 + 1) _ _ hocc hr
      rw [← hD'] at hsum
      convert hsum using 1
      funext i
      by_cases hi : i = 0
      · subst hi
        simp only [Wt, rect, if_true]
        rw [hs, hs']
        have e1 : n * D = n * D' + n * (R + 1 + 1) := by rw [hD']; ring
        have e2 : (R + 1 + 1) * l = (R + 1) * l + l := by ring
        have e3 : (R + 1 + 1) * l ≤ n * (R + 1 + 1) := by
          rw [mul_comm n]; exact Nat.mul_le_mul_left _ (hlL.trans hLn1)
        omega
      · simp only [Wt, rect, if_neg hi]
        by_cases h1 : i ≤ R + 1
        · rw [if_pos (by omega)]
          simp only [hε']
          rw [if_pos ⟨by omega, h1⟩]
          have := hge i (by omega) h1
          omega
        · rw [if_neg (by omega)]
          simp only [hε']
          rw [if_neg (by omega), add_zero]

/-- Even-body padding: if `lam0` occurs in degree `d0`, adding an even antitone body `ε` with at most
`R` rows (and filling the first row) still occurs, once the extra degree `D` covers the rectangles. -/
theorem pad_even (L : ℕ) (hL : Even L) (R : ℕ) (hRL : 0 < R → 2 ≤ L ∧ (R + 1) * L ≤ n)
    (ε : ℕ → ℕ) (hz : ∀ i, R + 1 ≤ i → ε i = 0) (hanti : ∀ i, 1 ≤ i → ε (i + 1) ≤ ε i)
    (hev : ∀ i, 1 ≤ i → Even (ε i)) (D : ℕ) (hD : (R + 1) * (R + bsum R ε / L) + 1 ≤ D)
    (d0 : ℕ) (lam0 : ℕ → ℕ) (h0 : Occ d0 lam0) :
    Occ (d0 + D) (fun i => lam0 i + Wt n R D ε i) :=
  hadd d0 D _ _ h0 (claim Occ n hadd hrect L hL R hRL ε hz hanti hev D hD)

end

end G4b



/-! P3 for a586c963: explicit column-strict filling of the residue shape, and the residue split. -/

namespace P3

theorem sig_eq {t : ℕ} {a : Fin t → ℕ} (s s' : Fin t) (k : Fin (a s)) (k' : Fin (a s'))
    (h1 : (s : ℕ) = s') (h2 : (k : ℕ) = k') : (⟨s, k⟩ : Σ s, Fin (a s)) = ⟨s', k'⟩ := by
  obtain rfl : s = s' := Fin.ext h1
  obtain rfl : k = k' := Fin.ext h2
  rfl

theorem gl_equiv (w t : ℕ) (c : Fin w → ℕ) (a : Fin t → ℕ) (f g : ℕ → ℕ → ℕ × ℕ)
    (hf1 : ∀ (s : Fin t) (k : Fin (a s)), (f s k).1 < w)
    (hf2 : ∀ (s : Fin t) (k : Fin (a s)), (f s k).2 < c ⟨(f s k).1, hf1 s k⟩)
    (hf3 : ∀ (s : Fin t) (k : Fin (a s)), g (f s k).1 (f s k).2 = ((s : ℕ), (k : ℕ)))
    (hg1 : ∀ (j : Fin w) (i : Fin (c j)), (g j i).1 < t)
    (hg2 : ∀ (j : Fin w) (i : Fin (c j)), (g j i).2 < a ⟨(g j i).1, hg1 j i⟩)
    (hg3 : ∀ (j : Fin w) (i : Fin (c j)), f (g j i).1 (g j i).2 = ((j : ℕ), (i : ℕ))) :
    ∃ e : (Σ s : Fin t, Fin (a s)) ≃ (Σ j : Fin w, Fin (c j)),
      ∀ x : Σ j : Fin w, Fin (c j), ((e.symm x).1 : ℕ) = (g x.1 x.2).1 := by
  refine ⟨{ toFun := fun x => ⟨⟨(f x.1 x.2).1, hf1 x.1 x.2⟩, ⟨(f x.1 x.2).2, hf2 x.1 x.2⟩⟩
            invFun := fun y => ⟨⟨(g y.1 y.2).1, hg1 y.1 y.2⟩, ⟨(g y.1 y.2).2, hg2 y.1 y.2⟩⟩
            left_inv := ?_, right_inv := ?_ }, fun x => rfl⟩
  · rintro ⟨s, k⟩
    have h := hf3 s k
    exact sig_eq _ _ _ _ (congrArg Prod.fst h) (congrArg Prod.snd h)
  · rintro ⟨j, i⟩
    have h := hg3 j i
    exact sig_eq (a := c) _ _ _ _ (congrArg Prod.fst h) (congrArg Prod.snd h)

theorem anti_le (nu : ℕ → ℕ) (hanti : ∀ i, 1 ≤ i → nu (i + 1) ≤ nu i) :
    ∀ i k, 1 ≤ i → nu (i + k) ≤ nu i := by
  intro i k hi
  induction k with
  | zero => simp
  | succ k ih => exact le_trans (hanti (i + k) (by omega)) ih

theorem conj (R : ℕ) (nu : ℕ → ℕ) (hanti : ∀ i, 1 ≤ i → nu (i + 1) ≤ nu i)
    (hz : ∀ i, R < i → nu i = 0) (j i : ℕ) (hi : 1 ≤ i) :
    i < 1 + ((Finset.range R).filter (fun i' => j < nu (i' + 1))).card ↔ j < nu i := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hsub : (Finset.range R).filter (fun i' => j < nu (i' + 1)) ⊆ Finset.range (i - 1) := by
      intro i' hi'
      rw [Finset.mem_filter, Finset.mem_range] at hi'
      rw [Finset.mem_range]
      by_contra hlt
      have := anti_le nu hanti i (i' + 1 - i) hi
      rw [show i + (i' + 1 - i) = i' + 1 by omega] at this
      omega
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    omega
  · intro h
    have hiR : i ≤ R := by
      by_contra hc
      rw [hz i (by omega)] at h
      omega
    have hsub : Finset.range i ⊆ (Finset.range R).filter (fun i' => j < nu (i' + 1)) := by
      intro i' hi'
      rw [Finset.mem_range] at hi'
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      have := anti_le nu hanti (i' + 1) (i - (i' + 1)) (by omega)
      rw [show i' + 1 + (i - (i' + 1)) = i by omega] at this
      omega
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    omega

/-! ### The shape and the filling -/

def nu (h T : ℕ) (P : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i = 0 then 0 else P i + (if i ≤ h then 2 * T else 0)

def ww (T : ℕ) (P : ℕ → ℕ) : ℕ := P 1 + 2 * T

def cN (R h T : ℕ) (P : ℕ → ℕ) (j : ℕ) : ℕ :=
  1 + ((Finset.range R).filter (fun i => j < nu h T P (i + 1))).card

def xs (P : ℕ → ℕ) (i : ℕ) : ℕ := P i + 2 * i + 1

def bs (R h T : ℕ) (P : ℕ → ℕ) : ℕ := P h + 2 * T - ((R + 1) * (R + 1) - (h + 1) * (h + 1))

def iX (W h i : ℕ) : ℕ := if i ≤ h then W + 2 * (i - 1) else W + h + i - 1

def gT (R h T : ℕ) (P : ℕ → ℕ) (j i : ℕ) : ℕ × ℕ :=
  if i = 0 then (j, 0)
  else if h < i then (iX (ww T P) h i, j)
  else if j < xs P i then (iX (ww T P) h i, j)
  else if i < h then (ww T P + 2 * i - 1, j - xs P i)
  else if j < bs R h T P then (ww T P + 2 * h - 1, j - xs P h)
  else (iX (ww T P) h (Nat.sqrt (j - bs R h T P + (h + 1) * (h + 1))),
        P (Nat.sqrt (j - bs R h T P + (h + 1) * (h + 1))) +
          (j - bs R h T P + (h + 1) * (h + 1) -
            Nat.sqrt (j - bs R h T P + (h + 1) * (h + 1)) *
              Nat.sqrt (j - bs R h T P + (h + 1) * (h + 1))))

def aN (R h T : ℕ) (P : ℕ → ℕ) (s : ℕ) : ℕ :=
  if s < ww T P then 1
  else if s < ww T P + 2 * h then
    (if (s - ww T P) % 2 = 0 then xs P ((s - ww T P) / 2 + 1)
     else if (s - ww T P) / 2 + 1 < h then 2 * T - 2 * ((s - ww T P) / 2 + 1) - 1
     else bs R h T P - xs P h)
  else xs P (s - ww T P - h + 1)

def fT (R h T : ℕ) (P : ℕ → ℕ) (s k : ℕ) : ℕ × ℕ :=
  if s < ww T P then (s, 0)
  else if s < ww T P + 2 * h then
    (if (s - ww T P) % 2 = 0 then (k, (s - ww T P) / 2 + 1)
     else (xs P ((s - ww T P) / 2 + 1) + k, (s - ww T P) / 2 + 1))
  else if k < P (s - ww T P - h + 1) then (k, s - ww T P - h + 1)
  else (bs R h T P + (s - ww T P - h + 1) * (s - ww T P - h + 1) - (h + 1) * (h + 1) +
          (k - P (s - ww T P - h + 1)), h)

section
variable (R h T : ℕ) (P : ℕ → ℕ)

theorem nu_le (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ h) : nu h T P i = P i + 2 * T := by
  have h0 : i ≠ 0 := by omega
  simp [nu, h0, hih]

theorem nu_gt (i : ℕ) (hi : h < i) : nu h T P i = P i := by
  have h0 : i ≠ 0 := by omega
  have h1 : ¬ i ≤ h := by omega
  simp [nu, h0, h1]

theorem gT_zero (j : ℕ) : gT R h T P j 0 = (j, 0) := by simp [gT]

theorem gT_short (j i : ℕ) (hi : h < i) : gT R h T P j i = (ww T P + h + i - 1, j) := by
  have h0 : i ≠ 0 := by omega
  have h1 : ¬ i ≤ h := by omega
  rw [gT, if_neg h0, if_pos hi, iX, if_neg h1]

theorem gT_X (j i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ h) (hj : j < xs P i) :
    gT R h T P j i = (ww T P + 2 * (i - 1), j) := by
  have h0 : i ≠ 0 := by omega
  have h1 : ¬ h < i := by omega
  rw [gT, if_neg h0, if_neg h1, if_pos hj, iX, if_pos hih]

theorem gT_B (j i : ℕ) (hi1 : 1 ≤ i) (hih : i < h) (hj : xs P i ≤ j) :
    gT R h T P j i = (ww T P + 2 * i - 1, j - xs P i) := by
  have h0 : i ≠ 0 := by omega
  have h1 : ¬ h < i := by omega
  have h2 : ¬ j < xs P i := by omega
  rw [gT, if_neg h0, if_neg h1, if_neg h2, if_pos hih]

theorem gT_Bh (j : ℕ) (hh : 1 ≤ h) (hj : xs P h ≤ j) (hj2 : j < bs R h T P) :
    gT R h T P j h = (ww T P + 2 * h - 1, j - xs P h) := by
  have h0 : h ≠ 0 := by omega
  have h2 : ¬ j < xs P h := by omega
  rw [gT, if_neg h0, if_neg (lt_irrefl h), if_neg h2, if_neg (lt_irrefl h), if_pos hj2]

theorem gT_fill (j x r : ℕ) (hh : 1 ≤ h) (hj : bs R h T P ≤ j) (hb : xs P h ≤ bs R h T P)
    (hx : x = j - bs R h T P + (h + 1) * (h + 1)) (hr : r = Nat.sqrt x) :
    gT R h T P j h = (iX (ww T P) h r, P r + (x - r * r)) := by
  subst hx hr
  have h0 : h ≠ 0 := by omega
  have h2 : ¬ j < xs P h := by omega
  have h3 : ¬ j < bs R h T P := by omega
  rw [gT, if_neg h0, if_neg (lt_irrefl h), if_neg h2, if_neg (lt_irrefl h), if_neg h3]

theorem aN_row0 (s : ℕ) (hs : s < ww T P) : aN R h T P s = 1 := by
  rw [aN, if_pos hs]

theorem aN_X (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ h) :
    aN R h T P (ww T P + 2 * (i - 1)) = xs P i := by
  have h1 : ¬ ww T P + 2 * (i - 1) < ww T P := by omega
  have h2 : ww T P + 2 * (i - 1) < ww T P + 2 * h := by omega
  have h3 : (ww T P + 2 * (i - 1) - ww T P) % 2 = 0 := by omega
  have h4 : (ww T P + 2 * (i - 1) - ww T P) / 2 + 1 = i := by omega
  rw [aN, if_neg h1, if_pos h2, if_pos h3, h4]

theorem aN_B (i : ℕ) (hi1 : 1 ≤ i) (hih : i < h) :
    aN R h T P (ww T P + 2 * i - 1) = 2 * T - 2 * i - 1 := by
  have h1 : ¬ ww T P + 2 * i - 1 < ww T P := by omega
  have h2 : ww T P + 2 * i - 1 < ww T P + 2 * h := by omega
  have h3 : ¬ (ww T P + 2 * i - 1 - ww T P) % 2 = 0 := by omega
  have h4 : (ww T P + 2 * i - 1 - ww T P) / 2 + 1 = i := by omega
  rw [aN, if_neg h1, if_pos h2, if_neg h3, h4, if_pos hih]

theorem aN_Bh (hh : 1 ≤ h) :
    aN R h T P (ww T P + 2 * h - 1) = bs R h T P - xs P h := by
  have h1 : ¬ ww T P + 2 * h - 1 < ww T P := by omega
  have h2 : ww T P + 2 * h - 1 < ww T P + 2 * h := by omega
  have h3 : ¬ (ww T P + 2 * h - 1 - ww T P) % 2 = 0 := by omega
  have h4 : (ww T P + 2 * h - 1 - ww T P) / 2 + 1 = h := by omega
  rw [aN, if_neg h1, if_pos h2, if_neg h3, h4, if_neg (lt_irrefl h)]

theorem aN_short (i : ℕ) (hi : h < i) :
    aN R h T P (ww T P + h + i - 1) = xs P i := by
  have h1 : ¬ ww T P + h + i - 1 < ww T P := by omega
  have h2 : ¬ ww T P + h + i - 1 < ww T P + 2 * h := by omega
  have h4 : ww T P + h + i - 1 - ww T P - h + 1 = i := by omega
  rw [aN, if_neg h1, if_neg h2, h4]

theorem fT_row0 (s k : ℕ) (hs : s < ww T P) : fT R h T P s k = (s, 0) := by
  rw [fT, if_pos hs]

theorem fT_X (i k : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ h) :
    fT R h T P (ww T P + 2 * (i - 1)) k = (k, i) := by
  have h1 : ¬ ww T P + 2 * (i - 1) < ww T P := by omega
  have h2 : ww T P + 2 * (i - 1) < ww T P + 2 * h := by omega
  have h3 : (ww T P + 2 * (i - 1) - ww T P) % 2 = 0 := by omega
  have h4 : (ww T P + 2 * (i - 1) - ww T P) / 2 + 1 = i := by omega
  rw [fT, if_neg h1, if_pos h2, if_pos h3, h4]

theorem fT_B (i k : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ h) :
    fT R h T P (ww T P + 2 * i - 1) k = (xs P i + k, i) := by
  have h1 : ¬ ww T P + 2 * i - 1 < ww T P := by omega
  have h2 : ww T P + 2 * i - 1 < ww T P + 2 * h := by omega
  have h3 : ¬ (ww T P + 2 * i - 1 - ww T P) % 2 = 0 := by omega
  have h4 : (ww T P + 2 * i - 1 - ww T P) / 2 + 1 = i := by omega
  rw [fT, if_neg h1, if_pos h2, if_neg h3, h4]

theorem fT_s1 (i k : ℕ) (hi : h < i) (hk : k < P i) :
    fT R h T P (ww T P + h + i - 1) k = (k, i) := by
  have h1 : ¬ ww T P + h + i - 1 < ww T P := by omega
  have h2 : ¬ ww T P + h + i - 1 < ww T P + 2 * h := by omega
  have h4 : ww T P + h + i - 1 - ww T P - h + 1 = i := by omega
  rw [fT, if_neg h1, if_neg h2, h4, if_pos hk]

theorem fT_s2 (i k : ℕ) (hi : h < i) (hk : P i ≤ k) :
    fT R h T P (ww T P + h + i - 1) k =
      (bs R h T P + i * i - (h + 1) * (h + 1) + (k - P i), h) := by
  have h1 : ¬ ww T P + h + i - 1 < ww T P := by omega
  have h2 : ¬ ww T P + h + i - 1 < ww T P + 2 * h := by omega
  have h4 : ww T P + h + i - 1 - ww T P - h + 1 = i := by omega
  have h5 : ¬ k < P i := by omega
  rw [fT, if_neg h1, if_neg h2, h4, if_neg h5]

theorem iX_gt (W i : ℕ) (hi : h < i) : iX W h i = W + h + i - 1 := by
  have h1 : ¬ i ≤ h := by omega
  rw [iX, if_neg h1]

end

/-! ### Arithmetic facts -/

theorem Pstep (P : ℕ → ℕ) (hP2 : ∀ i, P i ≤ P (i + 1) + 1) : ∀ i k, P i ≤ P (i + k) + k := by
  intro i k
  induction k with
  | zero => simp
  | succ k ih => have := hP2 (i + k); rw [show i + (k + 1) = i + k + 1 by omega]; omega

theorem Ple (R : ℕ) (P : ℕ → ℕ) (hP2 : ∀ i, P i ≤ P (i + 1) + 1) (hPz : ∀ i, R < i → P i = 0) :
    ∀ i, 1 ≤ i → P i ≤ R := by
  intro i hi
  by_cases hiR : i ≤ R + 1
  · have := Pstep P hP2 i (R + 1 - i)
    rw [show i + (R + 1 - i) = R + 1 by omega, hPz (R + 1) (by omega)] at this
    omega
  · rw [hPz i (by omega)]; omega

theorem Pmono (P : ℕ → ℕ) (hP1 : ∀ i, P (i + 1) ≤ P i) : ∀ i k, P (i + k) ≤ P i := by
  intro i k
  induction k with
  | zero => simp
  | succ k ih => have := hP1 (i + k); rw [show i + (k + 1) = i + k + 1 by omega]; omega

theorem Ple1 (P : ℕ → ℕ) (hP1 : ∀ i, P (i + 1) ≤ P i) (i : ℕ) (hi : 1 ≤ i) : P i ≤ P 1 := by
  have := Pmono P hP1 1 (i - 1)
  rwa [show 1 + (i - 1) = i by omega] at this

theorem xs_strict (P : ℕ → ℕ) (hP2 : ∀ i, P i ≤ P (i + 1) + 1) (i i' : ℕ) (h : i < i') :
    xs P i < xs P i' := by
  have := Pstep P hP2 i (i' - i)
  rw [show i + (i' - i) = i' by omega] at this
  unfold xs
  omega

theorem xs_inj (P : ℕ → ℕ) (hP2 : ∀ i, P i ≤ P (i + 1) + 1) (i i' : ℕ) (h : xs P i = xs P i') :
    i = i' := by
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · have := xs_strict P hP2 i i' hlt; omega
  · exact heq
  · have := xs_strict P hP2 i' i hgt; omega

theorem bs_facts (R h T : ℕ) (P : ℕ → ℕ) (hP2 : ∀ i, P i ≤ P (i + 1) + 1)
    (hPz : ∀ i, R < i → P i = 0) (hh1 : 1 ≤ h) (hhR : h ≤ R)
    (hT : (R + 1) * (R + 1) + 5 * R + 3 ≤ 2 * T) :
    xs P h + 3 * R + 2 ≤ bs R h T P ∧ R ≤ bs R h T P ∧
      bs R h T P + ((R + 1) * (R + 1) - (h + 1) * (h + 1)) = P h + 2 * T ∧
      (h + 1) * (h + 1) ≤ (R + 1) * (R + 1) := by
  have HA : (h + 1) * (h + 1) ≤ (R + 1) * (R + 1) := Nat.mul_self_le_mul_self (by omega)
  have hPh := Ple R P hP2 hPz h hh1
  unfold bs xs
  refine ⟨by omega, by omega, by omega, HA⟩

theorem code_cases (W h R s : ℕ) (hs : s < W + h + R) :
    s < W ∨ (∃ i, 1 ≤ i ∧ i ≤ h ∧ s = W + 2 * (i - 1)) ∨ (∃ i, 1 ≤ i ∧ i ≤ h ∧ s = W + 2 * i - 1) ∨
      (∃ i, h < i ∧ i ≤ R ∧ s = W + h + i - 1) := by
  by_cases h1 : s < W
  · exact Or.inl h1
  by_cases h2 : s < W + 2 * h
  · by_cases h3 : (s - W) % 2 = 0
    · exact Or.inr (Or.inl ⟨(s - W) / 2 + 1, by omega, by omega, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨(s - W) / 2 + 1, by omega, by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨s - W - h + 1, by omega, by omega, by omega⟩))

section
variable (R h T : ℕ) (P : ℕ → ℕ) (hP1 : ∀ i, P (i + 1) ≤ P i) (hP2 : ∀ i, P i ≤ P (i + 1) + 1)
  (hPz : ∀ i, R < i → P i = 0) (hh1 : 1 ≤ h) (hhR : h ≤ R)
  (hT : (R + 1) * (R + 1) + 5 * R + 3 ≤ 2 * T)
include hP1 hP2 hPz hh1 hhR hT

theorem HF (s k : ℕ) (hs : s < ww T P + h + R) (hk : k < aN R h T P s) :
    (fT R h T P s k).1 < ww T P ∧
      ((fT R h T P s k).2 = 0 ∨
        (1 ≤ (fT R h T P s k).2 ∧ (fT R h T P s k).1 < nu h T P (fT R h T P s k).2)) ∧
      gT R h T P (fT R h T P s k).1 (fT R h T P s k).2 = (s, k) := by
  obtain ⟨hb1, hb2, hb3, HA⟩ := bs_facts R h T P hP2 hPz hh1 hhR hT
  have hW : ww T P = P 1 + 2 * T := rfl
  have hPm := Ple1 P hP1
  have hPh1 := hPm h hh1
  rcases code_cases (ww T P) h R s hs with hs0 | ⟨i, hi1, hih, rfl⟩ | ⟨i, hi1, hih, rfl⟩ |
      ⟨i, hih, hiR, rfl⟩
  · rw [aN_row0 R h T P s hs0] at hk
    rw [fT_row0 R h T P s k hs0]
    refine ⟨hs0, Or.inl rfl, ?_⟩
    obtain rfl : k = 0 := by omega
    exact gT_zero R h T P s
  · rw [aN_X R h T P i hi1 hih] at hk
    rw [fT_X R h T P i k hi1 hih]
    have hPi := Ple R P hP2 hPz i hi1
    unfold xs at hk
    refine ⟨by omega, Or.inr ⟨hi1, by rw [nu_le h T P i hi1 hih]; omega⟩, ?_⟩
    rw [gT_X R h T P k i hi1 hih (by unfold xs; omega)]
  · rcases lt_or_eq_of_le hih with hlt | rfl
    · rw [aN_B R h T P i hi1 hlt] at hk
      rw [fT_B R h T P i k hi1 hih]
      have hPi := Ple R P hP2 hPz i hi1
      have hPi1 := hPm i hi1
      refine ⟨by unfold xs; omega, Or.inr ⟨hi1, by rw [nu_le h T P i hi1 hih]; unfold xs; omega⟩, ?_⟩
      rw [gT_B R h T P _ i hi1 hlt (by omega)]
      simp
    · rw [aN_Bh R i T P hi1] at hk
      rw [fT_B R i T P i k hi1 le_rfl]
      have hPi := Ple R P hP2 hPz i hi1
      refine ⟨by omega,
        Or.inr ⟨hi1, by rw [nu_le i T P i hi1 le_rfl]; omega⟩, ?_⟩
      rw [gT_Bh R i T P _ hi1 (by omega) (by omega)]
      simp
  · rw [aN_short R h T P i hih] at hk
    have hPi := Ple R P hP2 hPz i (by omega)
    by_cases hkP : k < P i
    · rw [fT_s1 R h T P i k hih hkP]
      refine ⟨by omega, Or.inr ⟨by omega, by rw [nu_gt h T P i hih]; exact hkP⟩, ?_⟩
      rw [gT_short R h T P k i hih]
    · push Not at hkP
      rw [fT_s2 R h T P i k hih hkP]
      have Hi : (h + 1) * (h + 1) ≤ i * i := Nat.mul_self_le_mul_self (by omega)
      have Ai : (i + 1) * (i + 1) ≤ (R + 1) * (R + 1) := Nat.mul_self_le_mul_self (by omega)
      have Ei : (i + 1) * (i + 1) = i * i + 2 * i + 1 := by ring
      unfold xs at hk
      have hPh := Ple R P hP2 hPz h hh1
      refine ⟨by omega, Or.inr ⟨hh1, by rw [nu_le h T P h hh1 le_rfl]; omega⟩, ?_⟩
      rw [gT_fill R h T P _ (i * i + (k - P i)) i hh1 (by omega) (by omega) (by omega)
        (by rw [Nat.sqrt_add_eq i (by unfold xs at hb1; omega)])]
      rw [iX_gt h (ww T P) i hih]
      ext
      · rfl
      · simp only; omega

theorem gT_cell_lb (j i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ h) (hc : j < nu h T P i) :
    ww T P + 2 * (i - 1) ≤ (gT R h T P j i).1 := by
  obtain ⟨hb1, hb2, hb3, HA⟩ := bs_facts R h T P hP2 hPz hh1 hhR hT
  by_cases hjx : j < xs P i
  · rw [gT_X R h T P j i hi1 hih hjx]
  rcases lt_or_eq_of_le hih with hlt | rfl
  · rw [gT_B R h T P j i hi1 hlt (by omega)]; simp only; omega
  by_cases hjb : j < bs R i T P
  · rw [gT_Bh R i T P j hi1 (by omega) hjb]; simp only; omega
  · rw [gT_fill R i T P j _ _ hi1 (by omega) (by omega) rfl rfl]
    have hr : i + 1 ≤ Nat.sqrt (j - bs R i T P + (i + 1) * (i + 1)) := Nat.le_sqrt.2 (by omega)
    rw [iX_gt i (ww T P) _ (by omega)]
    simp only
    omega

theorem gT_cell_ub (j i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ h) (hb : i < h ∨ j < bs R h T P) :
    (gT R h T P j i).1 ≤ ww T P + 2 * i - 1 := by
  obtain ⟨hb1, hb2, hb3, HA⟩ := bs_facts R h T P hP2 hPz hh1 hhR hT
  by_cases hjx : j < xs P i
  · rw [gT_X R h T P j i hi1 hih hjx]; simp only; omega
  rcases lt_or_eq_of_le hih with hlt | rfl
  · rw [gT_B R h T P j i hi1 hlt (by omega)]
  · have hjb : j < bs R i T P := by omega
    rw [gT_Bh R i T P j hi1 (by omega) hjb]

theorem nu_anti (i : ℕ) (hi : 1 ≤ i) : nu h T P (i + 1) ≤ nu h T P i := by
  unfold nu
  have := hP1 i
  split_ifs <;> omega

theorem nu_zero (i : ℕ) (hi : R < i) : nu h T P i = 0 := by
  rw [nu_gt h T P i (by omega), hPz i hi]

theorem gT_succ (j i : ℕ) (hj : j < ww T P) (hc : j < nu h T P (i + 1)) :
    (gT R h T P j i).1 < (gT R h T P j (i + 1)).1 := by
  obtain ⟨hb1, hb2, hb3, HA⟩ := bs_facts R h T P hP2 hPz hh1 hhR hT
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [zero_add] at hc
    rw [gT_zero, zero_add]
    have := gT_cell_lb R h T P hP1 hP2 hPz hh1 hhR hT j 1 le_rfl hh1 hc
    simp only
    omega
  have hci : j < nu h T P i := lt_of_lt_of_le hc (nu_anti R h T P hP1 hP2 hPz hh1 hhR hT i hi)
  rcases lt_trichotomy i h with hlt | rfl | hgt
  · have h1 := gT_cell_ub R h T P hP1 hP2 hPz hh1 hhR hT j i hi hlt.le (Or.inl hlt)
    have h2 := gT_cell_lb R h T P hP1 hP2 hPz hh1 hhR hT j (i + 1) (by omega) hlt hc
    omega
  · rw [nu_gt i T P (i + 1) (by omega)] at hc
    have hP := Ple R P hP2 hPz (i + 1) (by omega)
    have h1 := gT_cell_ub R i T P hP1 hP2 hPz hh1 hhR hT j i hi le_rfl (Or.inr (by omega))
    rw [gT_short R i T P j (i + 1) (by omega)]
    simp only
    omega
  · rw [gT_short R h T P j i hgt, gT_short R h T P j (i + 1) (by omega)]
    simp only
    omega

theorem gT_mono (j i k : ℕ) (hj : j < ww T P) (hc : j < nu h T P (i + k + 1)) :
    (gT R h T P j i).1 < (gT R h T P j (i + k + 1)).1 := by
  induction k with
  | zero => exact gT_succ R h T P hP1 hP2 hPz hh1 hhR hT j i hj hc
  | succ k ih =>
    have hc' : j < nu h T P (i + k + 1) :=
      lt_of_lt_of_le hc (nu_anti R h T P hP1 hP2 hPz hh1 hhR hT (i + k + 1) (by omega))
    have h2 := gT_succ R h T P hP1 hP2 hPz hh1 hhR hT j (i + k + 1) hj
      (by rw [show i + (k + 1) + 1 = i + k + 1 + 1 by omega] at hc; exact hc)
    rw [show i + (k + 1) + 1 = i + k + 1 + 1 by omega]
    exact lt_trans (ih hc') h2

theorem HG (j i : ℕ) (hj : j < ww T P) (hc : i = 0 ∨ (1 ≤ i ∧ j < nu h T P i)) :
    (gT R h T P j i).1 < ww T P + h + R ∧
      (gT R h T P j i).2 < aN R h T P (gT R h T P j i).1 ∧
      fT R h T P (gT R h T P j i).1 (gT R h T P j i).2 = (j, i) ∧
      (1 ≤ i → ww T P ≤ (gT R h T P j i).1) := by
  obtain ⟨hb1, hb2, hb3, HA⟩ := bs_facts R h T P hP2 hPz hh1 hhR hT
  rcases hc with rfl | ⟨hi1, hjn⟩
  · rw [gT_zero]
    refine ⟨by omega, by rw [aN_row0 R h T P j hj]; omega, by rw [fT_row0 R h T P j 0 hj], ?_⟩
    intro h; omega
  have hiR : i ≤ R := by
    by_contra hc
    rw [nu_zero R h T P hP1 hP2 hPz hh1 hhR hT i (by omega)] at hjn
    omega
  rcases lt_or_ge h i with hhi | hih
  · rw [nu_gt h T P i hhi] at hjn
    rw [gT_short R h T P j i hhi]
    refine ⟨by omega, by rw [aN_short R h T P i hhi]; unfold xs; omega,
      by rw [fT_s1 R h T P i j hhi hjn], fun _ => by omega⟩
  rw [nu_le h T P i hi1 hih] at hjn
  by_cases hjx : j < xs P i
  · rw [gT_X R h T P j i hi1 hih hjx]
    exact ⟨by omega, by rw [aN_X R h T P i hi1 hih]; exact hjx,
      by rw [fT_X R h T P i j hi1 hih], fun _ => by omega⟩
  rcases lt_or_eq_of_le hih with hlt | rfl
  · rw [gT_B R h T P j i hi1 hlt (by omega)]
    refine ⟨by omega, by rw [aN_B R h T P i hi1 hlt]; unfold xs at hjx ⊢; omega, ?_, fun _ => by omega⟩
    rw [fT_B R h T P i _ hi1 hih]
    ext
    · simp only; omega
    · rfl
  by_cases hjb : j < bs R i T P
  · rw [gT_Bh R i T P j hi1 (by omega) hjb]
    refine ⟨by omega, by rw [aN_Bh R i T P hi1]; omega, ?_, fun _ => by omega⟩
    rw [fT_B R i T P i _ hi1 le_rfl]
    ext
    · simp only; omega
    · rfl
  · push Not at hjb
    set x := j - bs R i T P + (i + 1) * (i + 1) with hx
    set r := Nat.sqrt x with hr
    rw [gT_fill R i T P j x r hi1 hjb (by omega) hx hr]
    have hr1 : r * r ≤ x := Nat.le_sqrt.1 le_rfl
    have hr2 : x < (r + 1) * (r + 1) := Nat.sqrt_lt.1 (Nat.lt_succ_self r)
    have hr3 : i + 1 ≤ r := Nat.le_sqrt.2 (by omega)
    have hr4 : r < R + 1 := Nat.sqrt_lt.2 (by omega)
    have Hr : (i + 1) * (i + 1) ≤ r * r := Nat.mul_self_le_mul_self hr3
    have Er : (r + 1) * (r + 1) = r * r + 2 * r + 1 := by ring
    rw [iX_gt i (ww T P) r (by omega)]
    refine ⟨by omega, by rw [aN_short R i T P r (by omega)]; unfold xs; omega, ?_, fun _ => by omega⟩
    rw [fT_s2 R i T P r _ (by omega) (by omega)]
    ext
    · simp only; omega
    · rfl

theorem aN_body (s : ℕ) (hw : ww T P ≤ s) (hs : s < ww T P + h + R) :
    (∃ i, 1 ≤ i ∧ i ≤ R ∧ s = iX (ww T P) h i ∧ aN R h T P s = xs P i) ∨
      (∃ i, 1 ≤ i ∧ i ≤ h ∧ s = ww T P + 2 * i - 1 ∧
        aN R h T P s = (if i < h then 2 * T - 2 * i - 1 else bs R h T P - xs P h)) := by
  rcases code_cases (ww T P) h R s hs with hs0 | ⟨i, hi1, hih, rfl⟩ | ⟨i, hi1, hih, rfl⟩ |
      ⟨i, hih, hiR, rfl⟩
  · omega
  · exact Or.inl ⟨i, hi1, by omega, by rw [iX, if_pos hih], aN_X R h T P i hi1 hih⟩
  · refine Or.inr ⟨i, hi1, hih, rfl, ?_⟩
    rcases lt_or_eq_of_le hih with hlt | rfl
    · rw [if_pos hlt, aN_B R h T P i hi1 hlt]
    · rw [if_neg (lt_irrefl i), aN_Bh R i T P hi1]
  · exact Or.inl ⟨i, by omega, hiR, (iX_gt h _ i hih).symm, aN_short R h T P i hih⟩

theorem aN_facts (s : ℕ) (hs : s < ww T P + h + R) :
    1 ≤ aN R h T P s ∧ aN R h T P s ≤ 2 * T ∧ (ww T P ≤ s → 2 ≤ aN R h T P s) := by
  obtain ⟨hb1, hb2, hb3, HA⟩ := bs_facts R h T P hP2 hPz hh1 hhR hT
  by_cases hw : ww T P ≤ s
  · rcases aN_body R h T P hP1 hP2 hPz hh1 hhR hT s hw hs with ⟨i, hi1, hiR, -, he⟩ |
      ⟨i, hi1, hih, -, he⟩
    · rw [he]
      have := Ple R P hP2 hPz i hi1
      unfold xs
      refine ⟨by omega, by omega, fun _ => by omega⟩
    · rw [he]
      have hPh := Ple R P hP2 hPz h hh1
      unfold xs at hb1 ⊢
      split_ifs <;> refine ⟨by omega, by omega, fun _ => by omega⟩
  · rw [aN_row0 R h T P s (by omega)]
    refine ⟨le_rfl, by omega, fun h => absurd h hw⟩

theorem aN_inj (s s' : ℕ) (hs : s < ww T P + h + R) (hs' : s' < ww T P + h + R)
    (hw : ww T P ≤ s) (hw' : ww T P ≤ s') (he : aN R h T P s = aN R h T P s') : s = s' := by
  obtain ⟨hb1, hb2, hb3, HA⟩ := bs_facts R h T P hP2 hPz hh1 hhR hT
  have hPh := Ple R P hP2 hPz h hh1
  have hxsh : xs P h = P h + 2 * h + 1 := rfl
  have hxs : ∀ i, 1 ≤ i → i ≤ R → xs P i ≤ 3 * R + 1 := fun i hi1 hiR => by
    have := Ple R P hP2 hPz i hi1; unfold xs; omega
  rcases aN_body R h T P hP1 hP2 hPz hh1 hhR hT s hw hs with ⟨i, hi1, hiR, rfl, he1⟩ |
      ⟨i, hi1, hih, rfl, he1⟩ <;>
    rcases aN_body R h T P hP1 hP2 hPz hh1 hhR hT s' hw' hs' with ⟨i', hi1', hiR', rfl, he2⟩ |
      ⟨i', hi1', hih', rfl, he2⟩ <;> rw [he1, he2] at he
  · rw [xs_inj P hP2 i i' he]
  · have := hxs i hi1 hiR
    split_ifs at he <;> omega
  · have := hxs i' hi1' hiR'
    split_ifs at he <;> omega
  · by_cases c1 : i < h <;> by_cases c2 : i' < h <;>
      simp only [c1, c2, if_true, if_false] at he <;> omega

end

/-! ### The tableau package -/

theorem tableau (R h T : ℕ) (P : ℕ → ℕ) (hP1 : ∀ i, P (i + 1) ≤ P i)
    (hP2 : ∀ i, P i ≤ P (i + 1) + 1) (hPz : ∀ i, R < i → P i = 0) (hh1 : 1 ≤ h) (hhR : h ≤ R)
    (hT : (R + 1) * (R + 1) + 5 * R + 3 ≤ 2 * T) :
    ∃ (c : Fin (ww T P) → ℕ) (a : Fin (ww T P + h + R) → ℕ)
      (e : (Σ s : Fin (ww T P + h + R), Fin (a s)) ≃ (Σ j : Fin (ww T P), Fin (c j))),
      (∀ j, c j ≤ R + 1) ∧
      (∀ j (i i' : Fin (c j)), i < i' → (e.symm ⟨j, i⟩).1 < (e.symm ⟨j, i'⟩).1) ∧
      (∀ j (i : Fin (c j)), (i : ℕ) = 0 → a (e.symm ⟨j, i⟩).1 = 1) ∧
      (∀ j (i : Fin (c j)), (i : ℕ) ≠ 0 → 2 ≤ a (e.symm ⟨j, i⟩).1) ∧
      (∀ s s', 2 ≤ a s → 2 ≤ a s' → a s = a s' → s = s') ∧
      (∀ s, 1 ≤ a s) ∧ (∀ s, a s ≤ 2 * T) ∧
      (∀ i, 1 ≤ i → (Finset.univ.filter (fun j => i < c j)).card = nu h T P i) ∧
      (Finset.univ.filter (fun j => 0 < c j)).card = ww T P ∧
      ∑ s, a s = ww T P + ∑ i ∈ Finset.range R, nu h T P (i + 1) := by
  classical
  have hanti := nu_anti R h T P hP1 hP2 hPz hh1 hhR hT
  have hz := nu_zero R h T P hP1 hP2 hPz hh1 hhR hT
  have hcell : ∀ j i : ℕ, i < cN R h T P j ↔ (i = 0 ∨ (1 ≤ i ∧ j < nu h T P i)) := by
    intro j i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [cN]
    · rw [cN, conj R (nu h T P) hanti hz j i hi]
      constructor
      · intro h; exact Or.inr ⟨hi, h⟩
      · rintro (h | h); · omega
        exact h.2
  have HFp := HF R h T P hP1 hP2 hPz hh1 hhR hT
  have HGp := HG R h T P hP1 hP2 hPz hh1 hhR hT
  obtain ⟨e, he⟩ := gl_equiv (ww T P) (ww T P + h + R) (fun j => cN R h T P j)
    (fun s => aN R h T P s) (fT R h T P) (gT R h T P)
    (fun s k => (HFp s k s.2 k.2).1)
    (fun s k => (hcell _ _).2 (HFp s k s.2 k.2).2.1)
    (fun s k => (HFp s k s.2 k.2).2.2)
    (fun j i => (HGp j i j.2 ((hcell j i).1 i.2)).1)
    (fun j i => (HGp j i j.2 ((hcell j i).1 i.2)).2.1)
    (fun j i => (HGp j i j.2 ((hcell j i).1 i.2)).2.2.1)
  have hnuW : ∀ i, 1 ≤ i → nu h T P i ≤ ww T P := by
    intro i hi
    have := anti_le (nu h T P) hanti 1 (i - 1) le_rfl
    rw [show 1 + (i - 1) = i by omega] at this
    have h1 : nu h T P 1 = ww T P := by rw [nu_le h T P 1 le_rfl hh1]; rfl
    omega
  refine ⟨fun j => cN R h T P j, fun s => aN R h T P s, e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    show 1 + _ ≤ R + 1
    have := Finset.card_filter_le (Finset.range R) (fun i => (j : ℕ) < nu h T P (i + 1))
    rw [Finset.card_range] at this
    omega
  · intro j i i' hii'
    rw [Fin.lt_def, he, he]
    have hi' : (i' : ℕ) ≠ 0 := by
      have : (i : ℕ) < i' := hii'
      omega
    have hc := (hcell j i').1 i'.2
    rcases hc with hc | hc
    · exact absurd hc hi'
    have hlt : (i : ℕ) < i' := hii'
    have := gT_mono R h T P hP1 hP2 hPz hh1 hhR hT j i (i' - i - 1) j.2
      (by rw [show (i : ℕ) + (i' - i - 1) + 1 = i' by omega]; exact hc.2)
    rw [show (i : ℕ) + (i' - i - 1) + 1 = i' by omega] at this
    exact this
  · intro j i hi0
    show aN R h T P ((e.symm ⟨j, i⟩).1 : ℕ) = 1
    rw [he]
    show aN R h T P (gT R h T P j i).1 = 1
    rw [hi0, gT_zero]
    exact aN_row0 R h T P j j.2
  · intro j i hi0
    show 2 ≤ aN R h T P ((e.symm ⟨j, i⟩).1 : ℕ)
    rw [he]
    show 2 ≤ aN R h T P (gT R h T P j i).1
    have hc := (hcell j i).1 i.2
    have H := HGp j i j.2 hc
    exact (aN_facts R h T P hP1 hP2 hPz hh1 hhR hT _ H.1).2.2 (H.2.2.2 (by omega))
  · intro s s' h1 h2 h3
    apply Fin.ext
    have hw : ww T P ≤ (s : ℕ) := by
      by_contra hc
      have : aN R h T P s = 1 := aN_row0 R h T P s (by omega)
      have : (2 : ℕ) ≤ aN R h T P s := h1
      omega
    have hw' : ww T P ≤ (s' : ℕ) := by
      by_contra hc
      have : aN R h T P s' = 1 := aN_row0 R h T P s' (by omega)
      have : (2 : ℕ) ≤ aN R h T P s' := h2
      omega
    exact aN_inj R h T P hP1 hP2 hPz hh1 hhR hT s s' s.2 s'.2 hw hw' h3
  · intro s
    exact (aN_facts R h T P hP1 hP2 hPz hh1 hhR hT s s.2).1
  · intro s
    exact (aN_facts R h T P hP1 hP2 hPz hh1 hhR hT s s.2).2.1
  · intro i hi
    have : (Finset.univ.filter (fun j : Fin (ww T P) => i < cN R h T P j)) =
        Finset.univ.filter (fun j : Fin (ww T P) => (j : ℕ) < nu h T P i) := by
      apply Finset.filter_congr
      intro j _
      rw [hcell]
      constructor
      · rintro (h | h); · omega
        exact h.2
      · intro h; exact Or.inr ⟨hi, h⟩
    rw [this, Fin.card_filter_val_lt]
    have := hnuW i hi
    omega
  · have : (Finset.univ.filter (fun j : Fin (ww T P) => 0 < cN R h T P j)) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro j _
      show 0 < 1 + _
      omega
    rw [this, Finset.card_univ, Fintype.card_fin]
  · have h1 : ∑ s : Fin (ww T P + h + R), aN R h T P s = ∑ j : Fin (ww T P), cN R h T P j := by
      have := Fintype.card_congr e
      rw [Fintype.card_sigma, Fintype.card_sigma] at this
      simpa using this
    show ∑ s : Fin (ww T P + h + R), aN R h T P s = _
    rw [h1]
    simp only [cN, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one]
    congr 1
    have hswap : ∑ j : Fin (ww T P), ((Finset.range R).filter
        (fun i => (j : ℕ) < nu h T P (i + 1))).card = ∑ i ∈ Finset.range R,
        (Finset.univ.filter (fun j : Fin (ww T P) => (j : ℕ) < nu h T P (i + 1))).card := by
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    rw [hswap]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Fin.card_filter_val_lt]
    have := hnuW (i + 1) (by omega)
    omega

end P3



namespace P3R

theorem residue (R T b : ℕ) (lam : ℕ → ℕ) (hanti : ∀ i, lam (i + 1) ≤ lam i)
    (hz : ∀ i, R + 1 ≤ i → lam i = 0) (hb : ∑ i ∈ Finset.range R, lam (i + 1) = b)
    (hbig : 2 * T * R * R < b) :
    ∃ (h : ℕ) (P eps : ℕ → ℕ), 1 ≤ h ∧ h ≤ R ∧ (∀ i, P (i + 1) ≤ P i) ∧
      (∀ i, P i ≤ P (i + 1) + 1) ∧ (∀ i, R < i → P i = 0) ∧
      (∀ i, R + 1 ≤ i → eps i = 0) ∧ (∀ i, 1 ≤ i → eps (i + 1) ≤ eps i) ∧
      (∀ i, 1 ≤ i → Even (eps i)) ∧
      (∀ i, 1 ≤ i → P i + (if i ≤ h then 2 * T else 0) + eps i = lam i) := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ, g = fun h => lam h - lam (h + 1) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℕ → ℕ, P = fun i => ∑ h ∈ Finset.Ico i (R + 1), g h % 2 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℕ, E = fun i => ∑ h ∈ Finset.Ico i (R + 1), 2 * (g h / 2) :=
    ⟨_, rfl⟩
  have hgi : ∀ i, g i = lam i - lam (i + 1) := fun i => by rw [hg]
  have hsplit : ∀ (f : ℕ → ℕ) i, i ≤ R →
      ∑ h ∈ Finset.Ico i (R + 1), f h = f i + ∑ h ∈ Finset.Ico (i + 1) (R + 1), f h :=
    fun f i hi => Finset.sum_eq_sum_Ico_succ_bot (by omega) f
  have hempty : ∀ (f : ℕ → ℕ) i, R < i → ∑ h ∈ Finset.Ico i (R + 1), f h = 0 := by
    intro f i hi
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
  have Psucc : ∀ i, i ≤ R → P i = g i % 2 + P (i + 1) := by
    intro i hi; rw [hP]; exact hsplit _ i hi
  have Esucc : ∀ i, i ≤ R → E i = 2 * (g i / 2) + E (i + 1) := by
    intro i hi; rw [hE]; exact hsplit _ i hi
  have Pzero : ∀ i, R < i → P i = 0 := by
    intro i hi; rw [hP]; exact hempty _ i hi
  have Ezero : ∀ i, R < i → E i = 0 := by
    intro i hi; rw [hE]; exact hempty _ i hi
  have htel : ∀ i, lam i = P i + E i := by
    have H : ∀ k i, i + k = R + 1 → lam i = P i + E i := by
      intro k
      induction k with
      | zero =>
        intro i hi
        rw [hz i (by omega), Pzero i (by omega), Ezero i (by omega)]
      | succ k ih =>
        intro i hi
        have h0 := ih (i + 1) (by omega)
        rw [Psucc i (by omega), Esucc i (by omega)]
        have h1 := hanti i
        have h2 := hgi i
        have h3 := Nat.mod_add_div (g i) 2
        omega
    intro i
    by_cases hi : i ≤ R + 1
    · exact H (R + 1 - i) i (by omega)
    · rw [hz i (by omega), Pzero i (by omega), Ezero i (by omega)]
  have hP1 : ∀ i, P (i + 1) ≤ P i := by
    intro i
    by_cases hi : i ≤ R
    · rw [Psucc i hi]; omega
    · rw [Pzero i (by omega), Pzero (i + 1) (by omega)]
  have hP2 : ∀ i, P i ≤ P (i + 1) + 1 := by
    intro i
    by_cases hi : i ≤ R
    · rw [Psucc i hi]; have := Nat.mod_lt (g i) (by norm_num : 2 > 0); omega
    · rw [Pzero i (by omega)]; omega
  -- a large gap
  have hgap : ∃ h, 1 ≤ h ∧ h ≤ R ∧ 2 * T + 1 ≤ g h := by
    by_contra hc
    push Not at hc
    have hG : ∀ i, lam i = ∑ h ∈ Finset.Ico i (R + 1), g h := by
      intro i
      rw [htel i, hP, hE]
      simp only
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun h _ => ?_)
      have := Nat.mod_add_div (g h) 2
      omega
    have hl1 : lam 1 ≤ R * (2 * T) := by
      rw [hG 1]
      have := Finset.sum_le_card_nsmul (Finset.Ico 1 (R + 1)) g (2 * T) (by
        intro h hh
        rw [Finset.mem_Ico] at hh
        have := hc h hh.1 (by omega)
        omega)
      rw [Nat.card_Ico, smul_eq_mul] at this
      simpa using this
    have hlam : Antitone lam := antitone_nat_of_succ_le hanti
    have hbR : b ≤ R * lam 1 := by
      rw [← hb]
      have := Finset.sum_le_card_nsmul (Finset.range R) (fun i => lam (i + 1)) (lam 1) (by
        intro i _
        exact hlam (by omega))
      rw [Finset.card_range, smul_eq_mul] at this
      exact this
    have : R * lam 1 ≤ R * (R * (2 * T)) := Nat.mul_le_mul_left R hl1
    have e : R * (R * (2 * T)) = 2 * T * R * R := by ring
    omega
  obtain ⟨h, hh1, hhR, hgh⟩ := hgap
  have Ege : ∀ i, i ≤ h → 2 * T ≤ E i := by
    intro i hi
    rw [hE]
    show 2 * T ≤ ∑ x ∈ Finset.Ico i (R + 1), 2 * (g x / 2)
    have hmem : h ∈ Finset.Ico i (R + 1) := by rw [Finset.mem_Ico]; omega
    have : 2 * (g h / 2) ≤ ∑ x ∈ Finset.Ico i (R + 1), 2 * (g x / 2) :=
      Finset.single_le_sum (f := fun h => 2 * (g h / 2)) (fun _ _ => Nat.zero_le _) hmem
    omega
  have Eev : ∀ i, Even (E i) := by
    intro i
    rw [hE]
    exact Finset.even_sum _ (fun h _ => even_two_mul _)
  refine ⟨h, P, fun i => E i - (if 1 ≤ i ∧ i ≤ h then 2 * T else 0), hh1, hhR, hP1, hP2, Pzero,
    ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only
    rw [Ezero i (by omega), if_neg (by omega)]
  · intro i hi
    simp only
    by_cases hiR : i ≤ R
    · have e1 := Esucc i hiR
      have e2 := Ege (i + 1)
      have e3 := Ege i
      have e4 : 2 * T ≤ 2 * (g h / 2) := by omega
      by_cases hih : i < h
      · rw [if_pos (by omega), if_pos (by omega)]
        omega
      · by_cases hih' : i = h
        · subst hih'
          rw [if_neg (by omega), if_pos (by omega)]
          omega
        · rw [if_neg (by omega), if_neg (by omega)]
          omega
    · rw [Ezero i (by omega), Ezero (i + 1) (by omega)]
      simp
  · intro i hi
    simp only
    split_ifs with hc
    · rw [Nat.even_sub (Ege i hc.2)]
      exact ⟨fun _ => even_two_mul T, fun _ => Eev i⟩
    · simpa using Eev i
  · intro i hi
    simp only
    rw [htel i]
    by_cases hih : i ≤ h
    · rw [if_pos hih, if_pos ⟨hi, hih⟩]
      have := Ege i hih
      omega
    · rw [if_neg hih, if_neg (by omega)]
      omega

end P3R

namespace P4

theorem ar1 (M : ℕ) (h : 4 ≤ M) : 3 * M ≤ M * M ∧ 16 ≤ M * M ∧
    (M + 2) * (M + 2) ≤ 4 * (M * M) ∧ M * M + 5 * M ≤ 2 * ((M + 2) * (M + 2)) := by
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

theorem ar2 (A : ℕ) (h : 16 ≤ A) : 2 * (4 * A) * A < A * A * A ∧
    (9 * A) * (2 * (4 * A)) ≤ (A * A * A) * (A * A * A) := by
  have h1 : 256 ≤ A * A := by nlinarith
  have h2 : 72 ≤ A * A * (A * A) := le_trans (by omega) (Nat.le_mul_of_pos_left (A * A) (by omega))
  constructor
  · nlinarith
  · have e1 : (9 * A) * (2 * (4 * A)) = 72 * (A * A) := by ring
    have e2 : (A * A * A) * (A * A * A) = (A * A * (A * A)) * (A * A) := by ring
    rw [e1, e2]
    exact Nat.mul_le_mul_right _ h2

theorem ar3 (A M : ℕ) (hA : 16 ≤ A) (hM : 4 ≤ M) : 64 * A ≤ A * A * M := by
  have : 64 ≤ A * M := by nlinarith
  calc 64 * A = A * 64 := by ring
    _ ≤ A * (A * M) := Nat.mul_le_mul_left _ this
    _ = A * A * M := by ring

theorem ar4 (m : ℕ) (h : 2 ≤ m) : 4 ≤ m * m ∧ m ≤ m * m ∧ 2 * m ≤ m * m := by
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem big_assembly (Occ : ℕ → (ℕ → ℕ) → Prop) (n d m : ℕ)
    (hadd : ∀ (d₁ d₂ : ℕ) (a b : ℕ → ℕ), Occ d₁ a → Occ d₂ b →
      Occ (d₁ + d₂) (fun i => a i + b i))
    (hrect : ∀ k l : ℕ, 1 ≤ k → k * l ≤ n → Even l → Occ k (G4b.rect n k l))
    (htab : ∀ (R h T : ℕ) (P : ℕ → ℕ), (∀ i, P (i + 1) ≤ P i) → (∀ i, P i ≤ P (i + 1) + 1) →
      (∀ i, R < i → P i = 0) → 1 ≤ h → h ≤ R → (R + 1) * (R + 1) + 5 * R + 3 ≤ 2 * T →
      R + 1 ≤ n → (1 + (P3.ww T P + h + R)) * (2 * T) ≤ n →
      Occ (P3.ww T P + h + R) (fun i => if i = 0 then
          n * (P3.ww T P + h + R) - ∑ i ∈ Finset.range R, P3.nu h T P (i + 1)
        else P3.nu h T P i) ∧
      ∑ i ∈ Finset.range R, P3.nu h T P (i + 1) ≤ n * (P3.ww T P + h + R))
    (hm : 0 < m) (hnm : m ^ 25 ≤ n) (lam : ℕ → ℕ)
    (hanti : ∀ i, lam (i + 1) ≤ lam i) (hlen : ∀ i, n * n ≤ i → lam i = 0)
    (hsum : ∑ i ∈ Finset.range (n * n), lam i = n * d)
    (hz : ∀ i, m * m ≤ i → lam i = 0)
    (hbody : (∑ i ∈ Finset.range (n * n), lam (i + 1)) ≤ m * d)
    (hsmall : ¬ (∑ i ∈ Finset.range (n * n), lam (i + 1)) *
      ((∑ i ∈ Finset.range (n * n), lam (i + 1)) + 1) ≤ n) :
    Occ d lam := by
  obtain ⟨b, hb⟩ : ∃ b, b = ∑ i ∈ Finset.range (n * n), lam (i + 1) := ⟨_, rfl⟩
  rw [← hb] at hbody hsmall
  have hmn : m ≤ n := le_trans (Nat.le_self_pow (by norm_num) m) hnm
  have hn1 : 1 ≤ n := le_trans hm hmn
  have hm2 : 2 ≤ m := by
    by_contra hc
    have hm1 : m = 1 := by omega
    have : b = 0 := by
      rw [hb]
      apply Finset.sum_eq_zero
      intro i _
      exact hz (i + 1) (by rw [hm1]; omega)
    rw [this] at hsmall
    simp at hsmall
  obtain ⟨M, hM⟩ : ∃ M, M = m * m := ⟨_, rfl⟩
  obtain ⟨hm4, hmm, h2mm⟩ := ar4 m hm2
  have hM4 : 4 ≤ M := by rw [hM]; exact hm4
  have hmM : m ≤ M := by rw [hM]; exact hmm
  have hpow : ∀ k, m ^ (2 * k) = M ^ k := by
    intro k; rw [pow_mul, sq, ← hM]
  -- size facts
  have hb12 : m ^ 12 ≤ b := by
    by_contra hc
    push Not at hc
    have h1 : b * (b + 1) ≤ m ^ 12 * m ^ 12 := Nat.mul_le_mul hc.le hc
    have h2 : m ^ 12 * m ^ 12 ≤ m ^ 25 := by
      rw [← pow_add]; exact Nat.pow_le_pow_right hm (by norm_num)
    omega
  have hd10 : m ^ 10 ≤ d := by
    have e1 : m ^ 12 = m * m ^ 11 := by ring
    have h1 : m * m ^ 11 ≤ m * d := by rw [← e1]; omega
    have h2 := Nat.le_of_mul_le_mul_left h1 hm
    exact le_trans (Nat.pow_le_pow_right hm (by norm_num)) h2
  have hnM : M ^ 12 ≤ n := by
    rw [← hpow 12]
    exact le_trans (Nat.pow_le_pow_right hm (by norm_num)) hnm
  have hbM : M ^ 6 ≤ b := by rw [← hpow 6]; exact hb12
  have hdM : M ^ 5 ≤ d := by rw [← hpow 5]; exact hd10
  obtain ⟨A, hA⟩ : ∃ A, A = M * M := ⟨_, rfl⟩
  obtain ⟨hA3, hA16, hT4', hTT'⟩ := ar1 M hM4
  rw [← hA] at hA3 hA16 hT4'
  have hM2A : M ^ 2 = A := by rw [hA, sq]
  have hM4A : M ^ 4 = A * A := by rw [hA]; ring
  have hM5 : M ^ 5 = A * A * M := by rw [hA]; ring
  have hM6 : M ^ 6 = A * A * A := by rw [hA]; ring
  have hM12 : M ^ 12 = (A * A * A) * (A * A * A) := by rw [hA]; ring
  obtain ⟨R, hR⟩ : ∃ R, R + 1 = M := ⟨M - 1, by omega⟩
  obtain ⟨T, hT⟩ : ∃ T, T = (M + 2) * (M + 2) := ⟨_, rfl⟩
  have hT4 : T ≤ 4 * A := by rw [hT]; exact hT4'
  have hRR : R * R ≤ A := by rw [hA]; exact Nat.mul_self_le_mul_self (by omega)
  have hTT : (R + 1) * (R + 1) + 5 * R + 3 ≤ 2 * T := by
    rw [hT, hR]; rw [← hA] at hTT' ⊢; omega
  -- b over the first R rows
  have hz' : ∀ i, R + 1 ≤ i → lam i = 0 := fun i hi => hz i (by rw [← hM]; omega)
  have hbR : ∑ i ∈ Finset.range R, lam (i + 1) = b := by
    have hRle : R ≤ n * n := by
      have : m * m ≤ n * n := Nat.mul_le_mul hmn hmn
      omega
    rw [hb, ← Finset.sum_range_add_sum_Ico _ hRle]
    have : ∑ i ∈ Finset.Ico R (n * n), lam (i + 1) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_Ico] at hi
      exact hz' (i + 1) (by omega)
    omega
  have hbig : 2 * T * R * R < b := by
    have h1 : 2 * T * R * R ≤ 2 * (4 * A) * A := by
      rw [show 2 * T * R * R = 2 * T * (R * R) by ring]
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hT4) hRR
    have h2 : 2 * (4 * A) * A < A * A * A := (ar2 A hA16).1
    omega
  obtain ⟨h, P, eps, hh1, hhR, hP1, hP2, hPz, hez, hea, hev, hsplit⟩ :=
    P3R.residue R T b lam hanti hz' hbR hbig
  have hP1R : P 1 ≤ R := P3.Ple R P hP2 hPz 1 le_rfl
  obtain ⟨t, ht⟩ : ∃ t, t = P3.ww T P + h + R := ⟨_, rfl⟩
  have hww : P3.ww T P = P 1 + 2 * T := rfl
  have ht9 : 1 + t ≤ 9 * A := by
    omega
  have hKn : R + 1 ≤ n := by
    have : M ≤ M ^ 12 := Nat.le_self_pow (by norm_num) M
    omega
  have hSn : (1 + t) * (2 * T) ≤ n := by
    have h1 : (1 + t) * (2 * T) ≤ (9 * A) * (2 * (4 * A)) := Nat.mul_le_mul ht9 (by omega)
    have h2 : (9 * A) * (2 * (4 * A)) ≤ (A * A * A) * (A * A * A) := (ar2 A hA16).2
    omega
  rw [ht] at hSn
  obtain ⟨hocc1, hnub⟩ := htab R h T P hP1 hP2 hPz hh1 hhR hTT hKn hSn
  rw [← ht] at hocc1 hnub
  -- degree bookkeeping
  have hd2 : 2 * (A + 1 + t) ≤ d := by
    have : A * A * M ≥ 64 * A := ar3 A M hA16 hM4
    omega
  obtain ⟨D, hD⟩ : ∃ D, D = d - t := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = 2 * (n / (2 * M)) := ⟨_, rfl⟩
  have hLev : Even L := by rw [hL]; exact even_two_mul _
  have hmML : m * M ≤ n / (2 * M) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have h1 : m * M * (2 * M) ≤ M * M * (2 * M) := by
      apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_right _ hmM
    have h2 : M * M * (2 * M) ≤ M ^ 12 := by
      rw [show M * M * (2 * M) = 2 * M ^ 3 by ring]
      have : 2 * M ^ 3 ≤ M ^ 4 := by
        rw [show M ^ 4 = M * M ^ 3 by ring]; exact Nat.mul_le_mul_right _ (by omega)
      exact le_trans this (Nat.pow_le_pow_right (by omega) (by norm_num))
    omega
  have hRL : 0 < R → 2 ≤ L ∧ (R + 1) * L ≤ n := by
    intro _
    refine ⟨?_, ?_⟩
    · have : 1 ≤ m * M := Nat.mul_pos hm (by omega)
      omega
    · rw [hR, hL, show M * (2 * (n / (2 * M))) = (2 * M) * (n / (2 * M)) by ring]
      exact Nat.mul_div_le n (2 * M)
  -- eps ≤ lam on rows, and sums
  have hnu_i : ∀ i, 1 ≤ i → P3.nu h T P i = P i + (if i ≤ h then 2 * T else 0) := by
    intro i hi
    have : i ≠ 0 := by omega
    simp [P3.nu, this]
  have hsumsplit : ∑ i ∈ Finset.range R, P3.nu h T P (i + 1) + G4b.bsum R eps = b := by
    rw [G4b.bsum, ← Finset.sum_add_distrib, ← hbR]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hnu_i (i + 1) (by omega)]
    exact hsplit (i + 1) (by omega)
  have hqd : 2 * M * (G4b.bsum R eps / L) ≤ d := by
    have h1 : G4b.bsum R eps / L * L ≤ G4b.bsum R eps := Nat.div_mul_le_self _ _
    have h2 : 2 * (m * M) ≤ L := by omega
    have h3 : G4b.bsum R eps / L * (2 * (m * M)) ≤ m * d := by
      have := Nat.mul_le_mul_left (G4b.bsum R eps / L) h2
      omega
    have h4 : m * (2 * M * (G4b.bsum R eps / L)) ≤ m * d := by
      rw [show m * (2 * M * (G4b.bsum R eps / L)) = G4b.bsum R eps / L * (2 * (m * M)) by ring]
      exact h3
    exact Nat.le_of_mul_le_mul_left h4 hm
  have hDb : (R + 1) * (R + G4b.bsum R eps / L) + 1 ≤ D := by
    rw [hR, Nat.mul_add]
    have h1 : M * R ≤ A := by rw [hA]; exact Nat.mul_le_mul_left _ (by omega)
    have h2 : M * (G4b.bsum R eps / L) * 2 ≤ d := by
      rw [show M * (G4b.bsum R eps / L) * 2 = 2 * M * (G4b.bsum R eps / L) by ring]; exact hqd
    omega
  have hpad := G4b.pad_even Occ n hadd hrect L hLev R hRL eps hez hea hev D hDb t _ hocc1
  have htD : t + D = d := by omega
  rw [htD] at hpad
  convert hpad using 1
  funext i
  by_cases hi : i = 0
  · subst hi
    simp only [G4b.Wt, if_true]
    have hl0 : lam 0 + b = n * d := by
      obtain ⟨k, hk⟩ : ∃ k, n * n = k + 1 := ⟨n * n - 1, by
        have : 1 ≤ n * n := Nat.mul_pos hn1 hn1
        omega⟩
      rw [hk, Finset.sum_range_succ'] at hsum
      rw [hb, hk, Finset.sum_range_succ, hlen (k + 1) (by omega)]
      omega
    have hbD : G4b.bsum R eps ≤ n * D := by
      have h1 : m * d ≤ n * D := by
        have : m * d ≤ m * (2 * D) := Nat.mul_le_mul_left _ (by omega)
        have h2 : m * (2 * D) = (2 * m) * D := by ring
        have h3 : (2 * m) * D ≤ n * D := Nat.mul_le_mul_right _ (by
          have : m * m ≤ M ^ 12 := by
            rw [← hM]; exact Nat.le_self_pow (by norm_num) M
          omega)
        omega
      omega
    have hnd : n * d = n * t + n * D := by rw [← htD, Nat.mul_add]
    omega
  · simp only [G4b.Wt, if_neg hi]
    rw [hnu_i i (by omega)]
    exact (hsplit i (by omega)).symm

end P4

/-! ===== Assembly (a586c963 session 8): tableau occurrences + even padding + small body ===== -/

open GCTOcc in
theorem p3_tab_occurs (n R h T : ℕ) (P : ℕ → ℕ) (hP1 : ∀ i, P (i + 1) ≤ P i)
    (hP2 : ∀ i, P i ≤ P (i + 1) + 1) (hPz : ∀ i, R < i → P i = 0) (hh1 : 1 ≤ h) (hhR : h ≤ R)
    (hT : (R + 1) * (R + 1) + 5 * R + 3 ≤ 2 * T) (hKn : R + 1 ≤ n)
    (hSn : (1 + (P3.ww T P + h + R)) * (2 * T) ≤ n) :
    Occurs n (P3.ww T P + h + R) (fun i => if i = 0 then
          n * (P3.ww T P + h + R) - ∑ i ∈ Finset.range R, P3.nu h T P (i + 1)
        else P3.nu h T P i) (orbitClosure n (detPoly n)) ∧
      ∑ i ∈ Finset.range R, P3.nu h T P (i + 1) ≤ n * (P3.ww T P + h + R) := by
  obtain ⟨c, a, e, hc, hcol, hrow0, hbody, hdist, hpos, hS, hw1, hw0, hsum⟩ :=
    P3.tableau R h T P hP1 hP2 hPz hh1 hhR hT
  have H := p2_occurs n (P3.ww T P) (R + 1) (P3.ww T P + h + R) (2 * T) (by omega) hKn c hc a e
    hcol hrow0 hbody hdist hpos hS hSn
  have hTn : 2 * T ≤ n := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hSn
  have hle : ∀ s, a s ≤ n := fun s => le_trans (hS s) hTn
  have hsplit : ∑ s, (n - a s) + ∑ s, a s = (P3.ww T P + h + R) * n := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun s _ => Nat.sub_add_cancel (hle s))]
    simp [Finset.sum_const, Finset.card_univ]
  rw [hsum] at hsplit
  have hmc : n * (P3.ww T P + h + R) = (P3.ww T P + h + R) * n := mul_comm _ _
  refine ⟨?_, by omega⟩
  have key : p2lam (∑ s, (n - a s)) (P3.ww T P) c = (fun i => if i = 0 then
          n * (P3.ww T P + h + R) - ∑ i ∈ Finset.range R, P3.nu h T P (i + 1)
        else P3.nu h T P i) := by
    funext i
    simp only [p2lam]
    by_cases hi : i = 0
    · subst hi
      rw [if_pos rfl, if_pos rfl, hw0]
      omega
    · rw [if_neg hi, if_neg hi, zero_add, hw1 i (by omega)]
  rw [key] at H
  exact H

open GCTOcc in
theorem solution (n d m : ℕ) (hn : 0 < n) (hd : 0 < d) (hm : 0 < m)
    (hnm : m ^ 25 ≤ n) (lam : ℕ → ℕ) (hlam : IsPartitionOf lam (n * n) (n * d))
    (h : Occurs n d lam (orbitClosure n (paddedPerm m n))) :
    Occurs n d lam (orbitClosure n (detPoly n)) := by
  have hmn : m ≤ n := le_trans (Nat.le_self_pow (by norm_num) m) hnm
  obtain ⟨hz, hbody⟩ := kl_shape_pos n d m hm hmn lam hlam h
  by_cases hsmall : (∑ i ∈ Finset.range (n * n), lam (i + 1)) *
      ((∑ i ∈ Finset.range (n * n), lam (i + 1)) + 1) ≤ n
  · obtain ⟨F, hF, p, hp, hne⟩ := h
    obtain ⟨g, -, hg⟩ := gct_orbit_of_closure hp F hne
    obtain ⟨q, hq, hq0⟩ := p1_small_body n d _ lam hlam le_rfl hsmall F hF
      ⟨_, kl_isForm_substLin n g _ (kl_isForm_paddedPerm m n hm hmn), hg⟩
    exact ⟨F, hF, q, hq, hq0⟩
  · exact P4.big_assembly (fun d lam => Occurs n d lam (orbitClosure n (detPoly n))) n d m
      (fun d₁ d₂ a b h₁ h₂ => gct_occurs_add n d₁ d₂ a b h₁ h₂)
      (fun k l hk hkl hl => g3_row_extended_rectangle_occurs n k l hk hkl hl)
      (fun R h T P hP1 hP2 hPz hh1 hhR hT hKn hSn =>
        p3_tab_occurs n R h T P hP1 hP2 hPz hh1 hhR hT hKn hSn)
      hm hnm lam hlam.1 hlam.2.1 hlam.2.2 hz hbody hsmall
