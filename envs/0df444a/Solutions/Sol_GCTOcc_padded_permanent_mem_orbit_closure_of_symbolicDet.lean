-- Prove2me | solution 1 for GCTOcc.padded_permanent_mem_orbit_closure_of_symbolicDet
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T07:06:04.777003+00:00
-- url     : https://prove2.me/submissions/a7d828f5-aa14-4bec-b7f2-6adb03895f18

import Mathlib
import Definitions.Def_GCTOcc_occurrence

set_option autoImplicit false

open MvPolynomial Filter Topology

/-- `f : ℂ → ℂ` is a polynomial function. -/
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
  apply (Polynomial.finite_setOfPred_isRoot hP0).subset
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

theorem gctRho_permPoly {n m : ℕ} (hmn : m ≤ n) (u : ℂ) :
    gctRho n u (GCTOcc.permPoly m) = C (u ^ m) * GCTOcc.permPoly m := by
  simp only [GCTOcc.permPoly, gctRho, map_sum, map_prod, aeval_X, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  have h : ∀ i : Fin m, ((if (i : ℕ) < n ∧ ((σ i : Fin m) : ℕ) < n then
      C u * X ((i : ℕ), ((σ i : Fin m) : ℕ)) else 0) : GCTOcc.PolyR)
        = C u * X ((i : ℕ), ((σ i : Fin m) : ℕ)) := by
    intro i
    rw [if_pos ⟨lt_of_lt_of_le i.2 hmn, lt_of_lt_of_le (σ i).2 hmn⟩]
  simp only [h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    map_pow]

/-- Homogenisation: from `det (C c + C u * ℓ) = u^m per_m` for all `u`, get
`det (ℓ + C c * X00) = X00^(n-m) per_m`. -/
theorem gct_homogenize (n m : ℕ) (hmn : m ≤ n) (c : Fin n → Fin n → ℂ)
    (ℓ : Fin n → Fin n → GCTOcc.PolyR)
    (h : ∀ u : ℂ, (Matrix.of fun i j => C (c i j) + C u * ℓ i j).det
      = C (u ^ m) * GCTOcc.permPoly m) :
    (Matrix.of fun i j => ℓ i j + C (c i j) * (X (0, 0) : GCTOcc.PolyR)).det
      = (X (0, 0) : GCTOcc.PolyR) ^ (n - m) * GCTOcc.permPoly m := by
  -- scalar identity
  have hs : ∀ s : ℂ, s ≠ 0 →
      (Matrix.of fun i j => ℓ i j + C (c i j) * C s).det = C (s ^ (n - m)) * GCTOcc.permPoly m := by
    intro s hs0
    have h1 := h s⁻¹
    have hmat : (Matrix.of fun i j => C (c i j) + C s⁻¹ * ℓ i j)
        = (C s⁻¹ : GCTOcc.PolyR) • (Matrix.of fun i j => ℓ i j + C (c i j) * C s) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
      rw [mul_add, ← mul_assoc, mul_comm (C s⁻¹) (C (c i j)), mul_assoc, ← map_mul,
        inv_mul_cancel₀ hs0, map_one, mul_one, add_comm]
    rw [hmat, Matrix.det_smul, Fintype.card_fin] at h1
    have h2 : (C s : GCTOcc.PolyR) ^ n * (C s⁻¹) ^ n = 1 := by
      rw [← mul_pow, ← map_mul, mul_inv_cancel₀ hs0, map_one, one_pow]
    calc (Matrix.of fun i j => ℓ i j + C (c i j) * C s).det
        = (C s) ^ n * ((C s⁻¹) ^ n * (Matrix.of fun i j => ℓ i j + C (c i j) * C s).det) := by
          rw [← mul_assoc, h2, one_mul]
      _ = (C s) ^ n * (C (s⁻¹ ^ m) * GCTOcc.permPoly m) := by rw [h1]
      _ = C (s ^ (n - m)) * GCTOcc.permPoly m := by
          rw [← mul_assoc, ← map_pow, ← map_mul]
          congr 2
          have hn : n = (n - m) + m := (Nat.sub_add_cancel hmn).symm
          conv_lhs => rw [hn, pow_add]
          rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hs0, one_pow, mul_one]
  -- polynomial identity in an auxiliary variable
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
  set R : Polynomial GCTOcc.PolyR := Q - Polynomial.X ^ (n - m) * Polynomial.C (GCTOcc.permPoly m)
    with hR
  have hroot : ∀ s : ℂ, s ≠ 0 → R.IsRoot (C s) := by
    intro s hs0
    simp only [Polynomial.IsRoot, hR, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, heval, hs s hs0, map_pow]
    ring
  have hR0 : R = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hinf : ({0}ᶜ : Set ℂ).Infinite := (Set.finite_singleton (0 : ℂ)).infinite_compl
    apply Set.Infinite.mono _ (hinf.image (C_injective (σ := ℕ × ℕ) (R := ℂ)).injOn)
    rintro _ ⟨s, hs, rfl⟩
    exact hroot s hs
  have hfin := congrArg (Polynomial.eval (X (0, 0) : GCTOcc.PolyR)) hR0
  simp only [hR, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_zero, heval] at hfin
  exact sub_eq_zero.1 hfin

open GCTOcc in
theorem solution (m n : ℕ) (hmn : m ≤ n)
    (h : IsSymbolicDet (permPoly m) n) :
    paddedPerm m n ∈ orbitClosure n (detPoly n) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hm : m = 0 := by omega
    subst hm
    have h1 : paddedPerm 0 0 = substLin 0 1 (detPoly 0) := by
      simp [paddedPerm, permPoly, detPoly, substLin]
    rw [h1]
    exact gct_mem_orbitClosure_of_subst 0 _ 1
  obtain ⟨L, hdeg, hdet⟩ := h
  have haff : ∀ i j, gctAff n (L i j) := fun i j => gctAff_of_totalDegree _ (hdeg i j)
  choose c a ha using haff
  set ℓ : Fin n → Fin n → PolyR := fun i j =>
    ∑ w : Fin n × Fin n, C (a i j w) * X ((w.1 : ℕ), (w.2 : ℕ)) with hℓ
  have hscal : ∀ u : ℂ, (Matrix.of fun i j => C (c i j) + C u * ℓ i j).det
      = C (u ^ m) * permPoly m := by
    intro u
    have h1 := congrArg (gctRho n u) hdet
    have h2 : gctRho n u L.det = (Matrix.of fun i j => gctRho n u (L i j)).det := by
      rw [← AlgHom.coe_toRingHom, RingHom.map_det]
      rfl
    rw [h2, gctRho_permPoly hmn] at h1
    rw [← h1]
    congr 1
    ext i j
    simp only [Matrix.of_apply]
    rw [ha i j u]
  have hhom := gct_homogenize n m hmn c ℓ hscal
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
  have hsub : substLin n g (detPoly n) = paddedPerm m n := by
    rw [gct_substLin_detPoly, paddedPerm, ← hhom]
    refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
    simp only [Matrix.of_apply]
    exact hsum i j
  rw [← hsub]
  exact gct_mem_orbitClosure_of_subst n _ g
