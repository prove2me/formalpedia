-- Prove2me | solution 1 for GCTOcc.occurs_add_of_occurs
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T06:57:24.709783+00:00
-- url     : https://prove2.me/submissions/083752b2-d0ca-46a9-96c5-7ff4d16e9f62

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

theorem gct_orbit_mem_closure (n : ℕ) (p₀ : GCTOcc.PolyR)
    (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hg : IsUnit g.det) :
    GCTOcc.substLin n g p₀ ∈ GCTOcc.orbitClosure n p₀ :=
  ⟨fun _ => g, fun _ => hg, fun _ => tendsto_const_nhds⟩

open GCTOcc in
theorem solution (n d₁ d₂ : ℕ) (lam mu : ℕ → ℕ)
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
