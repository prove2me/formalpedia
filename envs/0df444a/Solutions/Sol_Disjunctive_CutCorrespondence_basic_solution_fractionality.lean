-- Prove2me | solution 1 for Disjunctive.CutCorrespondence.basic_solution_fractionality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T17:13:15.126996+00:00
-- url     : https://prove2.me/submissions/81bf2200-bc0a-4d86-8fb0-ccfc79c5302c

import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp
import Definitions.Def_Disjunctive_CutCorrespondence_Tableau



namespace Disjunctive.CutCorrespondence

section core
variable {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M] [DecidableEq (Fin n)]

lemma cc_invrow (Atil : Matrix M (Fin n) ℝ) (ι : Fin n → M) (hnonsing : IsUnit (Ahat Atil ι).det)
    (k i : Fin n) :
    ∑ j, (Ahat Atil ι)⁻¹ k j * Ahat Atil ι j i = if i = k then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul _ hnonsing) k) i
  rw [Matrix.mul_apply] at h
  rw [h, Matrix.one_apply]
  by_cases hik : i = k
  · subst hik; simp
  · simp [hik, Ne.symm hik]

lemma cc_xk (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M)
    (hnonsing : IsUnit (Ahat Atil ι).det) (k : Fin n) (x : Fin n → ℝ) :
    x k = ∑ j, (Ahat Atil ι)⁻¹ k j * Surplus Atil btil ι j x + Abar0 Atil btil ι k := by
  have h1 : ∑ j, (Ahat Atil ι)⁻¹ k j * Surplus Atil btil ι j x
      = ∑ i, (∑ j, (Ahat Atil ι)⁻¹ k j * Ahat Atil ι j i) * x i
        - ∑ j, (Ahat Atil ι)⁻¹ k j * Bhat btil ι j := by
    simp only [Surplus, dotProduct, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Ahat, Bhat, mul_assoc]
  rw [h1]
  simp only [cc_invrow Atil ι hnonsing, Abar0, Matrix.mulVec, dotProduct]
  simp

lemma cc_solve (Atil : Matrix M (Fin n) ℝ) (ι : Fin n → M)
    (hnonsing : IsUnit (Ahat Atil ι).det) (k : Fin n) (c : ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, ∑ j, w j * Ahat Atil ι j i = if i = k then c else 0) (j : Fin n) :
    w j = c * (Ahat Atil ι)⁻¹ k j := by
  have hAB := Matrix.mul_nonsing_inv _ hnonsing
  have : ∑ i, (∑ l, w l * Ahat Atil ι l i) * (Ahat Atil ι)⁻¹ i j = w j := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ l, ∑ i, w l * Ahat Atil ι l i * (Ahat Atil ι)⁻¹ i j = w l * (if l = j then 1 else 0) := by
      intro l
      have h := congrFun (congrFun hAB l) j
      rw [Matrix.mul_apply, Matrix.one_apply] at h
      simp only [mul_assoc, ← Finset.mul_sum, h]
    simp only [this]
    simp
  rw [← this]
  simp only [hw]
  simp

lemma cc_reindex (ι : Fin n → M) (hι : Function.Injective ι) (f : M → ℝ)
    (hf : ∀ ρ, (∀ j, ι j ≠ ρ) → f ρ = 0) : ∑ ρ, f ρ = ∑ j, f (ι j) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := ι) (f := f) (fun a _ b _ h => hι h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro ρ _ hρ
  apply hf
  intro j hj
  exact hρ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)

/-- the core identity -/
lemma cc_core (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (k : Fin n)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) (ι : Fin n → M)
    (hfeas : IsCGLPKFeasible Atil btil k α u u0 v v0 β) (hu0 : 0 < u0) (hv0 : 0 < v0)
    (hι : Function.Injective ι) (hnonsing : IsUnit (Ahat Atil ι).det)
    (hsupp : ∀ ρ, (∀ j, ι j ≠ ρ) → u ρ = 0 ∧ v ρ = 0) (hcomp : ∀ ρ, u ρ * v ρ = 0) :
    (u0 + v0) * Abar0 Atil btil ι k = v0 ∧
    ∀ x, dotProduct α x - β = (u0 + v0) *
      ((∑ i, PiCoef Atil btil ι k i * Surplus Atil btil ι i x) - Pi0 Atil btil ι k) := by
  obtain ⟨h1, h2, h3, h4, h5, hu, hv, -, -⟩ := hfeas
  set B := (Ahat Atil ι)⁻¹ with hB
  set U : Fin n → ℝ := fun j => u (ι j)
  set V : Fin n → ℝ := fun j => v (ι j)
  have hUa : ∀ i, α i = ∑ j, U j * Ahat Atil ι j i - (if i = k then u0 else 0) := by
    intro i
    have := h1 i
    rw [cc_reindex ι hι (fun ρ => u ρ * Atil ρ i) (fun ρ hρ => by simp [(hsupp ρ hρ).1])] at this
    simp only [U, Ahat]
    by_cases hik : i = k
    · rw [if_pos hik] at this ⊢; linarith
    · rw [if_neg hik] at this ⊢; linarith
  have hVa : ∀ i, α i = ∑ j, V j * Ahat Atil ι j i + (if i = k then v0 else 0) := by
    intro i
    have := h2 i
    rw [cc_reindex ι hι (fun ρ => v ρ * Atil ρ i) (fun ρ hρ => by simp [(hsupp ρ hρ).2])] at this
    simp only [V, Ahat]
    by_cases hik : i = k
    · rw [if_pos hik] at this ⊢; linarith
    · rw [if_neg hik] at this ⊢; linarith
  have hw : ∀ i, ∑ j, (U j - V j) * Ahat Atil ι j i = if i = k then u0 + v0 else 0 := by
    intro i
    have e1 := hUa i; have e2 := hVa i
    simp only [sub_mul, Finset.sum_sub_distrib]
    split_ifs at e1 e2 ⊢ <;> linarith
  have hUV : ∀ j, U j - V j = (u0 + v0) * B k j := fun j =>
    cc_solve Atil ι hnonsing k (u0 + v0) (fun j => U j - V j) hw j
  have hUb : β = ∑ j, U j * Bhat btil ι j := by
    rw [cc_reindex ι hι (fun ρ => u ρ * btil ρ) (fun ρ hρ => by simp [(hsupp ρ hρ).1])] at h3
    simp only [U, Bhat]; linarith
  have hVb : β = ∑ j, V j * Bhat btil ι j + v0 := by
    rw [cc_reindex ι hι (fun ρ => v ρ * btil ρ) (fun ρ hρ => by simp [(hsupp ρ hρ).2])] at h4
    simp only [V, Bhat]; linarith
  have habar : (u0 + v0) * Abar0 Atil btil ι k = v0 := by
    have : ∑ j, (U j - V j) * Bhat btil ι j = v0 := by
      simp only [sub_mul, Finset.sum_sub_distrib]; linarith
    simp only [hUV] at this
    refine Eq.trans ?_ this
    rw [Abar0, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  refine ⟨habar, fun x => ?_⟩
  set z := Abar0 Atil btil ι k with hz
  have hxk := cc_xk Atil btil ι hnonsing k x
  rw [← hB, ← hz] at hxk
  have hdot : dotProduct α x - β = ∑ j, U j * Surplus Atil btil ι j x - u0 * x k := by
    have : dotProduct α x = ∑ j, U j * (∑ i, Ahat Atil ι j i * x i) - u0 * x k := by
      simp only [dotProduct, hUa, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      · simp
    rw [this, hUb]
    simp only [Surplus, mul_sub, Finset.sum_sub_distrib, dotProduct, Ahat, Bhat]
    ring
  have hc : 0 < u0 + v0 := by linarith
  have hcoef : ∀ j, U j - u0 * B k j = (u0 + v0) * PiCoef Atil btil ι k j := by
    intro j
    have hU : 0 ≤ U j := hu (ι j)
    have hV : 0 ≤ V j := hv (ι j)
    have hcj : U j * V j = 0 := hcomp (ι j)
    have e := hUV j
    simp only [PiCoef, Pi1, Pi2, Abar, ← hB, ← hz]
    rw [mul_max_of_nonneg _ _ hc.le]
    rcases mul_eq_zero.mp hcj with h | h
    · rw [h] at e ⊢
      have hle : (u0 + v0) * B k j ≤ 0 := by linarith
      rw [max_eq_left]
      · have : (u0 + v0) * (-B k j * (1 - z)) = -B k j * ((u0 + v0) - (u0 + v0) * z) := by ring
        rw [this, habar]; ring
      · have h1' : (u0 + v0) * (- -B k j * z) = B k j * ((u0 + v0) * z) := by ring
        have h2' : (u0 + v0) * (-B k j * (1 - z)) = -B k j * ((u0 + v0) - (u0 + v0) * z) := by ring
        rw [h1', h2', habar]; nlinarith
    · rw [h] at e
      have hle : 0 ≤ (u0 + v0) * B k j := by linarith
      rw [max_eq_right]
      · have : (u0 + v0) * (- -B k j * z) = B k j * ((u0 + v0) * z) := by ring
        rw [this, habar]; nlinarith
      · have h1' : (u0 + v0) * (- -B k j * z) = B k j * ((u0 + v0) * z) := by ring
        have h2' : (u0 + v0) * (-B k j * (1 - z)) = -B k j * ((u0 + v0) - (u0 + v0) * z) := by ring
        rw [h1', h2', habar]; nlinarith
  have hp0 : u0 * z = (u0 + v0) * Pi0 Atil btil ι k := by
    simp only [Pi0, ← hz]
    have : (u0 + v0) * (z * (1 - z)) = z * ((u0 + v0) - (u0 + v0) * z) := by ring
    rw [this, habar]; ring
  rw [hdot, hxk]
  have hfin : ∀ j, U j * Surplus Atil btil ι j x - u0 * (B k j * Surplus Atil btil ι j x)
      = (u0 + v0) * (PiCoef Atil btil ι k j * Surplus Atil btil ι j x) := by
    intro j
    rw [show (u0 + v0) * (PiCoef Atil btil ι k j * Surplus Atil btil ι j x)
      = ((u0 + v0) * PiCoef Atil btil ι k j) * Surplus Atil btil ι j x by ring, ← hcoef j]
    ring
  calc ∑ j, U j * Surplus Atil btil ι j x - u0 * (∑ j, B k j * Surplus Atil btil ι j x + z)
      = ∑ j, (U j * Surplus Atil btil ι j x - u0 * (B k j * Surplus Atil btil ι j x)) - u0 * z := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; ring
    _ = ∑ j, (u0 + v0) * (PiCoef Atil btil ι k j * Surplus Atil btil ι j x) - u0 * z := by
        simp only [hfin]
    _ = _ := by rw [hp0, mul_sub, Finset.mul_sum]

end core

section ext
variable {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]

/-- perturbed point -/
noncomputable def ccQ (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) (ρ : M) (s : ℝ) :
    (Fin n → ℝ) × (M → ℝ) × ℝ × (M → ℝ) × ℝ × ℝ :=
  (fun i => (α i + s * Atil ρ i) / (1 + 2 * s), fun σ => (u σ + if σ = ρ then s else 0) / (1 + 2 * s),
    u0 / (1 + 2 * s), fun σ => (v σ + if σ = ρ then s else 0) / (1 + 2 * s), v0 / (1 + 2 * s),
    (β + s * btil ρ) / (1 + 2 * s))

lemma ccQ_feas (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (k : Fin n)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) (ρ : M) (s : ℝ)
    (hfeas : IsCGLPKFeasible Atil btil k α u u0 v v0 β) (hT : 0 < 1 + 2 * s)
    (hus : 0 ≤ u ρ + s) (hvs : 0 ≤ v ρ + s) :
    ccQ Atil btil α u u0 v v0 β ρ s ∈ CGLPKFeasibleSet Atil btil k := by
  obtain ⟨h1, h2, h3, h4, h5, hu, hv, hu0, hv0⟩ := hfeas
  have hT' : (1 + 2 * s) ≠ 0 := hT.ne'
  simp only [CGLPKFeasibleSet, Set.mem_setOf_eq, ccQ, IsCGLPKFeasible]
  have sA : ∀ i, ∑ σ, (if σ = ρ then s else 0) * Atil σ i = s * Atil ρ i := by
    intro i; simp [ite_mul]
  have sb : ∑ σ, (if σ = ρ then s else 0) * btil σ = s * btil ρ := by simp [ite_mul]
  have s1 : ∑ σ, (if σ = ρ then s else (0:ℝ)) = s := by simp
  refine ⟨fun i => ?_, fun i => ?_, ?_, ?_, ?_, fun σ => ?_, fun σ => ?_, ?_, ?_⟩
  · have e := h1 i
    have : ∑ σ, (u σ + (if σ = ρ then s else 0)) / (1 + 2 * s) * Atil σ i
        = (∑ σ, u σ * Atil σ i + s * Atil ρ i) / (1 + 2 * s) := by
      rw [← sA i, ← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun σ _ => by ring
    rw [this]
    split_ifs at e ⊢
    · linear_combination e / (1 + 2 * s)
    · linear_combination e / (1 + 2 * s)
  · have e := h2 i
    have : ∑ σ, (v σ + (if σ = ρ then s else 0)) / (1 + 2 * s) * Atil σ i
        = (∑ σ, v σ * Atil σ i + s * Atil ρ i) / (1 + 2 * s) := by
      rw [← sA i, ← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun σ _ => by ring
    rw [this]
    split_ifs at e ⊢
    · linear_combination e / (1 + 2 * s)
    · linear_combination e / (1 + 2 * s)
  · have : ∑ σ, (u σ + (if σ = ρ then s else 0)) / (1 + 2 * s) * btil σ
        = (∑ σ, u σ * btil σ + s * btil ρ) / (1 + 2 * s) := by
      rw [← sb, ← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun σ _ => by ring
    rw [this]
    first
    | linear_combination h3 / (1 + 2 * s)
    | linear_combination h4 / (1 + 2 * s)
  · have : ∑ σ, (v σ + (if σ = ρ then s else 0)) / (1 + 2 * s) * btil σ
        = (∑ σ, v σ * btil σ + s * btil ρ) / (1 + 2 * s) := by
      rw [← sb, ← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun σ _ => by ring
    rw [this]
    first
    | linear_combination h3 / (1 + 2 * s)
    | linear_combination h4 / (1 + 2 * s)
  · rw [← Finset.sum_div, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib, s1,
      ← add_div, ← add_div, ← add_div, div_eq_one_iff_eq hT']
    linarith
  · show 0 ≤ (u σ + (if σ = ρ then s else 0)) / (1 + 2 * s)
    apply div_nonneg _ hT.le
    split_ifs with h
    · subst h; exact hus
    · simpa using hu σ
  · show 0 ≤ (v σ + (if σ = ρ then s else 0)) / (1 + 2 * s)
    apply div_nonneg _ hT.le
    split_ifs with h
    · subst h; exact hvs
    · simpa using hv σ
  · exact div_nonneg hu0 hT.le
  · exact div_nonneg hv0 hT.le

lemma cc_comp (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (k : Fin n)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ)
    (hbasic : IsBasicCGLPKSolution Atil btil k α u u0 v v0 β) (hu0 : 0 < u0) (ρ : M) :
    u ρ * v ρ = 0 := by
  have hfeas : IsCGLPKFeasible Atil btil k α u u0 v v0 β := hbasic.1
  obtain ⟨-, -, -, -, h5, hu, hv, -, hv0⟩ := hfeas
  have hup := hu ρ; have hvp := hv ρ
  simp only [Pi.zero_apply] at hup hvp
  by_contra hne
  have hupos : 0 < u ρ := lt_of_le_of_ne hup (fun h => hne (by rw [← h]; ring))
  have hvpos : 0 < v ρ := lt_of_le_of_ne hvp (fun h => hne (by rw [← h]; ring))
  have hule : u ρ ≤ ∑ σ, u σ := Finset.single_le_sum (fun σ _ => hu σ) (Finset.mem_univ ρ)
  have hvle : v ρ ≤ ∑ σ, v σ := Finset.single_le_sum (fun σ _ => hv σ) (Finset.mem_univ ρ)
  set ε := min (u ρ) (v ρ) / 2 with hε
  have hεpos : 0 < ε := by positivity
  have hεu : ε ≤ u ρ := by have := min_le_left (u ρ) (v ρ); linarith
  have hεv : ε ≤ v ρ := by have := min_le_right (u ρ) (v ρ); linarith
  have hε4 : 2 * ε < 1 := by linarith
  have hq1 := ccQ_feas Atil btil k α u u0 v v0 β ρ ε hbasic.1 (by linarith) (by linarith) (by linarith)
  have hq2 := ccQ_feas Atil btil k α u u0 v v0 β ρ (-ε) hbasic.1 (by linarith) (by linarith) (by linarith)
  have hseg : (α, u, u0, v, v0, β) ∈ openSegment ℝ (ccQ Atil btil α u u0 v v0 β ρ ε)
      (ccQ Atil btil α u u0 v v0 β ρ (-ε)) := by
    refine ⟨(1 + 2 * ε) / 2, (1 + 2 * -ε) / 2, by linarith, by linarith, by ring, ?_⟩
    have h1 : (1 + 2 * ε) ≠ 0 := by linarith
    have h2 : (1 + 2 * -ε) ≠ 0 := by linarith
    have cancel : ∀ T X : ℝ, T ≠ 0 → T / 2 * (X / T) = X / 2 := fun T X hT => by field_simp
    simp only [ccQ, Prod.smul_mk, Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cancel _ _ h1, cancel _ _ h2]
      try split_ifs
      all_goals ring
    · funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cancel _ _ h1, cancel _ _ h2]
      try split_ifs
      all_goals ring
    · simp only [smul_eq_mul, cancel _ _ h1, cancel _ _ h2]; ring
    · funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cancel _ _ h1, cancel _ _ h2]
      try split_ifs
      all_goals ring
    · simp only [smul_eq_mul, cancel _ _ h1, cancel _ _ h2]; ring
    · simp only [smul_eq_mul, cancel _ _ h1, cancel _ _ h2]; ring
  have := ((mem_extremePoints.mp hbasic).2 _ hq1 _ hq2 hseg).1
  simp only [ccQ, Prod.mk.injEq] at this
  have e := this.2.2.1
  have h1 : (1 + 2 * ε) ≠ 0 := by linarith
  field_simp at e
  nlinarith

end ext

section main
variable {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M] [DecidableEq (Fin n)]

lemma cc_supp_of_image (u v : M → ℝ) (M1 M2 : Finset M) (ι : Fin n → M)
    (hu_supp : ∀ ρ ∉ M1, u ρ = 0) (hv_supp : ∀ ρ ∉ M2, v ρ = 0)
    (hι_image : Finset.image ι Finset.univ = M1 ∪ M2) :
    ∀ ρ, (∀ j, ι j ≠ ρ) → u ρ = 0 ∧ v ρ = 0 := by
  intro ρ hρ
  have : ρ ∉ M1 ∪ M2 := by
    rw [← hι_image]; simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact hρ
  rw [Finset.mem_union, not_or] at this
  exact ⟨hu_supp ρ this.1, hv_supp ρ this.2⟩

theorem frac_core (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (k : Fin n)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) (M1 M2 : Finset M)
    (ι : Fin n → M) (hbasic : IsBasicCGLPKSolution Atil btil k α u u0 v v0 β) (hu0 : 0 < u0)
    (hv0 : 0 < v0) (hu_supp : ∀ ρ ∉ M1, u ρ = 0) (hv_supp : ∀ ρ ∉ M2, v ρ = 0)
    (hι_inj : Function.Injective ι) (hι_image : Finset.image ι Finset.univ = M1 ∪ M2)
    (hnonsing : IsUnit (Ahat Atil ι).det) :
    0 < Abar0 Atil btil ι k ∧ Abar0 Atil btil ι k < 1 := by
  have h := (cc_core Atil btil k α u u0 v v0 β ι hbasic.1 hu0 hv0 hι_inj hnonsing
    (cc_supp_of_image u v M1 M2 ι hu_supp hv_supp hι_image)
    (cc_comp Atil btil k α u u0 v v0 β hbasic hu0)).1
  constructor <;> nlinarith

theorem lp_core (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (k : Fin n)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) (M1 M2 : Finset M)
    (ι : Fin n → M) (hbasic : IsBasicCGLPKSolution Atil btil k α u u0 v v0 β) (hu0 : 0 < u0)
    (hv0 : 0 < v0) (hu_supp : ∀ ρ ∉ M1, u ρ = 0) (hv_supp : ∀ ρ ∉ M2, v ρ = 0)
    (hι_inj : Function.Injective ι) (hι_image : Finset.image ι Finset.univ = M1 ∪ M2)
    (hnonsing : IsUnit (Ahat Atil ι).det) :
    {x | β ≤ dotProduct α x} = SimpleDisjCutSet Atil btil ι k := by
  have h := (cc_core Atil btil k α u u0 v v0 β ι hbasic.1 hu0 hv0 hι_inj hnonsing
    (cc_supp_of_image u v M1 M2 ι hu_supp hv_supp hι_image)
    (cc_comp Atil btil k α u u0 v v0 β hbasic hu0)).2
  ext x
  simp only [Set.mem_setOf_eq, SimpleDisjCutSet]
  have hx := h x
  have hc : 0 < u0 + v0 := by linarith
  constructor
  · intro hb
    have : 0 ≤ (u0 + v0) * ((∑ i, PiCoef Atil btil ι k i * Surplus Atil btil ι i x) -
      Pi0 Atil btil ι k) := by linarith
    have := (mul_nonneg_iff_of_pos_left hc).mp this
    linarith
  · intro hb
    have : 0 ≤ (u0 + v0) * ((∑ i, PiCoef Atil btil ι k i * Surplus Atil btil ι i x) -
      Pi0 Atil btil ι k) := mul_nonneg hc.le (by linarith)
    linarith

/-- lifting a vector on positions to rows -/
def ccLift (ι : Fin n → M) (f : Fin n → ℝ) (ρ : M) : ℝ := ∑ j, if ι j = ρ then f j else 0

omit [DecidableEq (Fin n)] in
lemma ccLift_sum (ι : Fin n → M) (f : Fin n → ℝ) (g : M → ℝ) :
    ∑ ρ, ccLift ι f ρ * g ρ = ∑ j, f j * g (ι j) := by
  simp only [ccLift, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [ite_mul]

omit [DecidableEq (Fin n)] in
lemma ccLift_at (ι : Fin n → M) (hι : Function.Injective ι) (f : Fin n → ℝ) (j : Fin n) :
    ccLift ι f (ι j) = f j := by
  simp only [ccLift]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hι.ne hb]
  · simp

omit [DecidableEq (Fin n)] in
lemma ccLift_off (ι : Fin n → M) (f : Fin n → ℝ) (ρ : M) (h : ∀ j, ι j ≠ ρ) :
    ccLift ι f ρ = 0 := by
  simp [ccLift, h]

theorem sd_core (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (k : Fin n)
    (ι : Fin n → M) (hι_inj : Function.Injective ι) (hnonsing : IsUnit (Ahat Atil ι).det)
    (h0 : 0 < Abar0 Atil btil ι k) (h1 : Abar0 Atil btil ι k < 1) (M1 M2 : Finset M)
    (hpart : ∀ i, (Pi1 Atil btil ι k i < Pi2 Atil btil ι k i → ι i ∈ M1) ∧
      (Pi1 Atil btil ι k i > Pi2 Atil btil ι k i → ι i ∈ M2)) :
    ∃ α u u0 v v0 β, IsCGLPKFeasible Atil btil k α u u0 v v0 β ∧ 0 < u0 ∧ 0 < v0 ∧
      (∀ ρ ∉ M1, u ρ = 0) ∧ (∀ ρ ∉ M2, v ρ = 0) ∧
      {x | β ≤ dotProduct α x} = SimpleDisjCutSet Atil btil ι k := by
  set z := Abar0 Atil btil ι k with hz
  set a : Fin n → ℝ := fun j => (Ahat Atil ι)⁻¹ k j with ha
  set U : Fin n → ℝ := fun j => max (a j) 0 with hU
  set V : Fin n → ℝ := fun j => max (-a j) 0 with hV
  have hUV : ∀ j, U j - V j = a j := by
    intro j; simp only [hU, hV]
    rcases le_total (a j) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have hU0 : ∀ j, 0 ≤ U j := fun j => le_max_right _ _
  have hV0 : ∀ j, 0 ≤ V j := fun j => le_max_right _ _
  have hUVc : ∀ j, U j * V j = 0 := by
    intro j; simp only [hU, hV]
    rcases le_total (a j) 0 with h | h
    · rw [max_eq_right h]; ring
    · rw [max_eq_right (by linarith : -a j ≤ 0)]; ring
  set T : ℝ := ∑ j, (U j + V j) + 1 with hT
  have hTpos : 0 < T := by
    have : 0 ≤ ∑ j, (U j + V j) := Finset.sum_nonneg fun j _ => add_nonneg (hU0 j) (hV0 j)
    linarith
  have hTne : T ≠ 0 := hTpos.ne'
  have hinv := cc_invrow Atil ι hnonsing k
  -- Pi1 < Pi2 iff a > 0
  have hPi : ∀ j, Pi1 Atil btil ι k j < Pi2 Atil btil ι k j ↔ 0 < a j := by
    intro j
    simp only [Pi1, Pi2, Abar, ← hz]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  have hPi' : ∀ j, Pi1 Atil btil ι k j > Pi2 Atil btil ι k j ↔ a j < 0 := by
    intro j
    simp only [Pi1, Pi2, Abar, ← hz, gt_iff_lt]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  let u : M → ℝ := fun ρ => ccLift ι U ρ / T
  let v : M → ℝ := fun ρ => ccLift ι V ρ / T
  let u0 : ℝ := (1 - z) / T
  let v0 : ℝ := z / T
  let α : Fin n → ℝ := fun i => (∑ j, U j * Ahat Atil ι j i - (if i = k then 1 - z else 0)) / T
  let β : ℝ := (∑ j, U j * Bhat btil ι j) / T
  have sumU : ∀ g : M → ℝ, ∑ ρ, u ρ * g ρ = (∑ j, U j * g (ι j)) / T := by
    intro g
    rw [← ccLift_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun ρ _ => by simp only [u]; ring
  have sumV : ∀ g : M → ℝ, ∑ ρ, v ρ * g ρ = (∑ j, V j * g (ι j)) / T := by
    intro g
    rw [← ccLift_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun ρ _ => by simp only [v]; ring
  have hab : ∑ j, a j * Bhat btil ι j = z := by
    simp only [hz, Abar0, Matrix.mulVec, dotProduct, ha]
  have hfeas : IsCGLPKFeasible Atil btil k α u u0 v v0 β := by
    refine ⟨fun i => ?_, fun i => ?_, ?_, ?_, ?_, fun ρ => ?_, fun ρ => ?_, ?_, ?_⟩
    · rw [sumU (fun ρ => Atil ρ i)]
      simp only [α, u0, Ahat]
      split_ifs <;> ring
    · rw [sumV (fun ρ => Atil ρ i)]
      have e := hinv i
      have : ∑ j, U j * Ahat Atil ι j i = ∑ j, V j * Ahat Atil ι j i + ∑ j, a j * Ahat Atil ι j i := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by rw [← hUV j]; ring
      simp only [α, v0]
      simp only [Ahat] at this e ⊢
      rw [this, e]
      split_ifs <;> ring
    · rw [sumU btil]; simp only [β, Bhat]; ring
    · rw [sumV btil]
      have : ∑ j, U j * Bhat btil ι j = ∑ j, V j * Bhat btil ι j + ∑ j, a j * Bhat btil ι j := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by rw [← hUV j]; ring
      rw [hab] at this
      simp only [β, v0]
      simp only [Bhat] at this ⊢
      rw [this]; ring
    · have e1 := sumU (fun _ => 1)
      have e2 := sumV (fun _ => 1)
      simp only [mul_one] at e1 e2
      rw [e1, e2]
      simp only [u0, v0]
      rw [← add_div, ← add_div, ← add_div, div_eq_one_iff_eq hTne, hT, Finset.sum_add_distrib]
      ring
    · simp only [u, Pi.zero_apply]
      exact div_nonneg (Finset.sum_nonneg fun j _ => by split_ifs <;> simp [hU0 j]) hTpos.le
    · simp only [v, Pi.zero_apply]
      exact div_nonneg (Finset.sum_nonneg fun j _ => by split_ifs <;> simp [hV0 j]) hTpos.le
    · exact div_nonneg (by linarith) hTpos.le
    · exact div_nonneg h0.le hTpos.le
  have hu0 : 0 < u0 := div_pos (by linarith) hTpos
  have hv0 : 0 < v0 := div_pos h0 hTpos
  refine ⟨α, u, u0, v, v0, β, hfeas, hu0, hv0, ?_, ?_, ?_⟩
  · intro ρ hρ
    simp only [u, ccLift]
    rw [Finset.sum_eq_zero, zero_div]
    intro j _
    split_ifs with h
    · subst h
      have : ¬ 0 < a j := fun hp => hρ ((hpart j).1 ((hPi j).2 hp))
      simp only [hU]; exact max_eq_right (not_lt.mp this)
    · rfl
  · intro ρ hρ
    simp only [v, ccLift]
    rw [Finset.sum_eq_zero, zero_div]
    intro j _
    split_ifs with h
    · subst h
      have : ¬ a j < 0 := fun hp => hρ ((hpart j).2 ((hPi' j).2 hp))
      simp only [hV]; exact max_eq_right (by linarith [not_lt.mp this])
    · rfl
  · have hsupp : ∀ ρ, (∀ j, ι j ≠ ρ) → u ρ = 0 ∧ v ρ = 0 := by
      intro ρ hρ
      simp only [u, v, ccLift_off ι _ ρ hρ, zero_div, and_self]
    have hcomp : ∀ ρ, u ρ * v ρ = 0 := by
      intro ρ
      by_cases hρ : ∃ j, ι j = ρ
      · obtain ⟨j, rfl⟩ := hρ
        simp only [u, v, ccLift_at ι hι_inj]
        rw [div_mul_div_comm, hUVc j, zero_div]
      · push_neg at hρ
        simp only [(hsupp ρ hρ).1, zero_mul]
    have h := (cc_core Atil btil k α u u0 v v0 β ι hfeas hu0 hv0 hι_inj hnonsing hsupp hcomp).2
    have hc : 0 < u0 + v0 := by linarith
    ext x
    simp only [Set.mem_setOf_eq, SimpleDisjCutSet]
    have hx := h x
    constructor
    · intro hb
      have : 0 ≤ (u0 + v0) * ((∑ i, PiCoef Atil btil ι k i * Surplus Atil btil ι i x) -
        Pi0 Atil btil ι k) := by linarith
      have := (mul_nonneg_iff_of_pos_left hc).mp this
      linarith
    · intro hb
      have : 0 ≤ (u0 + v0) * ((∑ i, PiCoef Atil btil ι k i * Surplus Atil btil ι i x) -
        Pi0 Atil btil ι k) := mul_nonneg hc.le (by linarith)
      linarith

end main

end Disjunctive.CutCorrespondence

open Disjunctive.CutCorrespondence


theorem solution {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (k : Fin n)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) (M1 M2 : Finset M)
    (ι : Fin n → M) (hbasic : IsBasicCGLPKSolution Atil btil k α u u0 v v0 β) (hu0 : 0 < u0)
    (hv0 : 0 < v0) (hu_supp : ∀ ρ ∉ M1, u ρ = 0) (hv_supp : ∀ ρ ∉ M2, v ρ = 0)
    (hι_inj : Function.Injective ι) (hι_image : Finset.image ι Finset.univ = M1 ∪ M2)
    (hnonsing : IsUnit (Ahat Atil ι).det) :
    0 < Abar0 Atil btil ι k ∧ Abar0 Atil btil ι k < 1 := by
  exact frac_core Atil btil k α u u0 v v0 β M1 M2 ι hbasic hu0 hv0 hu_supp hv_supp hι_inj hι_image hnonsing
