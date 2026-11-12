-- Prove2me | solution 1 for FiniteSampleDependence.Rigidity.generic_determinant_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:30:16.879692+00:00
-- url     : https://prove2.me/submissions/610477ef-13a5-477f-a501-d049c9b70421

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model
import Definitions.Def_FiniteSampleDependence_Rigidity_PolynomialAlgebra

section
set_option autoImplicit false

namespace FiniteSampleDependence.Dev.Irred

open MvPolynomial Equiv Finsupp

variable {n : ℕ}

noncomputable def mσ (σ : Perm (Fin n)) : (Fin n × Fin n) →₀ ℕ := ∑ i, single (σ i, i) 1

lemma mσ_apply (σ : Perm (Fin n)) (v : Fin n × Fin n) :
    mσ σ v = if σ v.2 = v.1 then 1 else 0 := by
  classical
  simp only [mσ, Finsupp.coe_finsetSum, Finset.sum_apply, single_apply]
  rw [Finset.sum_eq_single v.2]
  · by_cases h : σ v.2 = v.1
    · simp [h]
    · simp [h, Prod.ext_iff]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (by rw [← h])
  · simp

lemma mσ_inj : Function.Injective (mσ (n := n)) := by
  intro σ τ h
  ext i
  have := congrArg (fun m => m (σ i, i)) h
  simp only [mσ_apply] at this
  by_contra hne
  have : τ i = σ i := by simpa using this
  exact hne (by rw [this])

noncomputable abbrev D (n : ℕ) : MvPolynomial (Fin n × Fin n) ℝ :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) ℝ).det

lemma D_eq : D n = ∑ σ : Perm (Fin n), monomial (mσ σ) (((Perm.sign σ : ℤ) : ℝ)) := by
  classical
  rw [D, Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mσ, monomial_sum_index]
  simp [Matrix.mvPolynomialX_apply, X]


lemma mσ_le (σ : Perm (Fin n)) (v : Fin n × Fin n) : mσ σ v ≤ 1 := by
  rw [mσ_apply]; split_ifs <;> simp

lemma degreeOf_D_le (v : Fin n × Fin n) : (D n).degreeOf v ≤ 1 := by
  classical
  rw [degreeOf_le_iff]
  intro m hm
  rw [MvPolynomial.mem_support_iff, D_eq, coeff_sum] at hm
  obtain ⟨σ, _, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [coeff_monomial] at hσ
  by_cases h : mσ σ = m
  · rw [← h]; exact mσ_le σ v
  · simp [h] at hσ

lemma pderiv_D (v : Fin n × Fin n) : pderiv v (D n) =
    ∑ σ : Perm (Fin n), monomial (mσ σ - single v 1) (((Perm.sign σ : ℤ) : ℝ) * (mσ σ v : ℕ)) := by
  rw [D_eq, map_sum]
  simp

lemma pderiv_pderiv_D {v w : Fin n × Fin n} (hvw : v ≠ w) (h : v.1 = w.1 ∨ v.2 = w.2) :
    pderiv v (pderiv w (D n)) = 0 := by
  rw [pderiv_D, map_sum]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [pderiv_monomial]
  have hz : mσ σ w * mσ σ v = 0 := by
    rw [mσ_apply, mσ_apply]
    by_cases h1 : σ w.2 = w.1
    · by_cases h2 : σ v.2 = v.1
      · exfalso
        apply hvw
        rcases h with h | h
        · have : σ w.2 = σ v.2 := by rw [h1, h2, h]
          have := σ.injective this
          exact Prod.ext h this.symm
        · have : v.1 = w.1 := by rw [← h2, ← h1, h]
          exact Prod.ext this h
      · simp [h2]
    · simp [h1]
  have : ((mσ σ - single w 1 : (Fin n × Fin n) →₀ ℕ) v) = mσ σ v := by
    simp [Finsupp.single_apply, hvw.symm]
  rw [this]
  have : (((Perm.sign σ : ℤ) : ℝ) * (mσ σ w : ℕ)) * (mσ σ v : ℕ) = 0 := by
    have : ((mσ σ w : ℕ) : ℝ) * (mσ σ v : ℕ) = 0 := by exact_mod_cast hz
    calc _ = ((Perm.sign σ : ℤ) : ℝ) * (((mσ σ w : ℕ) : ℝ) * (mσ σ v : ℕ)) := by ring
      _ = 0 := by rw [this, mul_zero]
  rw [this, monomial_zero]

lemma pderiv_D_ne_zero (v : Fin n × Fin n) : pderiv v (D n) ≠ 0 := by
  classical
  obtain ⟨τ, hτ⟩ : ∃ τ : Perm (Fin n), τ v.2 = v.1 := ⟨Equiv.swap v.2 v.1, by simp⟩
  have hτv : mσ τ v = 1 := by rw [mσ_apply, if_pos hτ]
  intro h0
  have := congrArg (coeff (mσ τ - single v 1)) h0
  rw [pderiv_D, coeff_sum, coeff_zero, Finset.sum_eq_single τ] at this
  · rw [coeff_monomial, if_pos rfl, hτv] at this
    simp at this
  · intro σ _ hστ
    rw [coeff_monomial]
    split_ifs with h1
    · by_cases hσv : mσ σ v = 0
      · simp [hσv]
      · exfalso
        have hσv1 : mσ σ v = 1 := by have := mσ_le σ v; omega
        have hle : ∀ ρ : Perm (Fin n), mσ ρ v = 1 → single v 1 ≤ mσ ρ := by
          intro ρ hρ
          rw [Finsupp.single_le_iff]; omega
        have := congrArg (· + single v 1) h1
        simp only [tsub_add_cancel_of_le (hle σ hσv1), tsub_add_cancel_of_le (hle τ hτv)] at this
        exact hστ (mσ_inj this)
    · rfl
  · simp


lemma pderiv_comm' {v w : Fin n × Fin n} (hvw : v ≠ w) (g : MvPolynomial (Fin n × Fin n) ℝ) :
    pderiv v (pderiv w g) = pderiv w (pderiv v g) := by
  ext m
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv]
  have h1 : ((m + single v 1 : (Fin n × Fin n) →₀ ℕ) w) = m w := by simp [Finsupp.single_apply, hvw.symm]
  have h2 : ((m + single w 1 : (Fin n × Fin n) →₀ ℕ) v) = m v := by simp [Finsupp.single_apply, hvw]
  rw [h1, h2, add_right_comm m (single v 1) (single w 1)]
  ring

lemma eq_C_of_pderiv_eq_zero (g : MvPolynomial (Fin n × Fin n) ℝ)
    (h : ∀ v, pderiv v g = 0) : ∃ c : ℝ, g = C c := by
  refine ⟨coeff 0 g, ?_⟩
  ext m
  rw [coeff_C]
  by_cases hm : m = 0
  · subst hm; simp
  · rw [if_neg (Ne.symm hm)]
    obtain ⟨v, hv⟩ : ∃ v, m v ≠ 0 := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hm (Finsupp.ext hc)
    have := congrArg (coeff (m - single v 1)) (h v)
    rw [coeff_pderiv, coeff_zero] at this
    have hm' : m - single v 1 + single v 1 = m := by
      apply tsub_add_cancel_of_le
      rw [Finsupp.single_le_iff]; omega
    rw [hm'] at this
    have hne : ((((m - single v 1 : (Fin n × Fin n) →₀ ℕ) v : ℕ)) : ℝ) + 1 ≠ 0 := by positivity
    exact (mul_eq_zero.mp this).resolve_right hne

lemma dichotomy {f g : MvPolynomial (Fin n × Fin n) ℝ} (hfg : f * g = D n) (v : Fin n × Fin n) :
    (pderiv v f = 0 ∨ pderiv v g = 0) ∧ ¬ (pderiv v f = 0 ∧ pderiv v g = 0) := by
  have hD : D n ≠ 0 := fun h => pderiv_D_ne_zero v (by rw [h, map_zero])
  have hf : f ≠ 0 := fun h => hD (by rw [← hfg, h, zero_mul])
  have hg : g ≠ 0 := fun h => hD (by rw [← hfg, h, mul_zero])
  constructor
  · have h1 := degreeOf_D_le v
    rw [← hfg, degreeOf_mul_eq hf hg] at h1
    by_cases hdf : f.degreeOf v = 0
    · left
      exact pderiv_eq_zero_of_notMem_vars (fun hm => (mem_vars_iff_degreeOf_ne_zero.mp hm) hdf)
    · right
      have : g.degreeOf v = 0 := by omega
      exact pderiv_eq_zero_of_notMem_vars (fun hm => (mem_vars_iff_degreeOf_ne_zero.mp hm) this)
  · rintro ⟨h1, h2⟩
    apply pderiv_D_ne_zero v
    rw [← hfg, pderiv_mul, h1, h2]; simp

lemma step {f g : MvPolynomial (Fin n × Fin n) ℝ} (hfg : f * g = D n) {v w : Fin n × Fin n}
    (hvw : v ≠ w) (h : v.1 = w.1 ∨ v.2 = w.2) (hv : pderiv v g = 0) : pderiv w g = 0 := by
  by_contra hw
  have hwf : pderiv w f = 0 := (dichotomy hfg w).1.resolve_right hw
  have hvf : pderiv v f ≠ 0 := fun h0 => (dichotomy hfg v).2 ⟨h0, hv⟩
  have h2 := pderiv_pderiv_D hvw h
  rw [← hfg, pderiv_mul, hwf, zero_mul, zero_add, pderiv_mul,
    pderiv_comm' hvw, hv, map_zero, mul_zero, add_zero] at h2
  exact (mul_ne_zero hvf hw) h2

lemma all_zero {f g : MvPolynomial (Fin n × Fin n) ℝ} (hfg : f * g = D n) (v0 : Fin n × Fin n)
    (h0 : pderiv v0 g = 0) (v : Fin n × Fin n) : pderiv v g = 0 := by
  by_cases h1 : v0 = v
  · rw [← h1]; exact h0
  by_cases h2 : v0.1 = v.1
  · exact step hfg h1 (Or.inl h2) h0
  · have hm : pderiv (v.1, v0.2) g = 0 :=
      step hfg (v := v0) (w := (v.1, v0.2)) (fun h => h2 (by rw [h])) (Or.inr rfl) h0
    by_cases h3 : (v.1, v0.2) = v
    · rw [← h3]; exact hm
    · exact step hfg h3 (Or.inl rfl) hm

lemma irreducible_aux (hn : 1 ≤ n) {f g : MvPolynomial (Fin n × Fin n) ℝ} (hfg : f * g = D n) :
    IsUnit f ∨ IsUnit g := by
  have hD : D n ≠ 0 := fun h =>
    pderiv_D_ne_zero ((⟨0, hn⟩, ⟨0, hn⟩) : Fin n × Fin n) (by rw [h, map_zero])
  have hf : f ≠ 0 := fun h => hD (by rw [← hfg, h, zero_mul])
  have hg : g ≠ 0 := fun h => hD (by rw [← hfg, h, mul_zero])
  have hfg' : g * f = D n := by rw [mul_comm]; exact hfg
  set v0 : Fin n × Fin n := (⟨0, hn⟩, ⟨0, hn⟩)
  rcases (dichotomy hfg v0).1 with h | h
  · left
    obtain ⟨c, hc⟩ := eq_C_of_pderiv_eq_zero f (all_zero hfg' v0 h)
    rw [hc] at hf ⊢
    exact (isUnit_iff_ne_zero.mpr (fun h0 => hf (by rw [h0, C_0]))).map C
  · right
    obtain ⟨c, hc⟩ := eq_C_of_pderiv_eq_zero g (all_zero hfg v0 h)
    rw [hc] at hg ⊢
    exact (isUnit_iff_ne_zero.mpr (fun h0 => hg (by rw [h0, C_0]))).map C

end FiniteSampleDependence.Dev.Irred

namespace FiniteSampleDependence.Rigidity

open MvPolynomial

theorem chk_generic_determinant_irreducible (n : ℕ) (hn : 1 ≤ n) :
    Irreducible (genericMatrix n n).det := by
  refine ⟨?_, fun f g h => ?_⟩
  · intro hu
    have := FiniteSampleDependence.Dev.Irred.pderiv_D_ne_zero (n := n) (⟨0, hn⟩, ⟨0, hn⟩)
    obtain ⟨c, _, hc⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mp hu
    apply this
    have hc' : FiniteSampleDependence.Dev.Irred.D n = C c := hc
    rw [hc', pderiv_C]
  · exact FiniteSampleDependence.Dev.Irred.irreducible_aux hn h.symm

end FiniteSampleDependence.Rigidity
end

theorem solution : type_of% @FiniteSampleDependence.Rigidity.chk_generic_determinant_irreducible := @FiniteSampleDependence.Rigidity.chk_generic_determinant_irreducible
