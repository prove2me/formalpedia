-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.Supplement.theorem_14_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:35:52.729333+00:00
-- url     : https://prove2.me/submissions/4729c1cb-6579-41cd-a4b6-1a324b30b6d7

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_IsSpectralModel

open Matrix MeasureTheory

open ConjGrad
open ConjGrad.ErrorDecrease
open ConjGrad.ErrorDecrease.Supplement

/-- Theorem 14:3 (Hestenes–Stiefel 1952, p. 429): for a positive definite symmetric `A` and a
vector `r₀` not perpendicular to any eigenvector of `A`, and for every `l` exceeding all
eigenvalues of `A`, there is a mass distribution on `[0, l]` related to `A` and `r₀` as in §14. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (r₀ : Fin n → ℝ)
    (hcyc : ∀ (v : Fin n → ℝ) (c : ℝ), v ≠ 0 → A *ᵥ v = c • v → r₀ ⬝ᵥ v ≠ 0)
    (l : ℝ) (hl : ∀ j, hA.1.eigenvalues j < l) :
    ∃ (lam α : Fin n → ℝ) (e : Fin n → Fin n → ℝ),
      StrictMono lam ∧ (∀ j, 0 < lam j ∧ lam j < l ∧ α j ≠ 0) ∧
      (∀ i j, e i ⬝ᵥ e j = if i = j then 1 else 0) ∧
      (∀ j, A *ᵥ e j = lam j • e j) ∧ r₀ = ∑ j, α j • e j ∧
      IsSpectralModel (∑ j, ENNReal.ofReal (α j ^ 2) • Measure.dirac (lam j)) l A r₀ := by
        classical
        set B := hA.1.eigenvectorBasis with hB
        set b : Fin n → Fin n → ℝ := fun i => WithLp.ofLp (B i) with hb
        have ob : ∀ i j, b i ⬝ᵥ b j = if i = j then 1 else 0 := by
          intro i j
          have := orthonormal_iff_ite.mp B.orthonormal i j
          rw [EuclideanSpace.inner_eq_star_dotProduct] at this
          simpa [b, dotProduct_comm] using this
        have eig : ∀ j, A *ᵥ b j = hA.1.eigenvalues j • b j := fun j => hA.1.mulVec_eigenvectorBasis j
        have bne : ∀ j, b j ≠ 0 := by
          intro j h; have := ob j j; simp [h] at this
        have inj : Function.Injective hA.1.eigenvalues := by
          intro i j hij
          by_contra hne
          by_cases hi : r₀ ⬝ᵥ b i = 0
          · exact hcyc (b i) _ (bne i) (eig i) hi
          · have hv : (r₀ ⬝ᵥ b j) • b i - (r₀ ⬝ᵥ b i) • b j ≠ 0 := by
              intro h0
              have := congrArg (fun x => x ⬝ᵥ b j) h0
              simp [sub_dotProduct, ob, hne] at this
              exact hi this
            apply hcyc _ (hA.1.eigenvalues i) hv
            · rw [mulVec_sub, mulVec_smul, mulVec_smul, eig, eig, ← hij, smul_sub,
                smul_comm (hA.1.eigenvalues i) (r₀ ⬝ᵥ b j), smul_comm (hA.1.eigenvalues i) (r₀ ⬝ᵥ b i)]
            · simp [dotProduct_sub, dotProduct_smul, mul_comm]
        have expand : r₀ = ∑ i, (r₀ ⬝ᵥ b i) • b i := by
          have h := B.sum_repr' (WithLp.toLp 2 r₀)
          have h2 := congrArg WithLp.ofLp h
          simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, EuclideanSpace.inner_eq_star_dotProduct] at h2
          simpa [b, dotProduct_comm] using h2.symm
        set σ := Tuple.sort hA.1.eigenvalues
        have hsm : StrictMono (fun j => hA.1.eigenvalues (σ j)) :=
          (Tuple.monotone_sort _).strictMono_of_injective (inj.comp σ.injective)
        have hpos : ∀ j, 0 < hA.1.eigenvalues (σ j) ∧ hA.1.eigenvalues (σ j) < l ∧
            r₀ ⬝ᵥ b (σ j) ≠ 0 :=
          fun j => ⟨hA.eigenvalues_pos _, hl _, hcyc _ _ (bne _) (eig _)⟩
        have horth : ∀ i j, b (σ i) ⬝ᵥ b (σ j) = if i = j then 1 else 0 := by
          intro i j; rw [ob]; simp [σ.injective.eq_iff]
        have hexp : r₀ = ∑ j, (r₀ ⬝ᵥ b (σ j)) • b (σ j) := by
          rw [Equiv.sum_comp σ (fun i => (r₀ ⬝ᵥ b i) • b i)]; exact expand
        refine ⟨fun j => hA.1.eigenvalues (σ j), fun j => r₀ ⬝ᵥ b (σ j), fun j => b (σ j),
          hsm, hpos, horth, fun j => eig (σ j), hexp, ?_⟩
        refine ⟨?_, ?_, ?_⟩
        · refine ⟨?_⟩
          simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
            smul_eq_mul, mul_one]
          exact ENNReal.sum_lt_top.mpr fun j _ => ENNReal.ofReal_lt_top
        · simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
          refine Finset.sum_eq_zero fun j _ => ?_
          rw [Measure.dirac_apply' _ measurableSet_Icc.compl]
          have : hA.1.eigenvalues (σ j) ∈ Set.Icc 0 l := ⟨(hpos j).1.le, (hpos j).2.1.le⟩
          simp [this]
        · refine ⟨fun j => hA.1.eigenvalues (σ j), fun j => (r₀ ⬝ᵥ b (σ j)) ^ 2,
            fun j => r₀ ⬝ᵥ b (σ j), fun j => b (σ j), ⟨hsm, ?_⟩, fun j => by have := (hpos j).2.2; positivity, horth,
            fun j => eig (σ j), hexp, fun j => rfl⟩
          · intro g _
            have hint : ∀ j ∈ Finset.univ, Integrable (fun t => g.eval t)
                (ENNReal.ofReal ((r₀ ⬝ᵥ b (σ j)) ^ 2) • Measure.dirac (hA.1.eigenvalues (σ j))) :=
              fun j _ => (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
            refine ⟨integrable_finsetSum_measure.mpr hint, ?_⟩
            rw [integral_finsetSum_measure hint]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
