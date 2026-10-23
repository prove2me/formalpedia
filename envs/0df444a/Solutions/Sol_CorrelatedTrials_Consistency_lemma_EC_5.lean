-- Prove2me | solution 1 for CorrelatedTrials.Consistency.lemma_EC_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T06:13:19.807337+00:00
-- url     : https://prove2.me/submissions/a00109bf-c98c-48fa-a900-f62168e7663a

import Mathlib
import Definitions.Def_CorrelatedTrials_Consistency_CpdeProcess
import Theorems.Thm_CorrelatedTrials_Consistency_lemma_EC_1
import Theorems.Thm_CorrelatedTrials_Consistency_lemma_EC_3

open MeasureTheory ProbabilityTheory Filter Topology CorrelatedTrials.Consistency

namespace CtMat
open Matrix

variable {M : ℕ}

noncomputable def Step (lam : Fin M → ℝ) (S : Matrix (Fin M) (Fin M) ℝ) (u : Fin M) :
    Matrix (Fin M) (Fin M) ℝ :=
  Matrix.of fun j k => S j k - S j u * S u k / (lam u + S u u)

noncomputable def bf (S : Matrix (Fin M) (Fin M) ℝ) (x y : Fin M → ℝ) : ℝ := x ⬝ᵥ (S *ᵥ y)

lemma bf_symm {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.IsHermitian) (x y : Fin M → ℝ) :
    bf S x y = bf S y x := by
  unfold bf
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  have : S.transpose = S := by simpa using hS.eq
  rw [this]

lemma bf_nonneg {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.PosDef) (x : Fin M → ℝ) : 0 ≤ bf S x x := by
  have := hS.posSemidef.dotProduct_mulVec_nonneg x
  simpa [bf] using this

lemma bf_cs {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.PosDef) (x y : Fin M → ℝ) :
    (bf S x y) ^ 2 ≤ bf S x x * bf S y y := by
  have hq : ∀ t : ℝ, 0 ≤ bf S y y * (t * t) + (2 * bf S x y) * t + bf S x x := by
    intro t
    have h := bf_nonneg hS (x + t • y)
    have e : bf S (x + t • y) (x + t • y) =
        bf S y y * (t * t) + (2 * bf S x y) * t + bf S x x := by
      have hs := bf_symm hS.1 y x
      simp only [bf, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, smul_dotProduct,
        dotProduct_smul, smul_eq_mul] at hs ⊢
      rw [hs]; ring
    rw [← e]; exact h
  have := discrim_le_zero hq
  unfold discrim at this
  nlinarith


lemma bf_single {S : Matrix (Fin M) (Fin M) ℝ} (x : Fin M → ℝ) (u : Fin M) :
    bf S x (Pi.single u 1) = ∑ j, x j * S j u := by
  simp [bf, dotProduct, mulVec, Pi.single_apply]

lemma bf_step {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.IsHermitian) (lam : Fin M → ℝ) (u : Fin M)
    (x : Fin M → ℝ) :
    bf (Step lam S u) x x = bf S x x - (∑ j, x j * S j u) ^ 2 / (lam u + S u u) := by
  have hsym : ∀ a b, S a b = S b a := fun a b => by
    have := hS.apply b a
    simpa using this
  have h1 : ∀ k, S u k = S k u := fun k => hsym u k
  unfold bf Step
  simp only [dotProduct, mulVec, Matrix.of_apply]
  simp only [sub_mul, Finset.sum_sub_distrib, mul_sub]
  congr 1
  simp only [h1]
  rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring


lemma sym_of {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.IsHermitian) (a b : Fin M) : S a b = S b a := by
  have := hS.apply b a
  simpa using this

lemma step_posDef {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.PosDef) (lam : Fin M → ℝ) (u : Fin M)
    (hu : 0 < lam u) : (Step lam S u).PosDef := by
  have hsym := sym_of hS.1
  have hSuu : 0 < S u u := hS.diag_pos
  have hD : 0 < lam u + S u u := by linarith
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · refine Matrix.IsHermitian.ext ?_
    intro i j
    simp only [Step, Matrix.of_apply, star_trivial]
    rw [hsym j i, hsym u j, hsym i u]
    ring
  · intro x hx
    have hpos := hS.dotProduct_mulVec_pos hx
    have hcs := bf_cs hS x (Pi.single u 1)
    rw [bf_single] at hcs
    have hee : bf S (Pi.single u 1) (Pi.single u 1) = S u u := by
      simp [bf, dotProduct, mulVec, Pi.single_apply]
    rw [hee] at hcs
    have hQ : 0 < bf S x x := by simpa [bf] using hpos
    have := bf_step hS.1 lam u x
    simp only [star_trivial]
    show 0 < bf (Step lam S u) x x
    rw [this]
    rw [sub_pos, div_lt_iff₀ hD]
    nlinarith [hcs, hQ, hu, hSuu]

lemma step_diag_le {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.PosDef) (lam : Fin M → ℝ) (u : Fin M)
    (hu : 0 < lam u) (j : Fin M) : Step lam S u j j ≤ S j j := by
  have hSuu : 0 < S u u := hS.diag_pos
  have hD : 0 < lam u + S u u := by linarith
  simp only [Step, Matrix.of_apply]
  rw [sym_of hS.1 u j, ← sq]
  have : 0 ≤ S j u ^ 2 / (lam u + S u u) := by positivity
  rw [sym_of hS.1 j u] at this ⊢
  linarith [this]

lemma step_diag_self {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.PosDef) (lam : Fin M → ℝ) (u : Fin M)
    (hu : 0 < lam u) :
    1 / Step lam S u u u = 1 / S u u + 1 / lam u := by
  have hSuu : 0 < S u u := hS.diag_pos
  have hD : 0 < lam u + S u u := by linarith
  simp only [Step, Matrix.of_apply]
  have h1 := hu.ne'
  have h2 := hSuu.ne'
  have h3 := hD.ne'
  have e : S u u - S u u * S u u / (lam u + S u u) = S u u * lam u / (lam u + S u u) := by
    field_simp; ring
  rw [e, one_div_div]
  field_simp

lemma step_cs {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.PosDef) (i j : Fin M) :
    (S i j) ^ 2 ≤ S i i * S j j := by
  have := bf_cs hS (Pi.single i 1) (Pi.single j 1)
  simpa [bf, dotProduct, mulVec, Pi.single_apply] using this

end CtMat

namespace CtSeq

variable {M : ℕ} (I : Instance M)

lemma sig_succ (t : ℕ) (ω : TrialSpace M) :
    Sig I (t + 1) ω = CtMat.Step I.lam (Sig I t ω) (alloc I t ω) := by
  simp only [Sig, cpdeState, alloc, update, CtMat.Step]

lemma sig_posDef (t : ℕ) (ω : TrialSpace M) : (Sig I t ω).PosDef := by
  induction t with
  | zero => exact I.posDef
  | succ t ih =>
    rw [sig_succ]
    exact CtMat.step_posDef ih _ _ (I.lam_pos _)

end CtSeq

theorem solution {M : ℕ} (I : Instance M) :
    ∀ᵐ ω ∂(trialMeasure I),
      (∀ i, ∀ ε > 0, ∃ᶠ T in atTop, nuStar I.lam I.c (mu I T ω) (Sig I T ω) i < -1 + ε) →
        ∀ i, Tendsto (fun T => Sig I T ω i i) atTop (𝓝 0) := by
  filter_upwards [lemma_EC_3 I] with ω hω h
  apply hω
  intro i ε hε
  refine (h i ε hε).mono fun T hT => lt_of_le_of_lt ?_ hT
  exact lemma_EC_1 I.lam I.c (mu I T ω) (Sig I T ω) i (CtSeq.sig_posDef I T ω) I.lam_pos I.c_pos
