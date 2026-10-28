-- Prove2me | solution 2 for DRJointCC.Individual.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T05:36:15.541278+00:00
-- url     : https://prove2.me/submissions/72cf2c59-151b-4dbd-a55a-cca2083fb97c

import Mathlib
import Definitions.Def_DRJointCC_Individual_Individual
import Theorems.Thm_SLemma_exists_multiplier_of_quadratic_along_lines
import Theorems.Thm_SLemma_concave_convex
import Theorems.Thm_MomentProblem_exists_dual_of_slater
import Theorems.Thm_Matrix_PosSemidef_exists_eq_sum_vecMulVec

-- carved verbatim out of submission 351d29f4-df20-4118-a8bc-25a1b62a5233, lines 4112-4146

section
open MeasureTheory
open scoped ENNReal
open MeasureTheory Matrix

namespace MomentKit

def HasSecondMoments {m : ℕ} (P : Measure (Fin m → ℝ)) : Prop :=
  IsProbabilityMeasure P ∧ ∀ i : Fin m, MemLp (fun ξ : Fin m → ℝ => ξ i) 2 P

end MomentKit

end

section
open MeasureTheory
open scoped ENNReal
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

private def aux2_Q {n : Type*} [Fintype n] (A : Matrix n n ℝ) (b : n → ℝ) (c : ℝ)
    (p : (n → ℝ) × ℝ) : ℝ :=
  p.1 ⬝ᵥ A *ᵥ p.1 + 2 * p.2 * (b ⬝ᵥ p.1) + c * p.2 ^ 2

private lemma aux2_qexp {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x y : n → ℝ) (s : ℝ) :
    (x + s • y) ⬝ᵥ A *ᵥ (x + s • y) =
      x ⬝ᵥ A *ᵥ x + s * (x ⬝ᵥ A *ᵥ y + y ⬝ᵥ A *ᵥ x) + s ^ 2 * (y ⬝ᵥ A *ᵥ y) := by
  simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  ring

private lemma aux2_Q_exp {n : Type*} [Fintype n] (A : Matrix n n ℝ) (b : n → ℝ) (c : ℝ)
    (p q : (n → ℝ) × ℝ) (s : ℝ) :
    aux2_Q A b c (p + s • q) = aux2_Q A b c p + s * (p.1 ⬝ᵥ A *ᵥ q.1 + q.1 ⬝ᵥ A *ᵥ p.1 +
      2 * (p.2 * (b ⬝ᵥ q.1) + q.2 * (b ⬝ᵥ p.1)) + 2 * c * p.2 * q.2) + s ^ 2 * aux2_Q A b c q := by
  simp only [aux2_Q, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [aux2_qexp]
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  ring

private lemma aux2_Q_one {n : Type*} [Fintype n] (A : Matrix n n ℝ) (b : n → ℝ) (c : ℝ) (x : n → ℝ) :
    aux2_Q A b c (x, 1) = x ⬝ᵥ A *ᵥ x + 2 * b ⬝ᵥ x + c := by
  simp only [aux2_Q]; ring

private lemma aux2_qf_smul {n : Type*} [Fintype n] (A : Matrix n n ℝ) (c : ℝ) (v : n → ℝ) :
    (c • v) ⬝ᵥ A *ᵥ (c • v) = c ^ 2 * (v ⬝ᵥ A *ᵥ v) := by
  simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring

private lemma aux2_Q_scale {n : Type*} [Fintype n] (A : Matrix n n ℝ) (b : n → ℝ) (c : ℝ)
    (u : n → ℝ) (t : ℝ) : aux2_Q A b c (t • u, t) = t ^ 2 * aux2_Q A b c (u, 1) := by
  simp only [aux2_Q, aux2_qf_smul, dotProduct_smul, smul_eq_mul]; ring

private lemma aux2_big (f₀ k q : ℝ) (hq : q < 0) : ∃ S : ℝ, 0 ≤ S ∧ f₀ + S * k + S ^ 2 * q < 0 := by
  set M := |f₀| + |k| + 1 with hM
  have hM0 : 0 < M := by positivity
  refine ⟨M / (-q) + 1, ?_⟩
  set S := M / (-q) + 1 with hS
  have hS1 : 1 ≤ S := by have : 0 ≤ M / (-q) := div_nonneg hM0.le (by linarith); linarith
  have hSq : S * q = -M + q := by
    rw [hS, add_mul, div_mul_eq_mul_div, one_mul]
    rw [div_neg, mul_div_assoc, div_self hq.ne, mul_one]
  have h1 : f₀ ≤ S * |f₀| := by nlinarith [le_abs_self f₀, abs_nonneg f₀]
  have h2 : S * k ≤ S * |k| := by nlinarith [le_abs_self k]
  have h3 : S ^ 2 * q = S * (-M + q) := by rw [← hSq]; ring
  refine ⟨by linarith, ?_⟩
  nlinarith

private lemma aux2_dot_self_nonneg {n : Type*} [Fintype n] (v : n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

private lemma aux2_dot_self_pos {n : Type*} [Fintype n] {v : n → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v :=
  lt_of_le_of_ne (aux2_dot_self_nonneg v) (Ne.symm (mt dotProduct_self_eq_zero.1 hv))

private lemma aux2_normalize {n : Type*} [Fintype n] {v : n → ℝ} (hv : v ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ (c • v) ⬝ᵥ (c • v) = 1 := by
  have hpos := aux2_dot_self_pos hv
  have hs : 0 < Real.sqrt (v ⬝ᵥ v) := Real.sqrt_pos.2 hpos
  have hs2 : Real.sqrt (v ⬝ᵥ v) ^ 2 = v ⬝ᵥ v := Real.sq_sqrt hpos.le
  refine ⟨(Real.sqrt (v ⬝ᵥ v))⁻¹, inv_pos.2 hs, ?_⟩
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  field_simp
  linarith [hs2]

private def aux2_sph (n : Type*) [Fintype n] : Set (n → ℝ) := {v | v ⬝ᵥ v = 1}

private lemma aux2_sph_compact (n : Type*) [Fintype n] : IsCompact (aux2_sph n) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (continuous_id.dotProduct continuous_id) continuous_const
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun v hv => ?_⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : v i * v i ≤ v ⬝ᵥ v :=
      Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg (v j))
        (Finset.mem_univ i)
    have h2 : v ⬝ᵥ v = 1 := hv
    rw [Real.norm_eq_abs]
    nlinarith [abs_mul_abs_self (v i), abs_nonneg (v i)]

private lemma aux2_sph_ne {n : Type*} [Fintype n] {v : n → ℝ} (hv : v ∈ aux2_sph n) : v ≠ 0 := by
  rintro rfl; simp [aux2_sph] at hv

private lemma aux2_t0 {V : Type*} [AddCommGroup V] [Module ℝ V] (Q₁ Q₂ : V → ℝ) (P d : V)
    (h1 : ∃ k, ∀ s : ℝ, Q₁ (P + s • d) = Q₁ P + s * k + s ^ 2 * Q₁ d)
    (h2 : ∃ k, ∀ s : ℝ, Q₂ (P + s • d) = Q₂ P + s * k + s ^ 2 * Q₂ d)
    (hP : Q₂ P < 0) (hd : Q₂ d ≤ 0) (H : ∀ s : ℝ, Q₂ (P + s • d) ≤ 0 → 0 ≤ Q₁ (P + s • d)) :
    0 ≤ Q₁ d := by
  obtain ⟨k₁, hk₁⟩ := h1
  obtain ⟨k₂, hk₂⟩ := h2
  by_contra hneg
  push Not at hneg
  have key : ∀ s : ℝ, s * k₂ ≤ 0 → 0 ≤ Q₁ P + s * k₁ + s ^ 2 * Q₁ d := by
    intro s hs
    rw [← hk₁]
    apply H
    rw [hk₂]
    nlinarith [sq_nonneg s]
  rcases le_total k₂ 0 with hk | hk
  · obtain ⟨S, hS0, hS⟩ := aux2_big (Q₁ P) k₁ (Q₁ d) hneg
    linarith [key S (mul_nonpos_of_nonneg_of_nonpos hS0 hk)]
  · obtain ⟨S, hS0, hS⟩ := aux2_big (Q₁ P) (-k₁) (Q₁ d) hneg
    have := key (-S) (by nlinarith)
    nlinarith

end

section
open MeasureTheory
open scoped ENNReal
open MeasureTheory Matrix

namespace MomentKit

def lift {k : ℕ} (ξ : Fin k → ℝ) : Fin k ⊕ Unit → ℝ := Sum.elim ξ (fun _ => 1)

end MomentKit

namespace MomentKit

theorem aux_atoms_entry {k : ℕ} (c : ℝ) (hc : 0 < c) (m : Fin k → ℝ) (s : Fin k → Fin k → ℝ)
    (a b : Fin k ⊕ Unit) :
    c / (k + 1) * (lift m a * lift m b) +
      ∑ i : Fin k, (c / (2 * (k + 1)) * ((lift m a + √((k + 1) / c) * Sum.elim (s i) 0 a) *
          (lift m b + √((k + 1) / c) * Sum.elim (s i) 0 b)) +
        c / (2 * (k + 1)) * ((lift m a + -√((k + 1) / c) * Sum.elim (s i) 0 a) *
          (lift m b + -√((k + 1) / c) * Sum.elim (s i) 0 b))) =
    c * (lift m a * lift m b) + ∑ i : Fin k, Sum.elim (s i) 0 a * Sum.elim (s i) 0 b := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hr : √((k + 1) / c) * √((k + 1) / c) = (k + 1) / c :=
    Real.mul_self_sqrt (div_nonneg hk.le hc.le)
  have e : ∀ i : Fin k, c / (2 * (k + 1)) * ((lift m a + √((k + 1) / c) * Sum.elim (s i) 0 a) *
          (lift m b + √((k + 1) / c) * Sum.elim (s i) 0 b)) +
        c / (2 * (k + 1)) * ((lift m a + -√((k + 1) / c) * Sum.elim (s i) 0 a) *
          (lift m b + -√((k + 1) / c) * Sum.elim (s i) 0 b)) =
      c / (k + 1) * (lift m a * lift m b) + Sum.elim (s i) 0 a * Sum.elim (s i) 0 b := by
    intro i
    have : c / (2 * (k + 1)) * (2 * (√((k + 1) / c) * √((k + 1) / c))) = 1 := by
      rw [hr]; field_simp
    have h2 : c / (2 * (k + 1)) * 2 = c / (k + 1) := by field_simp
    linear_combination (Sum.elim (s i) 0 a * Sum.elim (s i) 0 b) * this +
      (lift m a * lift m b) * h2
  rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

end MomentKit

namespace MomentKit

theorem aux_lift_add_smul {k : ℕ} (m d : Fin k → ℝ) (t : ℝ) :
    lift (m + t • d) = lift m + t • Sum.elim d 0 := by
  funext i
  cases i with
  | inl i => simp [lift]
  | inr u => simp [lift]

end MomentKit

namespace MomentKit

theorem aux_atoms {k : ℕ} (c : ℝ) (hc : 0 < c) (m : Fin k → ℝ) (s : Fin k → Fin k → ℝ) :
    ∃ (N : ℕ) (w : Fin N → ℝ) (ξ : Fin N → Fin k → ℝ), (∀ j, 0 ≤ w j) ∧
      ∑ j, w j • Matrix.vecMulVec (lift (ξ j)) (lift (ξ j)) =
        c • Matrix.vecMulVec (lift m) (lift m) +
          ∑ i, Matrix.vecMulVec (Sum.elim (s i) 0) (Sum.elim (s i) 0) := by
  classical
  let J := Option (Fin k × Bool)
  let r : ℝ := √((k + 1) / c)
  let W : J → ℝ := fun o => o.elim (c / (k + 1)) (fun _ => c / (2 * (k + 1)))
  let Ξ : J → Fin k → ℝ := fun o => o.elim m (fun p => m + (if p.2 then r else -r) • s p.1)
  have hW : ∀ o, 0 ≤ W o := by
    intro o; cases o <;> simp only [W, Option.elim] <;> positivity
  have key : ∑ o, W o • Matrix.vecMulVec (lift (Ξ o)) (lift (Ξ o)) =
      c • Matrix.vecMulVec (lift m) (lift m) +
        ∑ i, Matrix.vecMulVec (Sum.elim (s i) 0) (Sum.elim (s i) 0) := by
    ext a b
    rw [Matrix.sum_apply, Fintype.sum_option, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, W, Ξ, Option.elim, if_true, Bool.false_eq_true, if_false,
      aux_lift_add_smul, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sum_apply, Matrix.vecMulVec_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
    exact aux_atoms_entry c hc m s a b
  let e := Fintype.equivFin J
  refine ⟨Fintype.card J, fun j => W (e.symm j), fun j => Ξ (e.symm j), fun j => hW _, ?_⟩
  rw [← key]
  exact Equiv.sum_comp e.symm (fun o => W o • Matrix.vecMulVec (lift (Ξ o)) (lift (Ξ o)))

end MomentKit

namespace MomentKit

noncomputable def meanVec {m : ℕ} (P : Measure (Fin m → ℝ)) : Fin m → ℝ :=
  fun i => ∫ ξ, ξ i ∂P

end MomentKit

namespace MomentKit

noncomputable def covMat {m : ℕ} (P : Measure (Fin m → ℝ)) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => ∫ ξ, (ξ i - meanVec P i) * (ξ j - meanVec P j) ∂P

end MomentKit

namespace MomentKit

theorem aux_covMat_symm {k : ℕ} (P : Measure (Fin k → ℝ)) (i j : Fin k) :
    covMat P i j = covMat P j i := by
  simp only [covMat, Matrix.of_apply, mul_comm]

end MomentKit

namespace MomentKit

theorem aux_quad_elim {k : ℕ} (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) (x : Fin k → ℝ) (t : ℝ) :
    Sum.elim x (fun _ => t) ⬝ᵥ M *ᵥ Sum.elim x (fun _ => t) = x ⬝ᵥ M.toBlocks₁₁ *ᵥ x +
      t * (2 * ((fun i => (M (Sum.inl i) (Sum.inr ()) + M (Sum.inr ()) (Sum.inl i)) / 2) ⬝ᵥ x)) +
      t * t * M (Sum.inr ()) (Sum.inr ()) := by
  simp only [dotProduct, mulVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, toBlocks₁₁,
    of_apply, Finset.univ_unique, Finset.sum_singleton, Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  ring_nf
  rw [Finset.sum_add_distrib]
  simp only [show (default : Unit) = () from rfl]
  rw [show ∑ i, t * x i * M (Sum.inl i) (Sum.inr ()) = ∑ i, t * M (Sum.inl i) (Sum.inr ()) * x i from
    Finset.sum_congr rfl fun i _ => by ring]
  ring

end MomentKit

namespace MomentKit

noncomputable def discrete {X : Type*} [MeasurableSpace X] {N : ℕ} (w : Fin N → ℝ)
    (x : Fin N → X) : Measure X :=
  ∑ j, ENNReal.ofReal (w j) • Measure.dirac (x j)

end MomentKit

namespace MomentKit

theorem aux_discrete_of_psd {k : ℕ} {M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ}
    (hsym : ∀ a b, M a b = M b a) (hpsd : ∀ v, 0 ≤ v ⬝ᵥ M *ᵥ v)
    (hc0 : 0 < M (Sum.inr ()) (Sum.inr ())) :
    ∃ (N : ℕ) (w : Fin N → ℝ) (ξ : Fin N → Fin k → ℝ), (∀ j, 0 ≤ w j) ∧
      ∑ j, w j • Matrix.vecMulVec (lift (ξ j)) (lift (ξ j)) = M := by
  classical
  set c := M (Sum.inr ()) (Sum.inr ()) with hcdef
  have hc : 0 < c := hc0
  let b : Fin k → ℝ := fun i => M (Sum.inl i) (Sum.inr ())
  let S' : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => M (Sum.inl i) (Sum.inl j) - b i * b j / c
  have hquad : ∀ x : Fin k → ℝ, 0 ≤ x ⬝ᵥ S' *ᵥ x := by
    intro x
    have h1 := hpsd (Sum.elim x (fun _ => -(b ⬝ᵥ x) / c))
    rw [aux_quad_elim] at h1
    have hb : (fun i => (M (Sum.inl i) (Sum.inr ()) + M (Sum.inr ()) (Sum.inl i)) / 2) = b := by
      funext i; simp only [b]; rw [hsym (Sum.inr ()) (Sum.inl i)]; ring
    rw [hb] at h1
    have hS : x ⬝ᵥ S' *ᵥ x = x ⬝ᵥ M.toBlocks₁₁ *ᵥ x - (b ⬝ᵥ x) * (b ⬝ᵥ x) / c := by
      have e1 : (b ⬝ᵥ x) * (b ⬝ᵥ x) / c = ∑ i, ∑ j, x i * (b i * b j / c * x j) := by
        simp only [dotProduct]
        rw [Finset.sum_mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      have e2 : x ⬝ᵥ M.toBlocks₁₁ *ᵥ x = ∑ i, ∑ j, x i * (M (Sum.inl i) (Sum.inl j) * x j) := by
        simp only [dotProduct, mulVec, Finset.mul_sum]; rfl
      have e3 : x ⬝ᵥ S' *ᵥ x = ∑ i, ∑ j, x i * ((M (Sum.inl i) (Sum.inl j) - b i * b j / c) * x j) := by
        simp only [dotProduct, mulVec, Finset.mul_sum]; rfl
      rw [e1, e2, e3, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hS]
    have hc0 : c ≠ 0 := hc.ne'
    have : x ⬝ᵥ M.toBlocks₁₁ *ᵥ x + -(b ⬝ᵥ x) / c * (2 * (b ⬝ᵥ x)) +
        -(b ⬝ᵥ x) / c * (-(b ⬝ᵥ x) / c) * c =
        x ⬝ᵥ M.toBlocks₁₁ *ᵥ x - (b ⬝ᵥ x) * (b ⬝ᵥ x) / c := by
      field_simp; ring
    linarith
  have hPSD : S'.PosSemidef := by
    rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => by simpa using hquad x⟩
    ext i j
    simp only [S', conjTranspose_apply, Matrix.of_apply, star_trivial]
    rw [hsym (Sum.inl i) (Sum.inl j)]; ring
  obtain ⟨s, hs⟩ := Matrix.PosSemidef.exists_eq_sum_vecMulVec hPSD
  obtain ⟨N, w, ξ, hw, hsum⟩ := aux_atoms c hc (fun i => b i / c) s
  refine ⟨N, w, ξ, hw, ?_⟩
  rw [hsum]
  ext a a'
  have hS' : ∀ i j, ∑ l, s l i * s l j = M (Sum.inl i) (Sum.inl j) - b i * b j / c := by
    intro i j
    have := congrFun (congrFun hs i) j
    simp only [S', Matrix.of_apply, Matrix.sum_apply, Matrix.vecMulVec_apply] at this
    exact this.symm
  cases a with
  | inl i =>
    cases a' with
    | inl j =>
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
        smul_eq_mul, lift, Sum.elim_inl]
      rw [hS' i j]; field_simp; ring
    | inr u =>
      cases u
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
        smul_eq_mul, lift, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero,
        Finset.sum_const_zero, add_zero, mul_one]
      field_simp
      rfl
  | inr u =>
    cases u
    cases a' with
    | inl j =>
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
        smul_eq_mul, lift, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_mul,
        Finset.sum_const_zero, add_zero, one_mul]
      rw [hsym]; field_simp; rfl
    | inr v =>
      cases v
      simp [lift, Matrix.sum_apply, Matrix.vecMulVec_apply, c]

end MomentKit

namespace MomentKit

def momentMatrix {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) :
    Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ :=
  Matrix.fromBlocks (Sig + Matrix.vecMulVec μ μ) (fun i _ => μ i) (fun _ j => μ j) (fun _ _ => 1)

end MomentKit

namespace MomentKit

def frob {ι : Type*} [Fintype ι] (X Y : Matrix ι ι ℝ) : ℝ := Matrix.trace (X * Y)

end MomentKit

namespace MomentKit

theorem aux_frob_eq {k : ℕ} {Ω : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ}
    (hΩ : ∀ a b, Ω a b = Ω b a) (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) :
    frob Ω M = ∑ a, ∑ b, M a b * Ω a b := by
  simp only [frob, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hΩ]; ring

end MomentKit

namespace MomentKit

theorem aux_integrable_discrete {k N : ℕ} (w : Fin N → ℝ) (x : Fin N → Fin k → ℝ)
    (f : (Fin k → ℝ) → ℝ) : Integrable f (discrete w x) := by
  unfold discrete
  refine integrable_finsetSum_measure.2 fun j _ => ?_
  exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

end MomentKit

namespace MomentKit

theorem aux_integral_centered {k : ℕ} (P : Measure (Fin k → ℝ)) [IsProbabilityMeasure P]
    (i j : Fin k) (a b : ℝ) (hi : Integrable (fun ξ : Fin k → ℝ => ξ i) P)
    (hj : Integrable (fun ξ : Fin k → ℝ => ξ j) P)
    (hij : Integrable (fun ξ : Fin k → ℝ => ξ i * ξ j) P) :
    ∫ ξ, (ξ i - a) * (ξ j - b) ∂P =
      ∫ ξ, ξ i * ξ j ∂P - a * ∫ ξ, ξ j ∂P - b * ∫ ξ, ξ i ∂P + a * b := by
  have e : (fun ξ : Fin k → ℝ => (ξ i - a) * (ξ j - b)) =
      fun ξ => ((ξ i * ξ j - a * ξ j) - b * ξ i) + a * b := by
    funext ξ; ring
  have h1 : Integrable (fun ξ : Fin k → ℝ => ξ i * ξ j - a * ξ j) P := hij.sub (hj.const_mul a)
  have h2 : Integrable (fun ξ : Fin k → ℝ => ξ i * ξ j - a * ξ j - b * ξ i) P :=
    h1.sub (hi.const_mul b)
  rw [e, integral_add h2 (integrable_const _), integral_sub h1 (hi.const_mul b),
    integral_sub hij (hj.const_mul a), integral_const_mul, integral_const_mul, integral_const]
  simp

end MomentKit

namespace MomentKit

theorem aux_integral_discrete {k N : ℕ} (w : Fin N → ℝ) (x : Fin N → Fin k → ℝ)
    (hw : ∀ j, 0 ≤ w j) (f : (Fin k → ℝ) → ℝ) :
    ∫ ξ, f ξ ∂(discrete w x) = ∑ j, w j * f (x j) := by
  unfold discrete
  rw [integral_finsetSum_measure fun j _ =>
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw j), smul_eq_mul]

end MomentKit

namespace MomentKit

theorem aux_isFinite_discrete {k N : ℕ} (w : Fin N → ℝ) (x : Fin N → Fin k → ℝ) :
    IsFiniteMeasure (discrete w x) := by
  constructor
  simp only [discrete, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.2 fun j _ => ENNReal.ofReal_lt_top

end MomentKit

namespace MomentKit

def liftQuad {k : ℕ} (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) (ξ : Fin k → ℝ) : ℝ :=
  lift ξ ⬝ᵥ M.mulVec (lift ξ)

end MomentKit

namespace MomentKit

theorem aux_liftQuad_sum {k : ℕ} (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) (ξ : Fin k → ℝ) :
    liftQuad M ξ = ∑ a, ∑ b, M a b * (lift ξ a * lift ξ b) := by
  simp only [liftQuad, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end MomentKit

namespace MomentKit

theorem aux_lift_comb {k : ℕ} (ξ ζ : Fin k → ℝ) (a b : ℝ) (hab : a + b = 1) :
    lift (a • ξ + b • ζ) = a • lift ξ + b • lift ζ := by
  funext i
  cases i with
  | inl i => simp [lift]
  | inr u => simp [lift, hab]

end MomentKit

namespace MomentKit

theorem aux_lift_measurable {k : ℕ} (a : Fin k ⊕ Unit) : Measurable fun ξ : Fin k → ℝ => lift ξ a := by
  cases a with
  | inl i => exact measurable_pi_apply i
  | inr u => exact measurable_const

end MomentKit

namespace MomentKit

def momSet {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) :
    Set (Measure (Fin k → ℝ)) :=
  {P | HasSecondMoments P ∧ meanVec P = μ ∧ covMat P = Sig}

end MomentKit

namespace MomentKit

theorem aux_lift_memLp {k : ℕ} {μ : Fin k → ℝ} {Sig : Matrix (Fin k) (Fin k) ℝ}
    {P : Measure (Fin k → ℝ)} (hP : P ∈ momSet μ Sig) (a : Fin k ⊕ Unit) :
    MemLp (fun ξ => lift ξ a) 2 P := by
  have := hP.1.1
  cases a with
  | inl i => exact hP.1.2 i
  | inr u => exact memLp_const 1

end MomentKit

namespace MomentKit

theorem aux_lift_smul {k : ℕ} (d : Fin k → ℝ) (s : ℝ) :
    lift (s • d) = s • Sum.elim d 0 + (1 : ℝ) • lift 0 := by
  funext i
  cases i with
  | inl i => simp [lift]
  | inr u => simp [lift]

end MomentKit

namespace MomentKit

theorem aux_lift_sub {k : ℕ} (ξ ζ : Fin k → ℝ) :
    lift ξ - lift ζ = Sum.elim (ξ - ζ) 0 := by
  funext i
  cases i with
  | inl i => simp [lift]
  | inr u => simp [lift]

end MomentKit

namespace MomentKit

theorem aux_mm_ll {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (i j : Fin k) :
    momentMatrix μ Sig (Sum.inl i) (Sum.inl j) = Sig i j + μ i * μ j := rfl

end MomentKit

namespace MomentKit

theorem aux_mm_lr {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (i : Fin k) (u : Unit) :
    momentMatrix μ Sig (Sum.inl i) (Sum.inr u) = μ i := rfl

end MomentKit

namespace MomentKit

theorem aux_mm_rl {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (u : Unit) (j : Fin k) :
    momentMatrix μ Sig (Sum.inr u) (Sum.inl j) = μ j := rfl

end MomentKit

namespace MomentKit

theorem aux_mm_rr {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (u v : Unit) :
    momentMatrix μ Sig (Sum.inr u) (Sum.inr v) = 1 := rfl

end MomentKit

namespace MomentKit

theorem aux_mem_momSet_of_integral_eq {k : ℕ} {μ : Fin k → ℝ} {Sig : Matrix (Fin k) (Fin k) ℝ}
    (P : Measure (Fin k → ℝ)) [IsFiniteMeasure P]
    (hint : ∀ a b, Integrable (fun ξ => lift ξ a * lift ξ b) P)
    (hmom : ∀ a b, ∫ ξ, lift ξ a * lift ξ b ∂P = momentMatrix μ Sig a b) :
    P ∈ momSet μ Sig := by
  have h11 := hmom (Sum.inr ()) (Sum.inr ())
  simp only [lift, Sum.elim_inr, mul_one, integral_const, smul_eq_mul, aux_mm_rr] at h11
  have hprob : IsProbabilityMeasure P := by
    constructor
    rw [measureReal_def] at h11
    rw [← ENNReal.ofReal_toReal (measure_ne_top P Set.univ), h11, ENNReal.ofReal_one]
  have hI : ∀ i, Integrable (fun ξ : Fin k → ℝ => ξ i) P := fun i => by
    simpa [lift] using hint (Sum.inl i) (Sum.inr ())
  have hII : ∀ i j, Integrable (fun ξ : Fin k → ℝ => ξ i * ξ j) P := fun i j => by
    simpa [lift] using hint (Sum.inl i) (Sum.inl j)
  have hE1 : ∀ i, ∫ ξ, ξ i ∂P = μ i := fun i => by
    simpa [lift, aux_mm_lr, aux_mm_rl] using hmom (Sum.inl i) (Sum.inr ())
  have hE2 : ∀ i j, ∫ ξ, ξ i * ξ j ∂P = Sig i j + μ i * μ j := fun i j => by
    simpa [lift, aux_mm_ll] using hmom (Sum.inl i) (Sum.inl j)
  have hmean : meanVec P = μ := funext hE1
  refine ⟨⟨hprob, fun i => ?_⟩, hmean, ?_⟩
  · rw [memLp_two_iff_integrable_sq (continuous_apply i).aestronglyMeasurable]
    simpa [pow_two] using hII i i
  · ext i j
    simp only [covMat, Matrix.of_apply, hmean]
    rw [aux_integral_centered P i j _ _ (hI i) (hI j) (hII i j), hE2, hE1, hE1]
    ring

end MomentKit

namespace MomentKit

theorem aux_moment {k : ℕ} {μ : Fin k → ℝ} {Sig : Matrix (Fin k) (Fin k) ℝ}
    {P : Measure (Fin k → ℝ)} (hP : P ∈ momSet μ Sig) (a b : Fin k ⊕ Unit) :
    Integrable (fun ξ => lift ξ a * lift ξ b) P ∧
      ∫ ξ, lift ξ a * lift ξ b ∂P = momentMatrix μ Sig a b := by
  have := hP.1.1
  have hint : ∀ a b, Integrable (fun ξ => lift ξ a * lift ξ b) P := fun a b =>
    (aux_lift_memLp hP a).integrable_mul (aux_lift_memLp hP b)
  refine ⟨hint a b, ?_⟩
  have hI : ∀ i, Integrable (fun ξ : Fin k → ℝ => ξ i) P := fun i => by
    simpa [lift] using hint (Sum.inl i) (Sum.inr ())
  have hII : ∀ i j, Integrable (fun ξ : Fin k → ℝ => ξ i * ξ j) P := fun i j => by
    simpa [lift] using hint (Sum.inl i) (Sum.inl j)
  have hmean := hP.2.1
  have hE1 : ∀ i, ∫ ξ, ξ i ∂P = μ i := fun i => congrFun hmean i
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      have hc := congrFun (congrFun hP.2.2 i) j
      simp only [covMat, Matrix.of_apply, hmean] at hc
      rw [aux_integral_centered P i j _ _ (hI i) (hI j) (hII i j), hE1, hE1] at hc
      simp only [lift, Sum.elim_inl, aux_mm_ll]
      linarith
    | inr u => simpa [lift, aux_mm_lr, aux_mm_rl] using hE1 i
  | inr u =>
    cases b with
    | inl j => simpa [lift, aux_mm_lr, aux_mm_rl] using hE1 j
    | inr v => simp [lift, aux_mm_rr]

end MomentKit

namespace MomentKit

theorem aux_momentMatrix_symm {k : ℕ} {μ : Fin k → ℝ} {Sig : Matrix (Fin k) (Fin k) ℝ}
    (hS : ∀ i j, Sig i j = Sig j i) (a b : Fin k ⊕ Unit) :
    momentMatrix μ Sig a b = momentMatrix μ Sig b a := by
  cases a <;> cases b <;> simp [aux_mm_ll, aux_mm_lr, aux_mm_rl, aux_mm_rr, hS, mul_comm]

end MomentKit

namespace MomentKit

theorem aux_symm_of_posDef {n : Type*} [Fintype n] {M : Matrix n n ℝ} (hM : M.PosDef) (a b : n) :
    M a b = M b a := by
  have h := hM.isHermitian
  have := congrFun (congrFun h b) a
  simpa using this

end MomentKit

namespace MomentKit

theorem aux_momentMatrix_posDef {k : ℕ} (μ : Fin k → ℝ) {Sig : Matrix (Fin k) (Fin k) ℝ}
    (hSig : Sig.PosDef) : (momentMatrix μ Sig).PosDef := by
  have hSsym : ∀ i j, Sig i j = Sig j i := aux_symm_of_posDef hSig
  have hΩsym := aux_momentMatrix_symm (μ := μ) hSsym
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · ext a b
    simp only [conjTranspose_apply, star_trivial]
    exact hΩsym b a
  simp only [star_trivial]
  have hv' : v = Sum.elim (fun i => v (Sum.inl i)) (fun _ => v (Sum.inr ())) := by
    funext a; cases a with
    | inl i => rfl
    | inr u => cases u; rfl
  rw [hv', aux_quad_elim]
  set x : Fin k → ℝ := fun i => v (Sum.inl i)
  set t := v (Sum.inr ())
  have hb : (fun i => (momentMatrix μ Sig (Sum.inl i) (Sum.inr ()) +
      momentMatrix μ Sig (Sum.inr ()) (Sum.inl i)) / 2) = μ := by
    funext i; rw [aux_mm_lr, aux_mm_rl]; ring
  have h11 : (momentMatrix μ Sig).toBlocks₁₁ = Sig + vecMulVec μ μ := by
    ext i j; rfl
  have hq : x ⬝ᵥ (vecMulVec μ μ *ᵥ x) = (μ ⬝ᵥ x) * (μ ⬝ᵥ x) := by
    simp only [dotProduct, mulVec, vecMulVec_apply]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hb, h11, add_mulVec, dotProduct_add, hq, aux_mm_rr]
  have hS0 : 0 ≤ x ⬝ᵥ Sig *ᵥ x := by
    have h0 := hSig.posSemidef
    rw [posSemidef_iff_dotProduct_mulVec] at h0
    simpa using h0.2 x
  by_cases hx : x = 0
  · have ht : t ≠ 0 := by
      intro ht; apply hv
      rw [hv']; funext a; cases a with
      | inl i => exact congrFun hx i
      | inr u => exact ht
    rw [hx]
    simp only [dotProduct_zero, mulVec_zero, zero_add, mul_zero, zero_dotProduct]
    nlinarith [mul_self_pos.2 ht]
  · have hpos : 0 < x ⬝ᵥ Sig *ᵥ x := by
      have h0 := hSig
      rw [posDef_iff_dotProduct_mulVec] at h0
      simpa using h0.2 hx
    nlinarith [sq_nonneg (μ ⬝ᵥ x + t)]

end MomentKit

namespace MomentKit

theorem aux_qf_comb {n : Type*} [Fintype n] (M : Matrix n n ℝ) (x y : n → ℝ) (a b : ℝ) :
    (a • x + b • y) ⬝ᵥ M *ᵥ (a • x + b • y) = a * a * (x ⬝ᵥ M *ᵥ x) +
      a * b * (x ⬝ᵥ M *ᵥ y + y ⬝ᵥ M *ᵥ x) + b * b * (y ⬝ᵥ M *ᵥ y) := by
  simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  ring

end MomentKit

namespace MomentKit

theorem aux_quad_nonneg_lead {a b c : ℝ} (h : ∀ s : ℝ, 0 ≤ a * (s * s) + b * s + c) : 0 ≤ a := by
  by_contra ha
  push Not at ha
  set s : ℝ := (|b| + |c| + 1) / (-a) + 1 with hsdef
  have hpos : 0 < (|b| + |c| + 1) / (-a) := div_pos (by positivity) (by linarith)
  have hs1 : 1 ≤ s := by linarith
  have hs2 : a * s ≤ -(|b| + |c| + 1) := by
    have e : a * ((|b| + |c| + 1) / (-a)) = -(|b| + |c| + 1) := by
      have ha0 : a ≠ 0 := ha.ne
      field_simp
    have : a * s = -(|b| + |c| + 1) + a := by rw [hsdef, mul_add, e, mul_one]
    linarith
  have h3 : a * s + b ≤ -(|c| + 1) := by linarith [le_abs_self b]
  have h4 : s * (a * s + b) ≤ s * (-(|c| + 1)) := mul_le_mul_of_nonneg_left h3 (by linarith)
  have h5 := h s
  have h6 : s * (-(|c| + 1)) ≤ -(|c| + 1) := by nlinarith [abs_nonneg c]
  have h7 : a * (s * s) + b * s = s * (a * s + b) := by ring
  linarith [le_abs_self c]

end MomentKit

namespace MomentKit

theorem aux_qf_nonneg_of_liftQuad {k : ℕ} {M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ}
    (hM : ∀ ξ, 0 ≤ liftQuad M ξ) (d : Fin k → ℝ) :
    0 ≤ Sum.elim d 0 ⬝ᵥ M *ᵥ Sum.elim d 0 := by
  apply aux_quad_nonneg_lead (b := Sum.elim d 0 ⬝ᵥ M *ᵥ lift 0 + lift 0 ⬝ᵥ M *ᵥ Sum.elim d 0)
    (c := lift 0 ⬝ᵥ M *ᵥ lift 0)
  intro s
  have h := hM (s • d)
  unfold liftQuad at h
  rw [aux_lift_smul, aux_qf_comb] at h
  linarith

end MomentKit

namespace MomentKit

theorem aux_qf_sub {n : Type*} [Fintype n] (M : Matrix n n ℝ) (x y : n → ℝ) :
    (x - y) ⬝ᵥ M *ᵥ (x - y) = (x ⬝ᵥ M *ᵥ x) + (y ⬝ᵥ M *ᵥ y) - (x ⬝ᵥ M *ᵥ y + y ⬝ᵥ M *ᵥ x) := by
  simp only [mulVec_sub, dotProduct_sub, sub_dotProduct]
  ring

end MomentKit

namespace MomentKit

theorem aux_term_eq (ε β : ℝ) (I : ℝ≥0∞) (hI : I ≠ ⊤) :
    ((β : EReal) + ((ε⁻¹ : ℝ) : EReal) * (I : EReal)) = ((β + ε⁻¹ * I.toReal : ℝ) : EReal) := by
  rw [← EReal.coe_ennreal_toReal hI, ← EReal.coe_mul, ← EReal.coe_add]

end MomentKit

namespace MomentKit

theorem aux_term_top {ε : ℝ} (hε : 0 < ε) (β : ℝ) :
    ((β : EReal) + ((ε⁻¹ : ℝ) : EReal) * ((⊤ : ℝ≥0∞) : EReal)) = ⊤ := by
  rw [EReal.coe_ennreal_top, EReal.mul_top_of_pos (by exact_mod_cast inv_pos.2 hε),
    EReal.coe_add_top]

end MomentKit

namespace MomentKit

theorem convexOn_liftQuad {k : ℕ} {M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ}
    (hM : ∀ ξ, 0 ≤ liftQuad M ξ) : ConvexOn ℝ Set.univ (liftQuad M) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hq := aux_qf_nonneg_of_liftQuad hM (x - y)
  rw [← aux_lift_sub, aux_qf_sub] at hq
  simp only [liftQuad, smul_eq_mul]
  rw [aux_lift_comb x y a b hab, aux_qf_comb]
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [mul_nonneg ha hb]

end MomentKit

namespace MomentKit

noncomputable def cvar {k : ℕ} (ε : ℝ) (P : Measure (Fin k → ℝ)) (L : (Fin k → ℝ) → ℝ) :
    EReal :=
  ⨅ β : ℝ, ((β : EReal) + ((ε⁻¹ : ℝ) : EReal) *
    ((∫⁻ ξ, ENNReal.ofReal (L ξ - β) ∂P : ℝ≥0∞) : EReal))

end MomentKit

namespace MomentKit

theorem integrable_liftQuad {k : ℕ} {μ : Fin k → ℝ} {Sig : Matrix (Fin k) (Fin k) ℝ}
    {P : Measure (Fin k → ℝ)} (hP : P ∈ momSet μ Sig)
    (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) : Integrable (liftQuad M) P := by
  have e : liftQuad M = fun ξ => ∑ a, ∑ b, M a b * (lift ξ a * lift ξ b) :=
    funext (aux_liftQuad_sum M)
  rw [e]
  refine integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => ?_
  exact (aux_moment hP a b).1.const_mul _

end MomentKit

namespace MomentKit

theorem integral_liftQuad {k : ℕ} {μ : Fin k → ℝ} {Sig : Matrix (Fin k) (Fin k) ℝ}
    {P : Measure (Fin k → ℝ)} (hP : P ∈ momSet μ Sig)
    (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) :
    ∫ ξ, liftQuad M ξ ∂P = frob (momentMatrix μ Sig) M := by
  have hS : ∀ i j, Sig i j = Sig j i := by
    intro i j; rw [← hP.2.2]; exact aux_covMat_symm P i j
  rw [aux_frob_eq (aux_momentMatrix_symm hS)]
  simp only [aux_liftQuad_sum]
  have h1 : ∀ a, Integrable (fun ξ => ∑ b, M a b * (lift ξ a * lift ξ b)) P := fun a =>
    integrable_finset_sum _ fun b _ => (aux_moment hP a b).1.const_mul _
  rw [integral_finset_sum Finset.univ fun a _ => h1 a]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h2 : ∀ b, Integrable (fun ξ => M a b * (lift ξ a * lift ξ b)) P := fun b =>
    (aux_moment hP a b).1.const_mul _
  rw [integral_finset_sum Finset.univ fun b _ => h2 b]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, (aux_moment hP a b).2]

end MomentKit

namespace MomentKit

theorem cvar_le_of_liftQuad {k : ℕ} {ε : ℝ} (hε : 0 < ε) {μ : Fin k → ℝ}
    {Sig : Matrix (Fin k) (Fin k) ℝ} {P : Measure (Fin k → ℝ)} (hP : P ∈ momSet μ Sig)
    (L : (Fin k → ℝ) → ℝ) (β : ℝ) (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ)
    (hM : ∀ ξ, 0 ≤ liftQuad M ξ ∧ L ξ - β ≤ liftQuad M ξ) :
    cvar ε P L ≤ ((β + ε⁻¹ * frob (momentMatrix μ Sig) M : ℝ) : EReal) := by
  have := hP.1.1
  have hint := integrable_liftQuad hP M
  have hF := integral_liftQuad hP M
  have hnn : 0 ≤ frob (momentMatrix μ Sig) M := by
    rw [← hF]; exact integral_nonneg fun ξ => (hM ξ).1
  have hI : ∫⁻ ξ, ENNReal.ofReal (L ξ - β) ∂P ≤ ENNReal.ofReal (frob (momentMatrix μ Sig) M) := by
    rw [← hF, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ξ => (hM ξ).1)]
    exact lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (hM ξ).2
  have hItop : ∫⁻ ξ, ENNReal.ofReal (L ξ - β) ∂P ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hI
  unfold cvar
  refine le_trans (iInf_le _ β) ?_
  rw [aux_term_eq ε β _ hItop, EReal.coe_le_coe_iff]
  have h1 := ENNReal.toReal_le_of_le_ofReal hnn hI
  have h2 := mul_le_mul_of_nonneg_left h1 (inv_pos.2 hε).le
  linarith

end MomentKit

end

section
open MeasureTheory
open scoped ENNReal
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def psdForm (n : Type*) [Fintype n] : PointedCone ℝ (Matrix n n ℝ) where
  carrier := {A | ∀ v : n → ℝ, 0 ≤ v ⬝ᵥ A *ᵥ v}
  add_mem' := by
    intro A B hA hB v
    simp only [Set.mem_ofPred_eq, Matrix.add_mulVec, dotProduct_add] at *
    exact add_nonneg (hA v) (hB v)
  zero_mem' := by intro v; simp
  smul_mem' := by
    intro t A hA v
    have h : (0 : ℝ) ≤ (t : ℝ) * (v ⬝ᵥ A *ᵥ v) := mul_nonneg t.2 (hA v)
    simp only [Matrix.smul_mulVec, dotProduct_smul]
    exact h

theorem Matrix.PosDef.mem_interior_psdForm {n : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : A.PosDef) :
    A ∈ interior (psdForm n : Set (Matrix n n ℝ)) := by
  rw [mem_interior_iff_mem_nhds]
  have hpos : ∀ v ∈ aux2_sph n, 0 < v ⬝ᵥ A *ᵥ v := fun v hv => by
    simpa using hA.dotProduct_mulVec_pos (aux2_sph_ne hv)
  have hcont : Continuous (fun z : Matrix n n ℝ × (n → ℝ) => z.2 ⬝ᵥ z.1 *ᵥ z.2) :=
    continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd)
  have hev := (aux2_sph_compact n).eventually_forall_of_forall_eventually (x₀ := A)
    (P := fun B v => 0 < v ⬝ᵥ B *ᵥ v)
    (fun v hv => hcont.continuousAt.eventually (lt_mem_nhds (hpos v hv)))
  filter_upwards [hev] with B hB
  intro v
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨c, hc, hcv⟩ := aux2_normalize hv
  have h := hB _ hcv
  rw [aux2_qf_smul] at h
  exact (pos_of_mul_pos_right h (sq_nonneg c)).le

end

section
open MeasureTheory
open scoped ENNReal
open MeasureTheory Matrix

namespace MomentKit

theorem mem_momSet_of_integral_eq {k : ℕ} {μ : Fin k → ℝ} {Sig : Matrix (Fin k) (Fin k) ℝ}
    (P : Measure (Fin k → ℝ)) [IsFiniteMeasure P]
    (hint : ∀ a b, Integrable (fun ξ => lift ξ a * lift ξ b) P)
    (hmom : ∀ a b, ∫ ξ, lift ξ a * lift ξ b ∂P = momentMatrix μ Sig a b) :
    P ∈ momSet μ Sig := by
  exact aux_mem_momSet_of_integral_eq P hint hmom

end MomentKit

namespace MomentKit

theorem exists_liftQuad_certificate {k : ℕ} (μ : Fin k → ℝ) {Sig : Matrix (Fin k) (Fin k) ℝ}
    (hSig : Sig.PosDef) (g : (Fin k → ℝ) → ℝ) (hg : Measurable g) (p : ℝ)
    (hp : ∀ P ∈ momSet μ Sig, Integrable g P → ∫ ξ, g ξ ∂P ≤ p) :
    ∃ M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ, M.IsSymm ∧ (∀ ξ, g ξ ≤ liftQuad M ξ) ∧
      frob (momentMatrix μ Sig) M ≤ p := by
  classical
  have hSsym : ∀ i j, Sig i j = Sig j i := aux_symm_of_posDef hSig
  have hΩsym : ∀ a b, momentMatrix μ Sig a b = momentMatrix μ Sig b a :=
    aux_momentMatrix_symm hSsym
  set Ω := momentMatrix μ Sig with hΩdef
  let φ : (Fin k → ℝ) → (Fin k ⊕ Unit) × (Fin k ⊕ Unit) → ℝ :=
    fun ξ ab => lift ξ ab.1 * lift ξ ab.2
  let B : Set ((Fin k ⊕ Unit) × (Fin k ⊕ Unit) → ℝ) :=
    {s | ∀ a b, s (a, b) + s (b, a) = Ω a b + Ω b a}
  have hB : Convex ℝ B := by
    intro s₁ hs₁ s₂ hs₂ t₁ t₂ _ _ ht a b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination t₁ * hs₁ a b + t₂ * hs₂ a b + (Ω a b + Ω b a) * ht
  have hφ : ∀ ab, Measurable fun ξ => φ ξ ab := fun ab =>
    (aux_lift_measurable ab.1).mul (aux_lift_measurable ab.2)
  have hp' : ∀ P : Measure (Fin k → ℝ), IsFiniteMeasure P → P (Set.univ)ᶜ = 0 →
      (∀ ab, Integrable (fun ξ => φ ξ ab) P) → Integrable g P →
      (fun ab => ∫ ξ, φ ξ ab ∂P) ∈ B → ∫ ξ, g ξ ∂P ≤ p := by
    intro P hPf _ hφi hgi hBP
    have hmom : ∀ a b, ∫ ξ, lift ξ a * lift ξ b ∂P = Ω a b := by
      intro a b
      have h1 : (∫ ξ, lift ξ a * lift ξ b ∂P) + ∫ ξ, lift ξ b * lift ξ a ∂P = Ω a b + Ω b a :=
        hBP a b
      have h2 : ∫ ξ, lift ξ b * lift ξ a ∂P = ∫ ξ, lift ξ a * lift ξ b ∂P := by
        congr 1; funext ξ; ring
      rw [h2, hΩsym b a] at h1
      linarith
    exact hp P (mem_momSet_of_integral_eq P (fun a b => hφi (a, b)) hmom) hgi
  have hslater : (0 : (Fin k ⊕ Unit) × (Fin k ⊕ Unit) → ℝ) ∈ interior
      {u | ∃ P : Measure (Fin k → ℝ), IsFiniteMeasure P ∧ P (Set.univ)ᶜ = 0 ∧
        (∀ ab, Integrable (fun ξ => φ ξ ab) P) ∧ Integrable g P ∧
        ∃ s ∈ B, (fun ab => ∫ ξ, φ ξ ab ∂P) - s = u} := by
    let Φ : ((Fin k ⊕ Unit) × (Fin k ⊕ Unit) → ℝ) → Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ :=
      fun u => Ω + Matrix.of fun a b => (u (a, b) + u (b, a)) / 2
    have hcont : Continuous Φ := by fun_prop
    have hΩint := Matrix.PosDef.mem_interior_psdForm (aux_momentMatrix_posDef μ hSig)
    have hN1 : Φ ⁻¹' interior (psdForm (Fin k ⊕ Unit) : Set _) ∈
        nhds (0 : (Fin k ⊕ Unit) × (Fin k ⊕ Unit) → ℝ) := by
      refine hcont.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds ?_)
      have : Φ 0 = Ω := by ext a b; simp [Φ]
      rw [this]; exact hΩint
    have hN2 : {u : (Fin k ⊕ Unit) × (Fin k ⊕ Unit) → ℝ | -1 < u (Sum.inr (), Sum.inr ())} ∈
        nhds 0 :=
      (isOpen_lt continuous_const (continuous_apply _)).mem_nhds (by simp)
    rw [mem_interior_iff_mem_nhds]
    refine Filter.mem_of_superset (Filter.inter_mem hN1 hN2) ?_
    rintro u ⟨hu1, hu2⟩
    have hsym : ∀ a b, Φ u a b = Φ u b a := by
      intro a b; simp only [Φ, Matrix.add_apply, Matrix.of_apply]; rw [hΩsym]; ring
    have hpsd : ∀ v, 0 ≤ v ⬝ᵥ Φ u *ᵥ v := interior_subset hu1
    have hc0 : 0 < Φ u (Sum.inr ()) (Sum.inr ()) := by
      simp only [Φ, Matrix.add_apply, Matrix.of_apply, hΩdef, aux_mm_rr]
      simp only [Set.mem_setOf_eq] at hu2
      linarith
    obtain ⟨N, w, ξ, hw, hsum⟩ := aux_discrete_of_psd hsym hpsd hc0
    have hfin := aux_isFinite_discrete w ξ
    have hval : ∀ a b, ∫ x, φ x (a, b) ∂(discrete w ξ) = Φ u a b := by
      intro a b
      rw [aux_integral_discrete w ξ hw, ← hsum]
      simp [φ, Matrix.sum_apply, Matrix.vecMulVec_apply]
    refine ⟨discrete w ξ, hfin, by simp, fun ab => aux_integrable_discrete w ξ _,
      aux_integrable_discrete w ξ _, (fun ab => ∫ x, φ x ab ∂(discrete w ξ)) - u, ?_, by simp⟩
    intro a b
    simp only [Pi.sub_apply, hval]
    simp only [Φ, Matrix.add_apply, Matrix.of_apply]
    ring
  obtain ⟨η, hη1, hη2⟩ := MomentProblem.exists_dual_of_slater Set.univ MeasurableSet.univ φ hφ g hg B hB p
    hp' hslater
  let M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ := Matrix.of fun a b => (η (a, b) + η (b, a)) / 2
  have hMsym : M.IsSymm := by
    ext a b
    simp only [M, transpose_apply, Matrix.of_apply]
    ring
  have hL : ∀ ξ, liftQuad M ξ = η ⬝ᵥ φ ξ := by
    intro ξ
    rw [aux_liftQuad_sum]
    simp only [dotProduct, Fintype.sum_prod_type, M, Matrix.of_apply, φ]
    have h2 : ∑ a, ∑ b, η (b, a) * (lift ξ a * lift ξ b) =
        ∑ a, ∑ b, η (a, b) * (lift ξ a * lift ξ b) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    have e : ∀ a b, (η (a, b) + η (b, a)) / 2 * (lift ξ a * lift ξ b) =
        (1 / 2) * (η (a, b) * (lift ξ a * lift ξ b)) +
          (1 / 2) * (η (b, a) * (lift ξ a * lift ξ b)) := by
      intro a b; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, h2]
    ring
  have hF : frob Ω M = η ⬝ᵥ (fun ab => Ω ab.1 ab.2) := by
    rw [aux_frob_eq hΩsym]
    simp only [dotProduct, Fintype.sum_prod_type, M, Matrix.of_apply]
    have h2 : ∑ a, ∑ b, η (b, a) * Ω a b = ∑ a, ∑ b, η (a, b) * Ω a b := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hΩsym]
    have e : ∀ a b, (η (a, b) + η (b, a)) / 2 * Ω a b =
        (1 / 2) * (η (a, b) * Ω a b) + (1 / 2) * (η (b, a) * Ω a b) := by
      intro a b; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, h2]
    ring
  refine ⟨M, hMsym, fun ξ => ?_, ?_⟩
  · rw [hL]; exact hη1 ξ (Set.mem_univ _)
  · rw [hF]; exact hη2 _ (fun a b => rfl)

end MomentKit

namespace MomentKit

theorem liftQuad_eq {k : ℕ} (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) (ξ : Fin k → ℝ) :
    liftQuad M ξ = ξ ⬝ᵥ M.toBlocks₁₁ *ᵥ ξ +
      2 * ((fun i => (M (Sum.inl i) (Sum.inr ()) + M (Sum.inr ()) (Sum.inl i)) / 2) ⬝ᵥ ξ) +
      M (Sum.inr ()) (Sum.inr ()) := by
  have h := aux_quad_elim M ξ 1
  simp only [one_mul] at h
  exact h

end MomentKit

end

section
open MeasureTheory
open scoped ENNReal
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem sLemma_inhom {n : Type*} [Fintype n] (A₁ A₂ : Matrix n n ℝ) (b₁ b₂ : n → ℝ) (c₁ c₂ : ℝ)
    (hslater : ∃ x₀, x₀ ⬝ᵥ A₂ *ᵥ x₀ + 2 * b₂ ⬝ᵥ x₀ + c₂ < 0) :
    (∀ x, x ⬝ᵥ A₂ *ᵥ x + 2 * b₂ ⬝ᵥ x + c₂ ≤ 0 → 0 ≤ x ⬝ᵥ A₁ *ᵥ x + 2 * b₁ ⬝ᵥ x + c₁) ↔
      ∃ τ : ℝ, 0 ≤ τ ∧ ∀ x, 0 ≤ (x ⬝ᵥ A₁ *ᵥ x + 2 * b₁ ⬝ᵥ x + c₁) + τ * (x ⬝ᵥ A₂ *ᵥ x + 2 * b₂ ⬝ᵥ x + c₂) := by
  constructor
  · intro H
    obtain ⟨x₀, hx₀⟩ := hslater
    have H1 : ∀ u, aux2_Q A₂ b₂ c₂ (u, 1) ≤ 0 → 0 ≤ aux2_Q A₁ b₁ c₁ (u, 1) := by
      intro u hu
      rw [aux2_Q_one] at hu ⊢
      exact H u hu
    have hP0 : aux2_Q A₂ b₂ c₂ (x₀, 1) < 0 := by rw [aux2_Q_one]; exact hx₀
    have hHom : ∀ p : (n → ℝ) × ℝ, 0 ≤ -aux2_Q A₂ b₂ c₂ p → 0 ≤ aux2_Q A₁ b₁ c₁ p := by
      rintro ⟨w, t⟩ hp
      by_cases ht : t = 0
      · subst ht
        have hline : ∀ s : ℝ, ((x₀, (1 : ℝ)) + s • (w, (0 : ℝ))) = (x₀ + s • w, 1) := by
          intro s; ext <;> simp
        refine aux2_t0 (aux2_Q A₁ b₁ c₁) (aux2_Q A₂ b₂ c₂) (x₀, 1) (w, 0)
          ⟨_, aux2_Q_exp A₁ b₁ c₁ (x₀, 1) (w, 0)⟩ ⟨_, aux2_Q_exp A₂ b₂ c₂ (x₀, 1) (w, 0)⟩
          hP0 (by linarith) fun s hs => ?_
        rw [hline] at hs ⊢
        exact H1 _ hs
      · obtain ⟨u, rfl⟩ : ∃ u, w = t • u := ⟨t⁻¹ • w, by rw [smul_smul, mul_inv_cancel₀ ht, one_smul]⟩
        rw [aux2_Q_scale] at hp ⊢
        have ht2 : 0 < t ^ 2 := by positivity
        have h2 : aux2_Q A₂ b₂ c₂ (u, 1) ≤ 0 := by nlinarith
        have := H1 u h2
        positivity
    obtain ⟨τ, hτ, h⟩ := SLemma.exists_multiplier_of_quadratic_along_lines (aux2_Q A₁ b₁ c₁) (fun p => -aux2_Q A₂ b₂ c₂ p)
      (fun p q => ⟨_, aux2_Q_exp A₁ b₁ c₁ p q⟩)
      (fun p q => ⟨-(p.1 ⬝ᵥ A₂ *ᵥ q.1 + q.1 ⬝ᵥ A₂ *ᵥ p.1 +
          2 * (p.2 * (b₂ ⬝ᵥ q.1) + q.2 * (b₂ ⬝ᵥ p.1)) + 2 * c₂ * p.2 * q.2), fun s => by
        show -aux2_Q A₂ b₂ c₂ (p + s • q) = _
        rw [aux2_Q_exp A₂ b₂ c₂ p q s]
        ring⟩)
      ⟨(x₀, 1), by linarith⟩ hHom
    refine ⟨τ, hτ, fun x => ?_⟩
    have := h (x, 1)
    rw [aux2_Q_one, aux2_Q_one] at this
    linarith
  · rintro ⟨τ, hτ, h⟩ x hx
    have := h x
    nlinarith

end

section
open MeasureTheory
open scoped ENNReal
open MeasureTheory Matrix

theorem exists_tau {k : ℕ} (L : (Fin k → ℝ) → ℝ)
    (hshape : ConcaveOn ℝ Set.univ L ∨ DRJointCC.Individual.IsQuadratic L)
    (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) (hM0 : ∀ ξ, 0 ≤ MomentKit.liftQuad M ξ)
    (δ : ℝ) (ξ₀ : Fin k → ℝ) (hξ₀ : δ < L ξ₀)
    (H : ∀ ξ, δ ≤ L ξ → 1 ≤ MomentKit.liftQuad M ξ) :
    ∃ τ : ℝ, 0 ≤ τ ∧ ∀ ξ, 0 ≤ MomentKit.liftQuad M ξ - 1 - τ * (L ξ - δ) := by
  rcases hshape with hc | ⟨Q, q, q0, hLq⟩
  · obtain ⟨τ, hτ, h⟩ := SLemma.concave_convex (fun ξ => L ξ - δ)
      (fun ξ => MomentKit.liftQuad M ξ - 1) (hc.sub (convexOn_const δ convex_univ))
      ((MomentKit.convexOn_liftQuad hM0).sub (concaveOn_const 1 convex_univ)) ⟨ξ₀, by linarith⟩
      (fun x hx => by have := H x (by linarith); linarith)
    exact ⟨τ, hτ, fun ξ => by have := h ξ; linarith⟩
  · have hA2 : ∀ x : Fin k → ℝ, x ⬝ᵥ (-Q) *ᵥ x + 2 * ((-(1 / 2 : ℝ)) • q) ⬝ᵥ x + (δ - q0)
        = δ - L x := by
      intro x; rw [hLq]; simp [Matrix.neg_mulVec, smul_dotProduct]; ring
    have hA1 : ∀ x : Fin k → ℝ, x ⬝ᵥ M.toBlocks₁₁ *ᵥ x +
        2 * ((fun i => (M (Sum.inl i) (Sum.inr ()) + M (Sum.inr ()) (Sum.inl i)) / 2) ⬝ᵥ x) +
        (M (Sum.inr ()) (Sum.inr ()) - 1) = MomentKit.liftQuad M x - 1 := by
      intro x; rw [MomentKit.liftQuad_eq]; ring
    obtain ⟨τ, hτ, h⟩ := (sLemma_inhom M.toBlocks₁₁ (-Q)
      (fun i => (M (Sum.inl i) (Sum.inr ()) + M (Sum.inr ()) (Sum.inl i)) / 2)
      ((-(1 / 2 : ℝ)) • q) (M (Sum.inr ()) (Sum.inr ()) - 1) (δ - q0)
      ⟨ξ₀, by rw [hA2]; linarith⟩).mp
      (fun x hx => by rw [hA2] at hx; rw [hA1]; have := H x (by linarith); linarith)
    exact ⟨τ, hτ, fun ξ => by have := h ξ; rw [hA1, hA2] at this; linarith⟩

theorem frob_smul {k : ℕ} (c : ℝ) (X M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) :
    MomentKit.frob X (c • M) = c * MomentKit.frob X M := by
  simp [MomentKit.frob, Matrix.trace_smul]

namespace MomentKit

theorem discrete_mem_momSet {k N : ℕ} {μ : Fin k → ℝ} {Sig : Matrix (Fin k) (Fin k) ℝ}
    (w : Fin N → ℝ) (ξ : Fin N → Fin k → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hmom : ∑ j, w j • Matrix.vecMulVec (lift (ξ j)) (lift (ξ j)) = momentMatrix μ Sig) :
    discrete w ξ ∈ momSet μ Sig := by
  have := aux_isFinite_discrete w ξ
  refine aux_mem_momSet_of_integral_eq _ (fun a b => aux_integrable_discrete w ξ _) ?_
  intro a b
  rw [aux_integral_discrete w ξ hw, ← hmom]
  simp [Matrix.sum_apply, Matrix.vecMulVec_apply, mul_assoc]

end MomentKit

namespace MomentKit

theorem momSet_nonempty {k : ℕ} (μ : Fin k → ℝ) {Sig : Matrix (Fin k) (Fin k) ℝ}
    (hSig : Sig.PosSemidef) : (momSet μ Sig).Nonempty := by
  obtain ⟨s, hs⟩ := Matrix.PosSemidef.exists_eq_sum_vecMulVec hSig
  obtain ⟨N, w, ξ, hw, hsum⟩ := aux_atoms 1 one_pos μ s
  refine ⟨discrete w ξ, discrete_mem_momSet w ξ hw ?_⟩
  rw [hsum]
  ext a a'
  have hS : ∀ i j, ∑ l, s l i * s l j = Sig i j := by
    intro i j
    have := congrFun (congrFun hs i) j
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply] at this
    exact this.symm
  cases a with
  | inl i =>
    cases a' with
    | inl j =>
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
        smul_eq_mul, lift, Sum.elim_inl, aux_mm_ll, hS]
      ring
    | inr u => simp [lift, aux_mm_lr, aux_mm_rl, aux_mm_rr, Matrix.sum_apply, Matrix.vecMulVec_apply]
  | inr u =>
    cases a' with
    | inl j => simp [lift, aux_mm_lr, aux_mm_rl, aux_mm_rr, Matrix.sum_apply, Matrix.vecMulVec_apply]
    | inr v => simp [lift, aux_mm_lr, aux_mm_rl, aux_mm_rr, Matrix.sum_apply, Matrix.vecMulVec_apply]

end MomentKit

namespace MomentKit

theorem le_frob_of_le_liftQuad {k : ℕ} (μ : Fin k → ℝ) {Sig : Matrix (Fin k) (Fin k) ℝ}
    (hSig : Sig.PosSemidef) (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) (c : ℝ)
    (h : ∀ ξ, c ≤ liftQuad M ξ) : c ≤ frob (momentMatrix μ Sig) M := by
  obtain ⟨P, hP⟩ := momSet_nonempty μ hSig
  have := hP.1.1
  rw [← integral_liftQuad hP M]
  have := integral_mono (integrable_const c) (integrable_liftQuad hP M) h
  simpa using this

end MomentKit

theorem liftQuad_smul {k : ℕ} (c : ℝ) (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ)
    (ξ : Fin k → ℝ) : MomentKit.liftQuad (c • M) ξ = c * MomentKit.liftQuad M ξ := by
  simp [MomentKit.liftQuad, Matrix.smul_mulVec, dotProduct_smul]

theorem num1 (τ lq a : ℝ) (hτ : 0 < τ) (h : 0 ≤ lq - 1 - τ * a) : a + τ⁻¹ ≤ τ⁻¹ * lq := by
  have e : τ⁻¹ * lq - (a + τ⁻¹) = τ⁻¹ * (lq - 1 - τ * a) := by
    field_simp
    ring
  have : 0 ≤ τ⁻¹ * (lq - 1 - τ * a) := mul_nonneg (inv_nonneg.mpr hτ.le) h
  linarith

theorem num2 (ε τ f δ : ℝ) (hε : 0 < ε) (hτ : 0 < τ) (hf : f ≤ ε) :
    δ - τ⁻¹ + ε⁻¹ * (τ⁻¹ * f) ≤ δ := by
  have h1 : ε⁻¹ * (τ⁻¹ * f) ≤ ε⁻¹ * (τ⁻¹ * ε) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf (inv_nonneg.mpr hτ.le))
      (inv_nonneg.mpr hε.le)
  have h2 : ε⁻¹ * (τ⁻¹ * ε) = τ⁻¹ := by field_simp
  linarith

theorem cvar_le_delta {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ)
    (hSig : Sig.PosDef) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (L : (Fin k → ℝ) → ℝ) (hL : Measurable L)
    (hshape : ConcaveOn ℝ Set.univ L ∨ DRJointCC.Individual.IsQuadratic L)
    (hcc : ∀ P ∈ MomentKit.momSet μ Sig, P.real {ξ | 0 < L ξ} ≤ ε)
    (δ : ℝ) (hδ : 0 < δ) (ξ₀ : Fin k → ℝ) (hξ₀ : δ < L ξ₀) :
    ∀ P ∈ MomentKit.momSet μ Sig, MomentKit.cvar ε P L ≤ (δ : EReal) := by
  classical
  have hsm : MeasurableSet {ξ : Fin k → ℝ | 0 < L ξ} := measurableSet_lt measurable_const hL
  have hgm : Measurable (Set.indicator {ξ : Fin k → ℝ | 0 < L ξ} (1 : (Fin k → ℝ) → ℝ)) :=
    measurable_const.indicator hsm
  obtain ⟨M, -, hgM, hfrob⟩ := MomentKit.exists_liftQuad_certificate μ hSig _ hgm ε
    (fun P hP _ => by rw [integral_indicator_one hsm]; exact hcc P hP)
  have hM0 : ∀ ξ, 0 ≤ MomentKit.liftQuad M ξ := fun ξ =>
    le_trans (Set.indicator_nonneg (fun _ _ => zero_le_one) ξ) (hgM ξ)
  have H : ∀ ξ, δ ≤ L ξ → 1 ≤ MomentKit.liftQuad M ξ := by
    intro ξ hξ
    have hmem : ξ ∈ {ξ : Fin k → ℝ | 0 < L ξ} := by
      show 0 < L ξ
      linarith
    have := hgM ξ
    rwa [Set.indicator_of_mem hmem, Pi.one_apply] at this
  obtain ⟨τ, hτ, hτM⟩ := exists_tau L hshape M hM0 δ ξ₀ hξ₀ H
  have hτpos : 0 < τ := by
    rcases hτ.lt_or_eq with h | h
    · exact h
    · exfalso
      subst h
      have h1 : ∀ ξ, (1 : ℝ) ≤ MomentKit.liftQuad M ξ := fun ξ => by
        have := hτM ξ; simp at this; linarith
      have := MomentKit.le_frob_of_le_liftQuad μ hSig.posSemidef M 1 h1
      linarith
  intro P hP
  have hc := MomentKit.cvar_le_of_liftQuad hε hP L (δ - τ⁻¹) (τ⁻¹ • M) (fun ξ => by
    rw [liftQuad_smul]
    refine ⟨mul_nonneg (inv_nonneg.mpr hτ) (hM0 ξ), ?_⟩
    have := num1 τ (MomentKit.liftQuad M ξ) (L ξ - δ) hτpos (hτM ξ)
    linarith)
  refine hc.trans ?_
  rw [frob_smul]
  exact EReal.coe_le_coe_iff.mpr (num2 ε τ _ δ hε hτpos hfrob)

theorem ereal_le_zero (x : EReal) (a : ℝ) (ha : 0 < a)
    (h : ∀ δ : ℝ, 0 < δ → δ < a → x ≤ δ) : x ≤ 0 := by
  by_contra hx
  push Not at hx
  obtain ⟨r, h0r, hrx⟩ := EReal.lt_iff_exists_real_btwn.mp hx
  have h0r' : (0 : ℝ) < r := by exact_mod_cast h0r
  have h1 := h (min r (a / 2)) (lt_min h0r' (by linarith))
    (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have h2 : x ≤ (r : EReal) := h1.trans (by exact_mod_cast min_le_left r (a / 2))
  exact absurd hrx (not_lt.mpr h2)

theorem frob_zero {k : ℕ} (X : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) :
    MomentKit.frob X 0 = 0 := by
  simp [MomentKit.frob]

namespace MomentKit

theorem le_cvar_of_lt_measure {k : ℕ} {ε : ℝ} (hε : 0 < ε) (P : Measure (Fin k → ℝ))
    (L : (Fin k → ℝ) → ℝ) (hL : Measurable L) (t : ℝ)
    (ht : ENNReal.ofReal ε < P {ξ | t < L ξ}) : (t : EReal) ≤ cvar ε P L := by
  unfold cvar
  refine le_iInf fun β => ?_
  by_cases hI : ∫⁻ ξ, ENNReal.ofReal (L ξ - β) ∂P = ⊤
  · rw [hI, aux_term_top hε]; exact le_top
  rw [aux_term_eq ε β _ hI, EReal.coe_le_coe_iff]
  have hI0 : 0 ≤ (∫⁻ ξ, ENNReal.ofReal (L ξ - β) ∂P).toReal := ENNReal.toReal_nonneg
  have hεi : 0 < ε⁻¹ := inv_pos.2 hε
  rcases le_or_gt t β with htb | htb
  · nlinarith
  · have hmeas : MeasurableSet {ξ | t < L ξ} := measurableSet_lt measurable_const hL
    have hmark : ENNReal.ofReal (t - β) * P {ξ | t < L ξ} ≤
        ∫⁻ ξ, ENNReal.ofReal (L ξ - β) ∂P := by
      rw [← lintegral_indicator_const hmeas]
      refine lintegral_mono fun ξ => ?_
      by_cases h : t < L ξ
      · rw [Set.indicator_of_mem (show ξ ∈ {ξ | t < L ξ} from h)]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      · rw [Set.indicator_of_notMem (show ξ ∉ {ξ | t < L ξ} from h)]
        simp
    have h2 : ENNReal.ofReal ((t - β) * ε) ≤ ∫⁻ ξ, ENNReal.ofReal (L ξ - β) ∂P := by
      rw [ENNReal.ofReal_mul (by linarith)]
      exact le_trans (mul_le_mul_right ht.le _) hmark
    have h3 := (ENNReal.ofReal_le_iff_le_toReal hI).1 h2
    have h4 : t - β ≤ ε⁻¹ * (∫⁻ ξ, ENNReal.ofReal (L ξ - β) ∂P).toReal := by
      rw [le_inv_mul_iff₀ hε]; linarith
    linarith

end MomentKit

theorem liftQuad_zero {k : ℕ} (ξ : Fin k → ℝ) :
    MomentKit.liftQuad (0 : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) ξ = 0 := by
  simp [MomentKit.liftQuad]

namespace MomentKit

theorem ofReal_le_measure_of_cvar_nonpos {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (P : Measure (Fin k → ℝ)) [IsProbabilityMeasure P] (L : (Fin k → ℝ) → ℝ)
    (hL : Measurable L) (h : cvar ε P L ≤ 0) :
    ENNReal.ofReal (1 - ε) ≤ P {ξ | L ξ ≤ 0} := by
  rcases le_or_gt 1 ε with h1 | h1
  · rw [ENNReal.ofReal_of_nonpos (by linarith)]; simp
  by_contra hcon
  push Not at hcon
  have hmeas : MeasurableSet {ξ | L ξ ≤ 0} := measurableSet_le hL measurable_const
  have hcompl : {ξ | L ξ ≤ 0}ᶜ = {ξ | 0 < L ξ} := by ext ξ; simp
  have hgt : ENNReal.ofReal ε < P {ξ | 0 < L ξ} := by
    by_contra hle
    push Not at hle
    have hsum := measure_add_measure_compl (μ := P) hmeas
    rw [hcompl, measure_univ] at hsum
    have hlt := ENNReal.add_lt_add_of_lt_of_le (measure_ne_top P _) hcon hle
    rw [hsum, ← ENNReal.ofReal_add (by linarith) hε.le] at hlt
    simp at hlt
  let s : ℕ → Set (Fin k → ℝ) := fun n => {ξ | 1 / ((n : ℝ) + 1) < L ξ}
  have hmono : Monotone s := by
    intro n m hnm ξ hξ
    simp only [s, Set.mem_setOf_eq] at hξ ⊢
    refine lt_of_le_of_lt ?_ hξ
    apply one_div_le_one_div_of_le (by positivity)
    have : (n : ℝ) ≤ m := by exact_mod_cast hnm
    linarith
  have hU : (⋃ n, s n) = {ξ | 0 < L ξ} := by
    ext ξ
    simp only [s, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn⟩
      exact lt_trans (by positivity) hn
    · intro hξ
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hξ
      exact ⟨n, hn⟩
  have ht := tendsto_measure_iUnion_atTop (μ := P) hmono
  rw [hU] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (lt_mem_nhds hgt)).exists
  have hc := le_cvar_of_lt_measure hε P L hL (1 / ((n : ℝ) + 1)) hn
  have h0 : ((1 / ((n : ℝ) + 1) : ℝ) : EReal) ≤ ((0 : ℝ) : EReal) := le_trans hc h
  rw [EReal.coe_le_coe_iff] at h0
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

end MomentKit

theorem real_pos_le {k : ℕ} (P : Measure (Fin k → ℝ)) [IsProbabilityMeasure P]
    (L : (Fin k → ℝ) → ℝ) (hL : Measurable L) (ε : ℝ)
    (h : ENNReal.ofReal (1 - ε) ≤ P {ξ | L ξ ≤ 0}) : P.real {ξ | 0 < L ξ} ≤ ε := by
  have hs : MeasurableSet {ξ | L ξ ≤ 0} := measurableSet_le hL measurable_const
  have hc : {ξ | 0 < L ξ} = {ξ | L ξ ≤ 0}ᶜ := by ext; simp
  rw [hc, probReal_compl_eq_one_sub hs]
  have : 1 - ε ≤ P.real {ξ | L ξ ≤ 0} := by
    rw [measureReal_def]; exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp h
  linarith

end

section
open MeasureTheory
open scoped ENNReal

open DRJointCC.Individual in
theorem solution {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ)
    (hSig : Sig.PosDef) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (L : (Fin k → ℝ) → ℝ) (hL : Continuous L)
    (hshape : ConcaveOn ℝ Set.univ L ∨ IsQuadratic L) :
    wcCVaR ε μ Sig L ≤ 0 ↔
      ENNReal.ofReal (1 - ε) ≤ ⨅ P ∈ ambiguitySet μ Sig, P {ξ | L ξ ≤ 0} := by
  have hmeas : Measurable L := hL.measurable
  change (⨆ P ∈ MomentKit.momSet μ Sig, MomentKit.cvar ε P L) ≤ 0 ↔
    ENNReal.ofReal (1 - ε) ≤ ⨅ P ∈ MomentKit.momSet μ Sig, P {ξ | L ξ ≤ 0}
  constructor
  · intro h
    refine le_iInf₂ fun P hP => ?_
    have : MeasureTheory.IsProbabilityMeasure P := hP.1.1
    exact MomentKit.ofReal_le_measure_of_cvar_nonpos hε P L hmeas
      ((le_iSup₂ (f := fun P (_ : P ∈ MomentKit.momSet μ Sig) => MomentKit.cvar ε P L) P hP).trans h)
  · intro h
    have hcc : ∀ P ∈ MomentKit.momSet μ Sig, P.real {ξ | 0 < L ξ} ≤ ε := fun P hP => by
      have : MeasureTheory.IsProbabilityMeasure P := hP.1.1
      exact real_pos_le P L hmeas ε
        (h.trans (iInf₂_le P hP))
    by_cases hpos : ∃ ξ₀, 0 < L ξ₀
    · obtain ⟨ξ₀, hξ₀⟩ := hpos
      refine ereal_le_zero _ (L ξ₀) hξ₀ ?_
      intro δ hδ hδL
      exact iSup₂_le (cvar_le_delta μ Sig hSig ε hε hε1
        L hmeas hshape hcc δ hδ ξ₀ hδL)
    · push Not at hpos
      refine iSup₂_le fun P hP => ?_
      have := MomentKit.cvar_le_of_liftQuad hε hP L 0 0 (fun ξ => by
        simp only [liftQuad_zero, sub_zero]
        exact ⟨le_refl _, hpos ξ⟩)
      simpa [frob_zero] using this

end
