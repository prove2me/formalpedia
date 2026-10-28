-- Prove2me | solution 1 for ExtraConsensus.Sublinear.eq_3_20
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T03:23:03.240137+00:00
-- url     : https://prove2.me/submissions/13011117-40b2-4335-84e7-87e5d6994fe0

import Mathlib
import Definitions.Def_ExtraConsensus_Sublinear_Model

namespace Aux_EC_320

open Matrix ExtraConsensus.Sublinear

variable {n p : ℕ}

lemma frob_mix (M : Matrix (Fin n) (Fin n) ℝ) (x y : Stack n p) :
    frob x (mix M y) = ∑ i, ∑ j, M i j * inner ℝ (x i) (y j) := by
  unfold frob mix
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_right]

lemma frob_comm (x y : Stack n p) : frob x y = frob y x := by
  unfold frob
  exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _

lemma mix_frob (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) (x y : Stack n p) :
    frob (mix M x) y = frob x (mix M y) := by
  rw [frob_comm, frob_mix, frob_mix, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : M j i = M i j := by
    have := congrFun (congrFun hM i) j
    simpa [Matrix.transpose_apply] using this
  rw [this, real_inner_comm]

lemma mix_add (A B : Matrix (Fin n) (Fin n) ℝ) (x : Stack n p) :
    mix (A + B) x = mix A x + mix B x := by
  funext i
  simp [mix, add_smul, Finset.sum_add_distrib]

lemma mix_sub (A B : Matrix (Fin n) (Fin n) ℝ) (x : Stack n p) :
    mix (A - B) x = mix A x - mix B x := by
  funext i
  simp [mix, sub_smul, Finset.sum_sub_distrib]

lemma mix_one (x : Stack n p) : mix 1 x = x := by
  funext i
  simp [mix, Matrix.one_apply, ite_smul]

lemma mix_addv (A : Matrix (Fin n) (Fin n) ℝ) (x y : Stack n p) :
    mix A (x + y) = mix A x + mix A y := by
  funext i
  simp [mix, smul_add, Finset.sum_add_distrib]

lemma mix_subv (A : Matrix (Fin n) (Fin n) ℝ) (x y : Stack n p) :
    mix A (x - y) = mix A x - mix A y := by
  funext i
  simp [mix, smul_sub, Finset.sum_sub_distrib]

lemma mix_smulv (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x : Stack n p) :
    mix A (c • x) = c • mix A x := by
  funext i
  simp only [mix, Pi.smul_apply, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun j _ => by rw [mul_comm]

lemma mix_mul (A B : Matrix (Fin n) (Fin n) ℝ) (x : Stack n p) :
    mix (A * B) x = mix A (mix B x) := by
  funext i
  simp only [mix, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

lemma frob_add_left (a b c : Stack n p) : frob (a + b) c = frob a c + frob b c := by
  unfold frob; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp [inner_add_left]

lemma frob_add_right (a b c : Stack n p) : frob a (b + c) = frob a b + frob a c := by
  rw [frob_comm, frob_add_left, frob_comm b, frob_comm c]

lemma frob_smul_left (r : ℝ) (a b : Stack n p) : frob (r • a) b = r * frob a b := by
  unfold frob; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp [real_inner_smul_left]

lemma frob_neg (a : Stack n p) : frob (-a) (-a) = frob a a := by
  unfold frob
  exact Finset.sum_congr rfl fun i _ => by simp

lemma Q_expand (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) (a b : Stack n p) :
    mnormSq M (a + b) = mnormSq M a + 2 * frob a (mix M b) + mnormSq M b := by
  unfold mnormSq
  rw [mix_addv, frob_add_left, frob_add_right, frob_add_right]
  have : frob b (mix M a) = frob a (mix M b) := by
    rw [← mix_frob M hM, frob_comm]
  rw [this]; ring

lemma Q_smul (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (a : Stack n p) :
    mnormSq M (c • a) = c ^ 2 * mnormSq M a := by
  unfold mnormSq
  rw [mix_smulv, frob_smul_left, frob_comm, frob_smul_left, frob_comm]
  ring

lemma frob_smul_mix (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (a b : Stack n p) :
    frob (c • a) (mix M b) = c * frob a (mix M b) := frob_smul_left c a _

lemma Q_nonneg (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef) (x : Stack n p) :
    0 ≤ mnormSq M x := by
  unfold mnormSq
  rw [frob_mix]
  have : ∑ i, ∑ j, M i j * inner ℝ (x i) (x j) =
      ∑ c : Fin p, (fun i => x i c) ⬝ᵥ (M *ᵥ (fun i => x i c)) := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mulVec, star_trivial,
      Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this]
  refine Finset.sum_nonneg fun c _ => ?_
  have := hM.dotProduct_mulVec_nonneg (fun i => x i c)
  simpa using this

end Aux_EC_320

open Matrix Filter Topology Asymptotics ExtraConsensus.Sublinear Aux_EC_320 in
theorem solution {n p : ℕ} (Gr : SimpleGraph (Fin n))
    (W Wt U : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (α : ℝ)
    (hA1 : MixingAssumption Gr W Wt)
    (hUs : Uᵀ = U) (hUpsd : U.PosSemidef) (hU2 : U * U = Wt - W)
    (x0 : Stack n p) (ρ : ℝ) (hρ : 1 < ρ) :
    let x := extraIter α W Wt f x0
    let q := qSeq U x
    ∀ k : ℕ,
      zNormSq Wt (q k - q (k + 1)) (x k - x (k + 1)) =
          frob (q k - q (k + 1)) (q k - q (k + 1)) + mnormSq Wt (x k - x (k + 1)) ∧
        zNormSq Wt (q k - q (k + 1)) (x k - x (k + 1)) =
          mnormSq (Wt - W) (x (k + 1)) +
            mnormSq Wt (mix (1 - Wt) (x k) + mix U (q k) + α • gradF f (x k)) ∧
        mnormSq (Wt - W) (x (k + 1)) + 1 / ρ * mnormSq Wt (mix U (q k) + α • gradF f (x k))
            - 1 / (ρ - 1) * mnormSq Wt (mix (1 - Wt) (x k)) ≤
          zNormSq Wt (q k - q (k + 1)) (x k - x (k + 1)) := by
  intro x q
  have hq : ∀ k, q (k + 1) = q k + mix U (x (k + 1)) := by
    intro k
    simp only [q, qSeq]
    rw [Finset.sum_range_succ]
  have hUU : ∀ v : Stack n p, mix U (mix U v) = mix Wt v - mix W v := by
    intro v; rw [← mix_mul, hU2, mix_sub]
  -- the recursion in "q-form"
  have hrec : ∀ k, x (k + 1) = mix Wt (x k) - mix U (q k) - α • gradF f (x k) := by
    intro k
    induction k with
    | zero =>
      have h0 : q 0 = mix U (x 0) := by simp [q, qSeq]
      rw [h0, hUU]
      show mix W x0 - α • gradF f x0 = mix Wt x0 - (mix Wt x0 - mix W x0) - α • gradF f x0
      abel
    | succ k ih =>
      have hdef : x (k + 2) = mix (1 + W) (x (k + 1)) - mix Wt (x k)
          - α • (gradF f (x (k + 1)) - gradF f (x k)) := rfl
      rw [hdef, hq k, mix_addv, hUU, mix_add, mix_one]
      have hmq : mix U (q k) = mix Wt (x k) - x (k + 1) - α • gradF f (x k) := by
        rw [ih]; abel
      rw [hmq, smul_sub]
      abel
  intro k
  have hdx : x k - x (k + 1) = mix (1 - Wt) (x k) + mix U (q k) + α • gradF f (x k) := by
    rw [hrec k, mix_sub, mix_one]; abel
  have hdq : q k - q (k + 1) = -mix U (x (k + 1)) := by rw [hq k]; abel
  have hfq : frob (q k - q (k + 1)) (q k - q (k + 1)) = mnormSq (Wt - W) (x (k + 1)) := by
    rw [hdq, frob_neg, mix_frob U hUs, hUU, ← mix_sub]
    rfl
  have c1 : zNormSq Wt (q k - q (k + 1)) (x k - x (k + 1)) =
      frob (q k - q (k + 1)) (q k - q (k + 1)) + mnormSq Wt (x k - x (k + 1)) := rfl
  have c2 : zNormSq Wt (q k - q (k + 1)) (x k - x (k + 1)) =
      mnormSq (Wt - W) (x (k + 1)) +
        mnormSq Wt (mix (1 - Wt) (x k) + mix U (q k) + α • gradF f (x k)) := by
    rw [c1, hfq, hdx]
  refine ⟨c1, c2, ?_⟩
  rw [c2]
  set A := mix (1 - Wt) (x k) with hA
  set B := mix U (q k) + α • gradF f (x k) with hB
  have hAB : A + mix U (q k) + α • gradF f (x k) = A + B := by rw [hB]; abel
  rw [hAB]
  have hWs : Wtᵀ = Wt := hA1.symm_Wt
  have hpsd : Wt.PosSemidef := hA1.posDef_Wt.posSemidef
  set lam := ρ / (ρ - 1) with hlam
  have hρ1 : 0 < ρ - 1 := by linarith
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hnn := Q_nonneg Wt hpsd (B + lam • A)
  rw [Q_expand Wt hWs, Q_smul] at hnn
  have hexp := Q_expand Wt hWs A B
  have hc : frob B (mix Wt (lam • A)) = lam * frob A (mix Wt B) := by
    rw [mix_smulv, frob_comm, frob_smul_left, mix_frob Wt hWs]
  rw [hc] at hnn
  rw [hexp]
  have hQA := Q_nonneg Wt hpsd A
  have hQB := Q_nonneg Wt hpsd B
  -- multiply the nonnegativity by (ρ-1)/ρ
  have hk : 0 < (ρ - 1) / ρ := by positivity
  have key : (mnormSq Wt A + 2 * frob A (mix Wt B) + mnormSq Wt B) -
      (1 / ρ * mnormSq Wt B - 1 / (ρ - 1) * mnormSq Wt A) =
      (ρ - 1) / ρ * (mnormSq Wt B + 2 * (lam * frob A (mix Wt B)) + lam ^ 2 * mnormSq Wt A) := by
    rw [hlam]
    have h1 : ρ ≠ 0 := by linarith
    have h2 : ρ - 1 ≠ 0 := by linarith
    field_simp
    ring
  nlinarith [mul_nonneg hk.le hnn, key]
