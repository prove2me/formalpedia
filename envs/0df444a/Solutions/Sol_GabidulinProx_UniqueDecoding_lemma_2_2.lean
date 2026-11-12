-- Prove2me | solution 1 for GabidulinProx.UniqueDecoding.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:41:33.318758+00:00
-- url     : https://prove2.me/submissions/2bcaef82-ee08-4cdf-bb40-6cde53aa15bc

import Mathlib
import Definitions.Def_GabidulinProx_UniqueDecoding_Polynomials
import Definitions.Def_GabidulinProx_UniqueDecoding_RankMetric
import Definitions.Def_GabidulinProx_UniqueDecoding_Codes

section
set_option autoImplicit false

namespace GabidulinProx.Dev.Moore

open GabidulinProx.UniqueDecoding

lemma eval_linearized {R : Type*} [CommSemiring R] (q : ℕ) {k : ℕ} (c : Fin k → R) (x : R) :
    (linearized q c).eval x = ∑ i, c i * x ^ (q ^ i.val) := by
  simp [linearized, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

lemma add_pow_card_pow (K L : Type*) [Field K] [Fintype K] [Field L] [Algebra K L]
    (i : ℕ) (x y : L) :
    (x + y) ^ (Fintype.card K) ^ i = x ^ (Fintype.card K) ^ i + y ^ (Fintype.card K) ^ i := by
  have hp : CharP K (ringChar K) := ringChar.charP K
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  obtain ⟨m, -, hm⟩ := FiniteField.card K (ringChar K)
  rw [hm, ← pow_mul]
  exact add_pow_char_pow x y _ _

/-- Evaluation of the q-polynomial with coefficients `c`, as a `K`-linear map. -/
noncomputable def evalLin (K : Type*) {L : Type*} [Field K] [Fintype K] [Field L] [Algebra K L]
    {k : ℕ} (c : Fin k → L) : L →ₗ[K] L where
  toFun x := ∑ i, c i * x ^ (Fintype.card K) ^ i.val
  map_add' x y := by
    simp only [add_pow_card_pow K L, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Algebra.smul_def, mul_pow, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_pow, FiniteField.pow_card_pow]; ring

lemma evalLin_apply (K : Type*) {L : Type*} [Field K] [Fintype K] [Field L] [Algebra K L]
    {k : ℕ} (c : Fin k → L) (x : L) :
    evalLin K c x = (linearized (Fintype.card K) c).eval x := by
  rw [eval_linearized]; rfl

lemma coeff_linearized {R : Type*} [CommSemiring R] (q : ℕ) (hq : 2 ≤ q) {k : ℕ}
    (c : Fin k → R) (i : Fin k) : (linearized q c).coeff (q ^ i.val) = c i := by
  simp only [linearized, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg]
    intro h
    exact hj (Fin.ext (Nat.pow_right_injective hq h))
  · simp

lemma natDegree_linearized_le {R : Type*} [CommSemiring R] (q : ℕ) (hq : 1 ≤ q) {k : ℕ}
    (hk : 1 ≤ k) (c : Fin k → R) : (linearized q c).natDegree ≤ q ^ (k - 1) := by
  unfold linearized
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  refine (Polynomial.natDegree_monomial_le _).trans ?_
  exact Nat.pow_le_pow_right hq (by omega)

lemma card_ge_two (K : Type*) [Field K] [Fintype K] : 2 ≤ Fintype.card K :=
  Fintype.one_lt_card

/-- The Moore matrix is injective on `L^n`. -/
lemma moore_ker {K L : Type*} [Field K] [Fintype K] [Field L] [Algebra K L] {n : ℕ}
    (hn : 1 ≤ n) (α : Fin n → L) (hα : LinearIndependent K α) (c : Fin n → L)
    (h : ∀ r, ∑ i, α r ^ (Fintype.card K) ^ i.val * c i = 0) : c = 0 := by
  classical
  by_contra hc
  set q := Fintype.card K with hq
  have hq2 : 2 ≤ q := card_ge_two K
  set g := linearized q c with hg
  have hg0 : g ≠ 0 := by
    intro h0
    apply hc
    funext i
    have := coeff_linearized q hq2 c i
    rw [← hg, h0] at this
    simpa using this.symm
  have hker : Submodule.span K (Set.range α) ≤ LinearMap.ker (evalLin K c) := by
    rw [Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    show evalLin K c (α r) = 0
    have := h r
    simpa [evalLin, mul_comm] using this
  let φ : (Fin n → K) → L := fun v => ∑ j, v j • α j
  have hφinj : Function.Injective φ := by
    intro v w hvw
    have h1 : ∑ j, (v j - w j) • α j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr hvw
    have := Fintype.linearIndependent_iff.mp hα (fun j => v j - w j) h1
    funext j
    exact sub_eq_zero.mp (this j)
  have hφroot : ∀ v, g.eval (φ v) = 0 := by
    intro v
    have hmem : φ v ∈ Submodule.span K (Set.range α) :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have := hker hmem
    rw [LinearMap.mem_ker, evalLin_apply] at this
    exact this
  have hcard := Polynomial.card_le_degree_of_subset_roots
    (p := g) (Z := Finset.univ.image φ) (by
      intro x hx
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
      exact (Polynomial.mem_roots hg0).mpr (hφroot v))
  rw [Finset.card_image_of_injective _ hφinj] at hcard
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ← hq] at hcard
  have hd : g.natDegree ≤ q ^ (n - 1) := natDegree_linearized_le q (by omega) hn c
  have : q ^ (n - 1) < q ^ n := Nat.pow_lt_pow_right (by omega) (by omega)
  omega

lemma moore_eval {K L T : Type*} [Field K] [Fintype K] [Field L] [Algebra K L] [Field T]
    [Algebra L T] {n : ℕ} (α : Fin n → L) (c : Fin n → T) (r : Fin n) :
    (linearized (Fintype.card K) c).eval (algebraMap L T (α r)) =
      ((Matrix.of fun r i : Fin n => α r ^ (Fintype.card K) ^ i.val).map (algebraMap L T)).mulVec
        c r := by
  rw [eval_linearized]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, map_pow]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GabidulinProx.Dev.Moore

namespace GabidulinProx.UniqueDecoding

open GabidulinProx.Dev.Moore

theorem chk_lemma_2_2 {K L T : Type*} [Field K] [Fintype K] [Field L] [Fintype L]
    [Algebra K L] [Field T] [Algebra L T] {n : ℕ}
    (hn : 1 ≤ n) (α : Fin n → L) (hα : LinearIndependent K α) (y : Fin n → T) :
    ∃! f : Polynomial T, IsLinearized (Fintype.card K) n f ∧
      ∀ r, f.eval (algebraMap L T (α r)) = y r := by
  classical
  set M : Matrix (Fin n) (Fin n) L := Matrix.of fun r i => α r ^ (Fintype.card K) ^ i.val
    with hMdef
  have hM : IsUnit M := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro c d hcd
    have h0 : M.mulVec (c - d) = 0 := by rw [Matrix.mulVec_sub, hcd, sub_self]
    have := moore_ker (K := K) hn α hα (c - d) (fun r => by
      have := congrFun h0 r
      simpa [hMdef, Matrix.mulVec, dotProduct] using this)
    exact sub_eq_zero.mp this
  have hN : IsUnit (M.map (algebraMap L T)) := by
    have := hM.map (algebraMap L T).mapMatrix
    exact this
  have hsurj := Matrix.mulVec_surjective_iff_isUnit.mpr hN
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hN
  obtain ⟨c, hc⟩ := hsurj y
  refine ⟨linearized (Fintype.card K) c, ⟨⟨c, rfl⟩, fun r => ?_⟩, ?_⟩
  · rw [moore_eval, hc]
  · rintro f ⟨⟨d, rfl⟩, hev⟩
    have : d = c := by
      apply hinj
      rw [hc]
      funext r
      rw [← moore_eval, hev]
    rw [this]

end GabidulinProx.UniqueDecoding
end

theorem solution : type_of% @GabidulinProx.UniqueDecoding.chk_lemma_2_2 := @GabidulinProx.UniqueDecoding.chk_lemma_2_2
