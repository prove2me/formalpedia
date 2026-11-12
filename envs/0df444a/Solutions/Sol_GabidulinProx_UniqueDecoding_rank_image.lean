-- Prove2me | solution 1 for GabidulinProx.UniqueDecoding.rank_image
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:41:32.913055+00:00
-- url     : https://prove2.me/submissions/ad766614-5700-4118-a22d-0eda089a55be

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

end GabidulinProx.Dev.Moore

namespace GabidulinProx.UniqueDecoding

open GabidulinProx.Dev.Moore

theorem chk_rank_image {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L]
    [Algebra K L] {n : ℕ} (hn : 1 ≤ n) (α : Fin n → L) (hα : LinearIndependent K α)
    (y₀ y₁ : Fin n → L) (f₀ f₁ : Polynomial L)
    (hf₀ : IsLinearized (Fintype.card K) n f₀)
    (hf₁ : IsLinearized (Fintype.card K) n f₁)
    (hy₀ : ∀ r, f₀.eval (α r) = y₀ r) (hy₁ : ∀ r, f₁.eval (α r) = y₁ r) :
    wordRank K y₀ = Module.finrank K (Submodule.span K
      (f₀.eval '' (Submodule.span K (Set.range α) : Set L))) ∧
    pairRank K y₀ y₁ = Module.finrank K (Submodule.span K
      ((fun x => (f₀.eval x, f₁.eval x)) '' (Submodule.span K (Set.range α) : Set L))) := by
  obtain ⟨c₀, rfl⟩ := hf₀
  obtain ⟨c₁, rfl⟩ := hf₁
  have key : ∀ {M : Type _} [AddCommGroup M] [Module K M] (ℓ : L →ₗ[K] M) (y : Fin n → M),
      (∀ r, ℓ (α r) = y r) →
      Submodule.span K (Set.range y) =
        Submodule.span K (ℓ '' (Submodule.span K (Set.range α) : Set L)) := by
    intro M _ _ ℓ y h
    rw [← Submodule.map_coe, Submodule.span_eq, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext r
    exact (h r).symm
  have e₀ : (fun x => Polynomial.eval x (linearized (Fintype.card K) c₀)) =
      ⇑(evalLin K c₀) := funext fun x => (evalLin_apply K c₀ x).symm
  have e₁ : (fun x => (Polynomial.eval x (linearized (Fintype.card K) c₀),
      Polynomial.eval x (linearized (Fintype.card K) c₁))) =
      ⇑((evalLin K c₀).prod (evalLin K c₁)) := funext fun x => by
    show _ = (evalLin K c₀ x, evalLin K c₁ x)
    rw [evalLin_apply, evalLin_apply]
  constructor
  · have := key (evalLin K c₀) y₀ (fun r => by rw [evalLin_apply]; exact hy₀ r)
    unfold wordRank
    rw [this, show (Polynomial.eval · (linearized (Fintype.card K) c₀)) = _ from e₀]
  · have := key ((evalLin K c₀).prod (evalLin K c₁)) (fun r => (y₀ r, y₁ r)) (fun r => by
      show (evalLin K c₀ (α r), evalLin K c₁ (α r)) = _
      rw [evalLin_apply, evalLin_apply, hy₀ r, hy₁ r])
    unfold pairRank wordRank
    rw [this, e₁]

end GabidulinProx.UniqueDecoding
end

theorem solution : type_of% @GabidulinProx.UniqueDecoding.chk_rank_image := @GabidulinProx.UniqueDecoding.chk_rank_image
