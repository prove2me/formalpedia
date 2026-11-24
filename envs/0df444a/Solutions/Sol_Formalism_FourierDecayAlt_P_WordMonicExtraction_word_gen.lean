-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordMonicExtraction.word_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:25.523258+00:00
-- url     : https://prove2.me/submissions/425684a6-c79a-4f6f-8ce3-9054cdf60462

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_Fw_concat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.WordMonicExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
section
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]
end
section
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]
private theorem sumsnoc_lemma_2 {K m : ℕ} {β : Type} [AddCommMonoid β] (f : (Fin (K + 1) → Fin m) → β) :
    ∑ j, f j = ∑ jl : Fin m, ∑ j' : Fin K → Fin m, f (Fin.snoc j' jl) := by
  rw [← (Fin.snocEquiv (fun _ => Fin m)).sum_comp f, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  congr 1
private theorem sumlin_lemma_3 {ι κ : Type} [Fintype ι] [Fintype κ] (P : κ → ℝ) (L : ι → ℝ)
    (F G : ι → κ → ℂ) :
    ∑ i, ∑ k, ((P k * L i : ℝ) : ℂ) * (F i k - G i k) =
      ∑ i, ((L i : ℝ) : ℂ) * ((∑ k, ((P k : ℝ) : ℂ) * F i k) - ∑ k, ((P k : ℝ) : ℂ) * G i k) := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  push_cast
  ring
end
end Formalism.FourierDecayAlt.P.WordMonicExtraction
namespace Formalism.FourierDecayAlt.P
open Finset Polynomial Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.WordMonicExtraction
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordMonicExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]
namespace Formalism.FourierDecayAlt.P.WordMonicExtraction
theorem _root_.solution (Ξ : Sesq M) (d : ℕ) (X X' : M) : ∀ (K : ℕ) (dat : Fin K → Dat R)
    (grid : Fin K → Fin (d + 1) → ℝ) (c : Fin K → ℂ),
    (∀ a (Q Q' : R), ∑ i, ((lagCo (grid a) i : ℝ) : ℂ) *
      letterVal Ξ (dat a) (grid a i) (Q • X) (Q' • X') = c a * Ξ (Q • X) (Q' • X')) →
    ∀ Q Q' : R, (∏ a, c a) * Ξ (Q • X) (Q' • X') =
      ∑ j : Fin K → Fin (d + 1), ((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) *
        Fw Ξ (Q • X) (Q' • X') (List.ofFn fun a => (dat a, grid a (j a))) 1 1 := by
  intro K
  induction K with
  | zero =>
    intro dat grid c _ Q Q'
    simp [Fw]
  | succ K ih =>
    intro dat grid c hc Q Q'
    have ih' := ih (fun a => dat a.castSucc) (fun a => grid a.castSucc) (fun a => c a.castSucc)
      (fun a => hc a.castSucc)
    beta_reduce at ih'
    have hl := hc (Fin.last K) Q Q'
    unfold letterVal at hl
    simp only [← mul_smul] at hl
    rw [sumsnoc_lemma_2]
    simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, List.ofFn_succ',
      List.concat_eq_append, Fw_concat]
    simp only [← mul_smul]
    rw [sumlin_lemma_3]
    simp only [← ih']
    calc (∏ a : Fin K, c a.castSucc) * c (Fin.last K) * Ξ (Q • X) (Q' • X') =
        (∏ a : Fin K, c a.castSucc) * (c (Fin.last K) * Ξ (Q • X) (Q' • X')) := by ring
      _ = _ := by
        rw [← hl, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
end Formalism.FourierDecayAlt.P.WordMonicExtraction
