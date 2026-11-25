-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lift_vector_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:55:28.025133+00:00
-- url     : https://prove2.me/submissions/57d242ba-7ed2-42ec-99fc-642f3902af35

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_monic_extract
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
end
end Formalism.FourierDecayAlt.P.WordMonicExtraction
namespace Formalism.FourierDecayAlt.P
open Finset Polynomial Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.WordMonicExtraction
private theorem liftvec_lemma_4 {R M V : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M]
    [Module R M] [IsScalarTower ℂ R M] [AddCommGroup V] [Module ℂ V] (ev : M →ₗ[ℂ] V) (n : ℕ)
    (X₀ : M) :
    ∀ (K : ℕ) (G : Fin K → ℝ → R) (A₀ : Fin K → Polynomial R) (c : Fin K → ℂ)
      (grid : Fin K → Fin (n + 1) → ℝ),
      (∀ a, (A₀ a).Monic ∧ (A₀ a).natDegree = n) →
      (∀ a (Y : ℝ) (Q : R), ev (G a Y • Q • X₀) = c a • ev (evR (A₀ a) Y • Q • X₀)) →
      (∀ a, Function.Injective (grid a)) →
      ∀ Q : R, (∏ a, c a) • ev (Q • X₀) =
        ∑ j : Fin K → Fin (n + 1), ((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) •
          ev ((List.ofFn fun a => G a (grid a (j a))).prod • Q • X₀) := by
  intro K
  induction K with
  | zero =>
    intro G A₀ c grid _ _ _ Q
    simp
  | succ K ih =>
    intro G A₀ c grid hA hG hg Q
    have ih' := ih (fun a => G a.castSucc) (fun a => A₀ a.castSucc) (fun a => c a.castSucc)
      (fun a => grid a.castSucc) (fun a => hA a.castSucc) (fun a => hG a.castSucc)
      (fun a => hg a.castSucc)
    beta_reduce at ih'
    rw [sumsnoc_lemma_2]
    simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, List.ofFn_succ',
      List.concat_eq_append, List.prod_append, List.prod_singleton, mul_smul]
    have inner : ∀ jl : Fin (n + 1), ∑ j' : Fin K → Fin (n + 1),
        (((∏ a : Fin K, lagCo (grid a.castSucc) (j' a)) * lagCo (grid (Fin.last K)) jl : ℝ) : ℂ) •
          ev ((List.ofFn fun a : Fin K => G a.castSucc (grid a.castSucc (j' a))).prod •
            G (Fin.last K) (grid (Fin.last K) jl) • Q • X₀) =
        ((lagCo (grid (Fin.last K)) jl : ℝ) : ℂ) •
          ((∏ a : Fin K, c a.castSucc) • ev (G (Fin.last K) (grid (Fin.last K) jl) • Q • X₀)) := by
      intro jl
      have e := ih' (G (Fin.last K) (grid (Fin.last K) jl) * Q)
      simp only [mul_smul] at e
      rw [e, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      rw [smul_smul ((lagCo (grid (Fin.last K)) jl : ℝ) : ℂ)]
      congr 1
      push_cast
      ring
    simp only [inner]
    have hm := monic_extract ev n (A₀ (Fin.last K)) (hA (Fin.last K)).1 (hA (Fin.last K)).2
      (grid (Fin.last K)) (hg (Fin.last K)) (Q • X₀)
    simp_rw [hG (Fin.last K)]
    rw [← hm, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [smul_smul]
    congr 1
    ring
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Polynomial Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.WordMonicExtraction
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.F7.LiftVectorWord := by
  unfold LiftVectorWord
  intro R M V _ _ _ _ _ _ _ _ ev n K G A₀ c grid X₀ hA hG hg
  have h := liftvec_lemma_4 ev n X₀ K G A₀ c grid hA hG hg 1
  simp only [one_smul] at h
  exact h
end Formalism.FourierDecayAlt.P
