-- Prove2me | solution 1 for GenFrameSpan.SatP.Tmap_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:22:52.051194+00:00
-- url     : https://prove2.me/submissions/76ef6b91-788a-4f7a-a60e-60094533981a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatProj
import Theorems.Thm_GenFrameSpan_SatP_res_sum
import Theorems.Thm_GenFrameSpan_SatP_prod_rename_monomial
import Theorems.Thm_GenFrameSpan_SatP_Tmap_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open GenFrameSpan
open CutKW MvPolynomial
open GenFrameSpan.SatP
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 : ℕ}
namespace GenFrameSpan.SatP
theorem _root_.solution (π : Lt → (MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (ℕ × Fin N0) ℤ))
    (h : Lt → MvPolynomial (ℕ × Fin N0) ℤ) :
    Tmap π (∏ s, rename (emb s) (h s)) = ∏ s, rename (emb s) (π s (h s)) := by
  suffices H : ∀ F : Finset Lt, ∀ h : Lt → MvPolynomial (ℕ × Fin N0) ℤ,
      (∀ s ∉ F, ∃ n, h s = monomial n 1) →
      Tmap π (∏ s, rename (emb s) (h s)) = ∏ s, rename (emb s) (π s (h s)) from
    H Finset.univ h (fun s hs => absurd (Finset.mem_univ s) hs)
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro h hh
    choose n hn using fun s => hh s (by simp)
    have : h = fun s => monomial (n s) 1 := funext hn
    subst this
    rw [prod_rename_monomial, Tmap_monomial]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [res_sum]
  | insert a F haF ih =>
    intro h hh
    have key : ∀ g : MvPolynomial (ℕ × Fin N0) ℤ,
        Tmap π (rename (emb a) g * ∏ s ∈ Finset.univ.erase a, rename (emb s) (h s)) =
          rename (emb a) (π a g) * ∏ s ∈ Finset.univ.erase a, rename (emb s) (π s (h s)) := by
      let A : MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
        Tmap π ∘ₗ LinearMap.mulRight ℤ (∏ s ∈ Finset.univ.erase a, rename (emb s) (h s)) ∘ₗ
          (rename (emb a)).toLinearMap
      let B : MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
        LinearMap.mulRight ℤ (∏ s ∈ Finset.univ.erase a, rename (emb s) (π s (h s))) ∘ₗ
          (rename (emb a)).toLinearMap ∘ₗ π a
      have hAB : A = B := by
        refine (basisMonomials (ℕ × Fin N0) ℤ).ext fun u => ?_
        rw [coe_basisMonomials]
        simp only [A, B, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
          AlgHom.toLinearMap_apply]
        have h1 := ih (Function.update h a (monomial u 1)) (by
          intro s hs
          by_cases hsa : s = a
          · subst hsa
            exact ⟨u, by simp⟩
          · rw [Function.update_of_ne hsa]
            exact hh s (by simp [hsa, hs]))
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a),
          ← Finset.mul_prod_erase _ (fun s => rename (emb s) (π s (Function.update h a (monomial u 1) s)))
            (Finset.mem_univ a)] at h1
        simp only [Function.update_self] at h1
        have e1 : ∏ s ∈ Finset.univ.erase a, rename (emb s) (Function.update h a (monomial u 1) s) =
            ∏ s ∈ Finset.univ.erase a, rename (emb s) (h s) :=
          Finset.prod_congr rfl fun s hs => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
        have e2 : ∏ s ∈ Finset.univ.erase a,
            rename (emb s) (π s (Function.update h a (monomial u 1) s)) =
            ∏ s ∈ Finset.univ.erase a, rename (emb s) (π s (h s)) :=
          Finset.prod_congr rfl fun s hs => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
        rw [e1, e2] at h1
        exact h1
      intro g
      exact LinearMap.congr_fun hAB g
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a),
      ← Finset.mul_prod_erase _ (fun s => rename (emb s) (π s (h s))) (Finset.mem_univ a)]
    exact key (h a)
end GenFrameSpan.SatP
