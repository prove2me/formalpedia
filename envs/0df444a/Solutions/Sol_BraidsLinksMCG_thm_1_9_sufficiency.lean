-- Prove2me | solution 1 for BraidsLinksMCG.thm_1_9_sufficiency
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T20:29:38.978491+00:00
-- url     : https://prove2.me/submissions/489ccf6b-ddd8-4502-a98b-59ada1323939

import Theorems.Thm_BraidsLinksMCG_artin_conjugators_trivializable
import Theorems.Thm_BraidsLinksMCG_artin_action_fixes_word
import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG

namespace Suff

variable {α : Type*} [DecidableEq α]

lemma mk_eq_of_reduced {L M : List (α × Bool)} (hL : FreeGroup.IsReduced L)
    (hM : FreeGroup.IsReduced M) (h : FreeGroup.mk L = FreeGroup.mk M) : L = M := by
  obtain ⟨N, h1, h2⟩ := FreeGroup.Red.exact.1 h
  rw [hL.red_iff_eq] at h1
  rw [hM.red_iff_eq] at h2
  rw [← h1, ← h2]

/-- A word all of whose letters are positive is reduced. -/
lemma isReduced_positive (l : List α) :
    FreeGroup.IsReduced (l.map (fun x => (x, true))) := by
  induction l with
  | nil => exact FreeGroup.IsReduced.nil
  | cons a l ih =>
    cases l with
    | nil => exact FreeGroup.IsReduced.singleton
    | cons b l =>
      rw [List.map_cons, List.map_cons, FreeGroup.isReduced_cons_cons]
      exact ⟨fun _ => rfl, by simpa using ih⟩

lemma prod_of_map (l : List α) :
    (l.map FreeGroup.of).prod = FreeGroup.mk (l.map (fun x => (x, true))) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons]
    show FreeGroup.mk [(a, true)] * FreeGroup.mk (List.map (fun x => (x, true)) l) = _
    rw [FreeGroup.mul_mk]
    rfl

/-- In a free group, a permuted product of distinct generators determines the
permutation. -/
theorem perm_of_prod_eq {n : ℕ} (mu : Equiv.Perm (Fin n))
    (h : (List.ofFn fun j : Fin n => FreeGroup.of (mu j)).prod
       = (List.ofFn fun j : Fin n => FreeGroup.of j).prod) : mu = 1 := by
  have e1 : (List.ofFn fun j : Fin n => FreeGroup.of (mu j))
      = (List.ofFn mu).map FreeGroup.of := by
    rw [List.map_ofFn]; rfl
  have e2 : (List.ofFn fun j : Fin n => FreeGroup.of j)
      = (List.ofFn (id : Fin n → Fin n)).map FreeGroup.of := by
    rw [List.map_ofFn]; rfl
  rw [e1, e2, prod_of_map, prod_of_map] at h
  have hlist := mk_eq_of_reduced (isReduced_positive _) (isReduced_positive _) h
  have hinj : Function.Injective (fun x : Fin n => (x, true)) :=
    fun a b hab => congrArg Prod.fst hab
  have hofn : List.ofFn (⇑mu) = List.ofFn (id : Fin n → Fin n) :=
    List.map_injective_iff.mpr hinj hlist
  have hfun : (⇑mu) = (id : Fin n → Fin n) := List.ofFn_injective hofn
  exact Equiv.ext fun j => congrFun hfun j



end Suff

theorem _root_.solution (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (beta : FreeGroup (Fin n) →* FreeGroup (Fin n))
    (hconj : ∃ mu : Equiv.Perm (Fin n), ∃ A : Fin n → FreeGroup (Fin n),
        ∀ i : Fin n, beta (FreeGroup.of i) = A i * FreeGroup.of (mu i) * (A i)⁻¹)
    (hword : beta (freeWordProd n) = freeWordProd n) :
    ∃ b : ArtinBraidGroup n, ∀ w : FreeGroup (Fin n), xi b w = beta w := by
  obtain ⟨b, nu, hb⟩ :=
    BraidsLinksMCG.artin_conjugators_trivializable n xi hxi beta hconj hword
  -- the composite `xi b ∘ beta` is the permutation automorphism of `nu`
  have hgamma : ∀ i : Fin n, ((xi b).toMonoidHom.comp beta) (FreeGroup.of i)
      = FreeGroup.of (nu i) := hb
  -- it fixes the word `x₁ ⋯ xₙ`
  have hfix : ((xi b).toMonoidHom.comp beta) (freeWordProd n) = freeWordProd n := by
    show xi b (beta (freeWordProd n)) = freeWordProd n
    rw [hword]
    exact BraidsLinksMCG.artin_action_fixes_word n xi hxi b
  -- evaluate that fixing on the explicit product
  have hprod : (List.ofFn fun j : Fin n => FreeGroup.of (nu j)).prod
      = (List.ofFn fun j : Fin n => FreeGroup.of j).prod := by
    have e : ((xi b).toMonoidHom.comp beta) (freeWordProd n)
        = (List.ofFn fun j : Fin n => FreeGroup.of (nu j)).prod := by
      show ((xi b).toMonoidHom.comp beta)
        ((List.ofFn fun j : Fin n => FreeGroup.of j).prod) = _
      rw [map_list_prod, List.map_ofFn]
      refine congrArg List.prod (congrArg List.ofFn ?_)
      funext j
      exact hgamma j
    rw [← e, hfix]
    rfl
  have hnu : nu = 1 := Suff.perm_of_prod_eq nu hprod
  -- so the composite is the identity on generators, hence everywhere
  have hid : (xi b).toMonoidHom.comp beta = MonoidHom.id (FreeGroup (Fin n)) := by
    apply FreeGroup.ext_hom
    intro i
    rw [hgamma i, hnu]
    rfl
  refine ⟨b⁻¹, fun w => ?_⟩
  have h1 : xi b (beta w) = w := DFunLike.congr_fun hid w
  calc xi b⁻¹ w = (xi b)⁻¹ w := by rw [map_inv]
    _ = (xi b).symm w := rfl
    _ = (xi b).symm (xi b (beta w)) := by rw [h1]
    _ = beta w := (xi b).symm_apply_apply _

#print axioms solution
