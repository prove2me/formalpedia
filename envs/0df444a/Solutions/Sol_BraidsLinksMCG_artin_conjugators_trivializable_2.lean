-- Prove2me | solution 2 for BraidsLinksMCG.artin_conjugators_trivializable
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T00:04:11.009865+00:00
-- url     : https://prove2.me/submissions/4360a70e-8d3d-483f-8676-b0575b3354fb

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Theorems.Thm_BraidsLinksMCG_artin_action_conj_perm
import Theorems.Thm_BraidsLinksMCG_artin_action_fixes_word
import Theorems.Thm_BraidsLinksMCG_braid_perm_hom
import Theorems.Thm_BraidsLinksMCG_artin_hurwitz_norm_reduction

/-!
`artin_conjugators_trivializable` from the Hurwitz-form descent step.
-/

namespace HurwitzTriv

open BraidsLinksMCG

/-- A product of positive letters is the class of the evident word. -/
private lemma prod_of_map {α : Type*} (L : List α) :
    (L.map fun a => FreeGroup.of a).prod = FreeGroup.mk (L.map fun a => (a, true)) := by
  induction L with
  | nil => rfl
  | cons a t ih =>
      rw [List.map_cons, List.prod_cons, ih, List.map_cons,
        show (FreeGroup.of a : FreeGroup α) = FreeGroup.mk [(a, true)] from rfl,
        FreeGroup.mul_mk]
      rfl

/-- A word all of whose letters are positive admits no cancellation. -/
private lemma isReduced_map_true {α : Type*} : ∀ L : List α,
    FreeGroup.IsReduced (L.map fun a => (a, true))
  | [] => FreeGroup.IsReduced.nil
  | [_] => FreeGroup.IsReduced.singleton
  | _ :: b :: t => by
      rw [List.map_cons, List.map_cons, FreeGroup.isReduced_cons_cons]
      exact ⟨fun _ => rfl, isReduced_map_true (b :: t)⟩

private lemma prod_ofFn_of {n : ℕ} (g : Fin n → Fin n) :
    (List.ofFn fun i : Fin n => FreeGroup.of (g i)).prod
      = FreeGroup.mk ((List.ofFn g).map fun a => (a, true)) := by
  rw [show (List.ofFn fun i : Fin n => FreeGroup.of (g i))
        = (List.ofFn g).map (fun a => FreeGroup.of a) by rw [List.map_ofFn]; rfl]
  exact prod_of_map _

/-- Only the identity permutation leaves `x₁ ⋯ xₙ` unchanged. -/
private lemma perm_eq_of_prod_eq {n : ℕ} (nu : Equiv.Perm (Fin n))
    (h : (List.ofFn fun i : Fin n => FreeGroup.of (nu i)).prod = freeWordProd n) :
    ∀ i, nu i = i := by
  have h2 : FreeGroup.mk ((List.ofFn (fun i : Fin n => nu i)).map fun a => (a, true))
      = FreeGroup.mk ((List.ofFn (fun i : Fin n => i)).map fun a => (a, true)) := by
    rw [← prod_ofFn_of, ← prod_ofFn_of]
    exact h
  have h3 := FreeGroup.reduce.sound h2
  rw [(isReduced_map_true _).reduce_eq, (isReduced_map_true _).reduce_eq] at h3
  rw [List.map_ofFn, List.map_ofFn] at h3
  have h4 := List.ofFn_inj.1 h3
  intro i
  exact congrArg Prod.fst (congrFun h4 i)

theorem _root_.solution (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (beta : FreeGroup (Fin n) →* FreeGroup (Fin n))
    (hconj : ∃ mu : Equiv.Perm (Fin n), ∃ A : Fin n → FreeGroup (Fin n),
        ∀ i : Fin n, beta (FreeGroup.of i) = A i * FreeGroup.of (mu i) * (A i)⁻¹)
    (hword : beta (freeWordProd n) = freeWordProd n) :
    ∃ b : ArtinBraidGroup n, ∃ nu : Equiv.Perm (Fin n),
      ∀ i : Fin n, xi b (beta (FreeGroup.of i)) = FreeGroup.of (nu i) := by
  obtain ⟨pi, hpi⟩ := braid_perm_hom n
  have key : ∀ N : ℕ, ∀ gamma : FreeGroup (Fin n) →* FreeGroup (Fin n),
      (∑ i : Fin n, FreeGroup.norm (gamma (FreeGroup.of i))) ≤ N →
      (∃ mu : Equiv.Perm (Fin n), ∃ A : Fin n → FreeGroup (Fin n),
          ∀ i : Fin n, gamma (FreeGroup.of i) = A i * FreeGroup.of (mu i) * (A i)⁻¹) →
      gamma (freeWordProd n) = freeWordProd n →
      ∃ c : ArtinBraidGroup n, ∃ nu : Equiv.Perm (Fin n),
        ∀ i : Fin n, gamma (xi c (FreeGroup.of i)) = FreeGroup.of (nu i) := by
    intro N
    induction N with
    | zero =>
        intro gamma hle hc hw
        by_cases hp : ∃ nu : Equiv.Perm (Fin n),
            ∀ i : Fin n, gamma (FreeGroup.of i) = FreeGroup.of (nu i)
        · obtain ⟨nu, hnu⟩ := hp
          exact ⟨1, nu, fun i => by simpa using hnu i⟩
        · obtain ⟨c, hcc⟩ := artin_hurwitz_norm_reduction n xi hxi gamma hc hw hp
          omega
    | succ N ih =>
        intro gamma hle hc hw
        by_cases hp : ∃ nu : Equiv.Perm (Fin n),
            ∀ i : Fin n, gamma (FreeGroup.of i) = FreeGroup.of (nu i)
        · obtain ⟨nu, hnu⟩ := hp
          exact ⟨1, nu, fun i => by simpa using hnu i⟩
        · obtain ⟨c, hcc⟩ := artin_hurwitz_norm_reduction n xi hxi gamma hc hw hp
          obtain ⟨mu, A, hA⟩ := hc
          have hconjc : ∀ i : Fin n, ∃ C : FreeGroup (Fin n),
              xi c (FreeGroup.of i) = C * FreeGroup.of (pi c i) * C⁻¹ :=
            fun i => artin_action_conj_perm n xi hxi pi hpi c i
          choose C hC using hconjc
          have happ : ∀ i : Fin n,
              (gamma.comp (xi c).toMonoidHom) (FreeGroup.of i) = gamma (xi c (FreeGroup.of i)) :=
            fun _ => rfl
          have hle' : (∑ i : Fin n,
              FreeGroup.norm ((gamma.comp (xi c).toMonoidHom) (FreeGroup.of i))) ≤ N := by
            simp only [happ]
            omega
          have hc' : ∃ mu' : Equiv.Perm (Fin n), ∃ A' : Fin n → FreeGroup (Fin n),
              ∀ i : Fin n, (gamma.comp (xi c).toMonoidHom) (FreeGroup.of i)
                = A' i * FreeGroup.of (mu' i) * (A' i)⁻¹ := by
            refine ⟨(pi c).trans mu, fun i => gamma (C i) * A (pi c i), fun i => ?_⟩
            rw [happ, hC i, map_mul, map_mul, map_inv, hA (pi c i)]
            simp [mul_assoc]
          have hw' : (gamma.comp (xi c).toMonoidHom) (freeWordProd n) = freeWordProd n := by
            show gamma (xi c (freeWordProd n)) = freeWordProd n
            rw [artin_action_fixes_word n xi hxi c]
            exact hw
          obtain ⟨c₁, nu, hnu⟩ := ih (gamma.comp (xi c).toMonoidHom) hle' hc' hw'
          refine ⟨c * c₁, nu, fun i => ?_⟩
          rw [map_mul, MulAut.mul_apply]
          exact hnu i
  obtain ⟨c, nu, hnu⟩ := key (∑ i : Fin n, FreeGroup.norm (beta (FreeGroup.of i))) beta
    le_rfl hconj hword
  have hfix : beta (xi c (freeWordProd n)) = freeWordProd n := by
    rw [artin_action_fixes_word n xi hxi c]; exact hword
  have hmap : beta (xi c (freeWordProd n))
      = (List.ofFn fun i : Fin n => FreeGroup.of (nu i)).prod := by
    have hfun : (⇑(beta.comp (xi c).toMonoidHom) ∘ fun j : Fin n => FreeGroup.of j)
        = fun i : Fin n => FreeGroup.of (nu i) := funext fun j => hnu j
    show (beta.comp (xi c).toMonoidHom) (freeWordProd n) = _
    rw [freeWordProd, map_list_prod, List.map_ofFn, hfun]
  have hnuid : ∀ i, nu i = i := perm_eq_of_prod_eq nu (hmap ▸ hfix)
  have hcomp : ∀ w, beta (xi c w) = w := by
    have hext : beta.comp (xi c).toMonoidHom = MonoidHom.id (FreeGroup (Fin n)) := by
      refine FreeGroup.ext_hom _ _ fun i => ?_
      show beta (xi c (FreeGroup.of i)) = FreeGroup.of i
      rw [hnu i, hnuid i]
    intro w
    exact DFunLike.congr_fun hext w
  have hbeta : ∀ y, beta y = (xi c).symm y := by
    intro y
    have h := hcomp ((xi c).symm y)
    rwa [MulEquiv.apply_symm_apply] at h
  refine ⟨c, 1, fun i => ?_⟩
  rw [hbeta, MulEquiv.apply_symm_apply]
  rfl

end HurwitzTriv

#print axioms solution
