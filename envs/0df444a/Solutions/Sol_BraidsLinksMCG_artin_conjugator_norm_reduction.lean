-- Prove2me | solution 1 for BraidsLinksMCG.artin_conjugator_norm_reduction
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T10:30:03.365988+00:00
-- url     : https://prove2.me/submissions/5c0d2cff-ca4a-4ce8-b6dd-f71e42467d3a

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Theorems.Thm_BraidsLinksMCG_artin_action_conj_perm
import Theorems.Thm_BraidsLinksMCG_artin_action_fixes_word
import Theorems.Thm_BraidsLinksMCG_braid_perm_hom
import Theorems.Thm_BraidsLinksMCG_artin_hurwitz_norm_reduction

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false

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

theorem triv_aux (n : ℕ)
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



/-- Selective abelianisation at the generator `m`. -/
def selAb {n : ℕ} (m : Fin n) : FreeGroup (Fin n) →* Multiplicative ℤ :=
  FreeGroup.lift fun j => if j = m then Multiplicative.ofAdd 1 else 1

lemma selAb_conj {n : ℕ} (m : Fin n) (A : FreeGroup (Fin n)) :
    selAb m (A * FreeGroup.of m * A⁻¹) = Multiplicative.ofAdd 1 := by
  simp [selAb, mul_comm]

lemma norm_pos_of_conj {n : ℕ} (m : Fin n) (A : FreeGroup (Fin n)) :
    1 ≤ FreeGroup.norm (A * FreeGroup.of m * A⁻¹) := by
  rcases Nat.eq_zero_or_pos (FreeGroup.norm (A * FreeGroup.of m * A⁻¹)) with h | h
  · rw [FreeGroup.norm_eq_zero] at h
    have := selAb_conj m A
    rw [h, map_one] at this
    exact absurd this (by decide)
  · exact h

lemma eq_of_of_norm_one {n : ℕ} (m : Fin n) (A : FreeGroup (Fin n))
    (h : FreeGroup.norm (A * FreeGroup.of m * A⁻¹) = 1) :
    A * FreeGroup.of m * A⁻¹ = FreeGroup.of m := by
  set g := A * FreeGroup.of m * A⁻¹ with hg
  unfold FreeGroup.norm at h
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 h
  have hgm : g = FreeGroup.mk [a] := by rw [← ha, FreeGroup.mk_toWord]
  have hs := selAb_conj m A
  rw [← hg, hgm] at hs
  obtain ⟨j, b⟩ := a
  have hsel : selAb m (FreeGroup.mk [(j, b)]) = if b then selAb m (FreeGroup.of j) else (selAb m (FreeGroup.of j))⁻¹ := by
    cases b
    · have : FreeGroup.mk [(j, false)] = (FreeGroup.of j)⁻¹ := by
        rw [FreeGroup.of, FreeGroup.inv_mk]; rfl
      rw [this, map_inv]; rfl
    · rfl
  rw [hsel] at hs
  by_cases hj : j = m
  · subst hj
    cases b
    · simp [selAb] at hs
      exact absurd hs (by decide)
    · rw [hgm]; rfl
  · cases b <;> simp [selAb, hj] at hs <;> exact absurd hs (by decide)

namespace BraidsLinksMCG

theorem _root_.solution (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (beta : FreeGroup (Fin n) →* FreeGroup (Fin n))
    (hconj : ∃ mu : Equiv.Perm (Fin n), ∃ A : Fin n → FreeGroup (Fin n),
        ∀ i : Fin n, beta (FreeGroup.of i) = A i * FreeGroup.of (mu i) * (A i)⁻¹)
    (hword : beta (freeWordProd n) = freeWordProd n)
    (hnotperm : ¬ ∃ nu : Equiv.Perm (Fin n),
        ∀ i : Fin n, beta (FreeGroup.of i) = FreeGroup.of (nu i)) :
    ∃ c : ArtinBraidGroup n,
      (∑ i : Fin n, FreeGroup.norm (((xi c).toMonoidHom.comp beta) (FreeGroup.of i)))
        < ∑ i : Fin n, FreeGroup.norm (beta (FreeGroup.of i)) := by
  obtain ⟨b, nu, hnu⟩ := HurwitzTriv.triv_aux n xi hxi beta hconj hword
  refine ⟨b, ?_⟩
  have hl : (∑ i : Fin n, FreeGroup.norm (((xi b).toMonoidHom.comp beta) (FreeGroup.of i))) = n := by
    have : ∀ i : Fin n, FreeGroup.norm (((xi b).toMonoidHom.comp beta) (FreeGroup.of i)) = 1 := by
      intro i
      show FreeGroup.norm (xi b (beta (FreeGroup.of i))) = 1
      rw [hnu i, FreeGroup.norm_of]
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    simp
  rw [hl]
  obtain ⟨mu, A, hA⟩ := hconj
  have hge : ∀ i : Fin n, 1 ≤ FreeGroup.norm (beta (FreeGroup.of i)) := by
    intro i; rw [hA i]; exact norm_pos_of_conj _ _
  have hex : ∃ i : Fin n, 2 ≤ FreeGroup.norm (beta (FreeGroup.of i)) := by
    by_contra hno
    push Not at hno
    apply hnotperm
    refine ⟨mu, fun i => ?_⟩
    have h1 : FreeGroup.norm (beta (FreeGroup.of i)) = 1 := by
      have := hge i; have := hno i; omega
    rw [hA i] at h1 ⊢
    exact eq_of_of_norm_one _ _ h1
  obtain ⟨i0, hi0⟩ := hex
  have hsum : (∑ i : Fin n, 1) < ∑ i : Fin n, FreeGroup.norm (beta (FreeGroup.of i)) :=
    Finset.sum_lt_sum (fun i _ => hge i) ⟨i0, Finset.mem_univ _, by omega⟩
  simpa using hsum

end BraidsLinksMCG

#print axioms solution
