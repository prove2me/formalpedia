-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.rr_roots_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:23.801703+00:00
-- url     : https://prove2.me/submissions/47dad238-2114-49ee-a637-ac1b8000cd90

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_RestrictRoots
import Theorems.Thm_Formalism_GaloisIrreducibility_rr_charpoly_compl
import Theorems.Thm_Formalism_GaloisIrreducibility_rr_roots_of_nilp
import Theorems.Thm_Formalism_GaloisIrreducibility_rr_nilp_pow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.GaloisIrreducibility
open Module Polynomial
section SlopeTestRemainingChoices
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end SlopeTestRemainingChoices
private lemma coe_restrict_pow_apply' {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (A : Module.End K V) (S : Submodule K V) (hS : ∀ x ∈ S, A x ∈ S) (k : ℕ) (x : S) :
    (((A.restrict hS) ^ k) x : V) = (A ^ k) x := by
  induction k with
  | zero => simp
  | succ k ihk =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply,
      LinearMap.restrict_coe_apply, ihk]
end Formalism.GaloisIrreducibility
end

set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Module Polynomial
namespace Formalism.GaloisIrreducibility
theorem _root_.solution {K : Type} [Field K] [IsAlgClosed K] (q : ℕ) : ∀ (n : ℕ) (V : Type)
    [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    finrank K V = n → ∀ (A : Module.End K V),
      (A ^ q).charpoly.roots = A.charpoly.roots.map (· ^ q) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn A
  have hinv : ∀ (S : Submodule K V) (hS : ∀ x ∈ S, A x ∈ S) (hSq : ∀ x ∈ S, (A ^ q) x ∈ S),
      (A ^ q).restrict hSq = (A.restrict hS) ^ q := by
    intro S hS hSq
    ext x
    rw [LinearMap.restrict_coe_apply, coe_restrict_pow_apply']
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  ·
    have hsub : Subsingleton V := Module.finrank_zero_iff.mp (hn.trans hn0)
    have hnil : ∀ B : Module.End K V, B.charpoly = 1 := by
      intro B
      have hB : IsNilpotent B := ⟨1, LinearMap.ext fun x => Subsingleton.elim _ _⟩
      rw [(LinearMap.isNilpotent_iff_charpoly B).mp hB, hn, hn0, pow_zero]
    simp [hnil]
  · haveI : Nontrivial V := Module.finrank_pos_iff.mp (hn ▸ hnpos)
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue A
    obtain ⟨f, hf⟩ : ∃ f : Module.End K V, f = A - μ • 1 := ⟨_, rfl⟩
    obtain ⟨N0, hN0⟩ :=
      Filter.eventually_atTop.mp (LinearMap.eventually_isCompl_ker_pow_range_pow f)
    have hPQ := hN0 (N0 + 1) (Nat.le_succ _)

    have hcomm : ∀ g : Module.End K V, Commute g f →
        (∀ x ∈ LinearMap.ker (f ^ (N0 + 1)), g x ∈ LinearMap.ker (f ^ (N0 + 1))) ∧ (∀ x ∈ LinearMap.range (f ^ (N0 + 1)), g x ∈ LinearMap.range (f ^ (N0 + 1))) := by
      intro g hg
      have hgN := (hg.pow_right (N0 + 1)).eq
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [LinearMap.mem_ker] at hx ⊢
        rw [← Module.End.mul_apply, ← hgN, Module.End.mul_apply, hx, map_zero]
      · obtain ⟨y, rfl⟩ := hx
        exact ⟨g y, by rw [← Module.End.mul_apply, ← hgN, Module.End.mul_apply]⟩
    have hAf : Commute A f := by
      rw [hf]
      exact (Commute.refl A).sub_right ((Commute.one_right A).smul_right μ)
    obtain ⟨hP, hQ⟩ := hcomm A hAf
    obtain ⟨hPq, hQq⟩ := hcomm (A ^ q) (hAf.pow_left q)
    by_cases hQb : LinearMap.range (f ^ (N0 + 1)) = ⊥
    ·
      have hPt : LinearMap.ker (f ^ (N0 + 1)) = ⊤ := by
        have h := hPQ.sup_eq_top
        rwa [hQb, sup_bot_eq] at h
      have hnil : IsNilpotent f := ⟨N0 + 1, LinearMap.ker_eq_top.mp hPt⟩
      rw [hf] at hnil
      have hnilq : IsNilpotent (A ^ q - (μ ^ q) • 1) := by
        have h := rr_nilp_pow A μ (by rw [Algebra.algebraMap_eq_smul_one]; exact hnil) q
        rwa [Algebra.algebraMap_eq_smul_one] at h
      rw [rr_roots_of_nilp A μ hnil, rr_roots_of_nilp (A ^ q) (μ ^ q) hnilq, Multiset.map_replicate]
    ·
      have hPb : LinearMap.ker (f ^ (N0 + 1)) ≠ ⊥ := by
        intro hPb
        obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
        apply hv.2
        have hfv : f v = 0 := by
          rw [hf, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
            hv.apply_eq_smul, sub_self]
        have hvP : v ∈ LinearMap.ker (f ^ (N0 + 1)) := by
          rw [LinearMap.mem_ker, pow_succ, Module.End.mul_apply, hfv, map_zero]
        rw [hPb] at hvP
        exact (Submodule.mem_bot K).mp hvP
      have hdim := Submodule.finrank_add_eq_of_isCompl hPQ
      have hP0 : finrank K (LinearMap.ker (f ^ (N0 + 1))) ≠ 0 := fun h => hPb (Submodule.finrank_eq_zero.mp h)
      have hQ0 : finrank K (LinearMap.range (f ^ (N0 + 1))) ≠ 0 := fun h => hQb (Submodule.finrank_eq_zero.mp h)
      have ihP := ih _ (by omega) (LinearMap.ker (f ^ (N0 + 1))) rfl (A.restrict hP)
      have ihQ := ih _ (by omega) (LinearMap.range (f ^ (N0 + 1))) rfl (A.restrict hQ)
      have hne : ∀ (S : Submodule K V) (B : Module.End K S), B.charpoly ≠ 0 :=
        fun S B => (LinearMap.charpoly_monic B).ne_zero
      rw [rr_charpoly_compl (A ^ q) _ _ hPQ hPq hQq, rr_charpoly_compl A _ _ hPQ hP hQ,
        Polynomial.roots_mul (mul_ne_zero (hne _ _) (hne _ _)),
        Polynomial.roots_mul (mul_ne_zero (hne _ _) (hne _ _)),
        hinv _ hP hPq, hinv _ hQ hQq, ihP, ihQ, Multiset.map_add]
end Formalism.GaloisIrreducibility
