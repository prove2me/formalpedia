-- Prove2me | solution 1 for DerivativeChainPrefixLaws.uniform_labelled_histories
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:46:07.051522+00:00
-- url     : https://prove2.me/submissions/e4f29a36-b675-4a48-b0ba-6115622a995d

import Mathlib
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainFiniteHistory
end DerivativeChainFiniteHistory
namespace DerivativeChainPhaseLock
end DerivativeChainPhaseLock
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate
open DerivativeChainPrefixLaws


theorem solution (n : ℕ)
    (K : (k : ℕ) → Fin (k+1) → Fin (k+2) → ℝ)
    (hK : ∀ k<n,∀ i j,0 ≤ K k i j)
    (hKs : ∀ k<n,∀ i,∑ j,K k i j=1)
    (hKcol : ∀ k<n,∀ j,(∑ i,(k+1:ℝ)⁻¹*K k i j)=(k+2:ℝ)⁻¹) :
    ∃ (κ : Type) (inst : Fintype κ),letI := inst;
      ∃ (w : κ → ℝ) (slots : κ → (k : ℕ) → Fin (k+1)),
        (∀ i,0 ≤ w i) ∧ (∑ i,w i=1) ∧
        (∀ k≤n,∀ f : Fin (k+1) → ℝ,
          (∑ i,w i*f (slots i k))=∑ j,(k+1:ℝ)⁻¹*f j) ∧
        ∀ k<n,∀ f : Fin (k+1) → Fin (k+2) → ℝ,
          (∑ i,w i*f (slots i k) (slots i (k+1)))=
            ∑ j,(k+1:ℝ)⁻¹*(∑ l,K k j l*f j l) := by
  classical
  induction n with
  | zero =>
    refine ⟨Fin 1,inferInstance,(fun _ => 1),(fun _ _ => 0),(by intro i; norm_num),?_,?_,?_⟩
    · simp
    · intro k hk f
      have he : k=0 := by omega
      subst k
      simp
    · intro k hk
      omega
  | succ n ih =>
    obtain ⟨κ,inst,hdata⟩ := ih (fun k hk => hK k (by omega))
      (fun k hk => hKs k (by omega)) (fun k hk => hKcol k (by omega))
    letI : Fintype κ := inst
    obtain ⟨w,slots,hw0,hws,hmarg,hjoint⟩ := hdata
    let W : κ × Fin (n+2) → ℝ := fun ij => w ij.1*K n (slots ij.1 n) ij.2
    let S : κ × Fin (n+2) → (k : ℕ) → Fin (k+1) :=
      fun ij => Function.update (slots ij.1) (n+1) ij.2
    have hSame (ij : κ × Fin (n+2)) (k : ℕ) (hk : k ≤ n) : S ij k=slots ij.1 k := by
      simp [S,Function.update_of_ne (show k ≠ n+1 by omega)]
    have hNew (ij : κ × Fin (n+2)) : S ij (n+1)=ij.2 := by simp [S]
    have hWs : (∑ ij,W ij)=1 := by
      simp only [W,Fintype.sum_prod_type,← Finset.mul_sum,hKs n (by omega),mul_one,hws]
    refine ⟨κ × Fin (n+2),inferInstance,W,S,?_,hWs,?_,?_⟩
    · intro ij
      exact mul_nonneg (hw0 ij.1) (hK n (by omega) _ _)
    · intro k hk f
      by_cases hold : k ≤ n
      · simp_rw [hSame _ k hold]
        simp only [W,Fintype.sum_prod_type,← Finset.sum_mul,← Finset.mul_sum,
          hKs n (by omega),mul_one]
        simpa only [← Finset.mul_sum] using hmarg k hold f
      · have he : k=n+1 := by omega
        subst k
        simp only [W,Fintype.sum_prod_type,hNew,mul_assoc,← Finset.mul_sum]
        rw [hmarg n le_rfl (fun i : Fin (n+1) => ∑ j,K n i j*f j)]
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        simp only [← mul_assoc,← Finset.sum_mul,hKcol n (by omega)]
        norm_num [Nat.cast_add,Nat.cast_one,add_assoc]

    · intro k hk f
      by_cases hold : k<n
      · simp_rw [hSame _ k (by omega),hSame _ (k+1) (by omega)]
        simp only [W,Fintype.sum_prod_type,← Finset.sum_mul,← Finset.mul_sum,
          hKs n (by omega),mul_one]
        simpa only [← Finset.mul_sum] using hjoint k hold f
      · have he : k=n := by omega
        subst k
        simp_rw [hSame _ n le_rfl,hNew]
        simp only [W,Fintype.sum_prod_type,mul_assoc,← Finset.mul_sum]
        simpa only [← Finset.mul_sum] using hmarg n le_rfl (fun j : Fin (n+1) => ∑ l,K n j l*f j l)
