-- Prove2me | solution 1 for DerivativeChainPhaseLock.uniform_kernel_minimum
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:47:42.259065+00:00
-- url     : https://prove2.me/submissions/7094ee5b-e1a5-4a78-9ddc-3b6b67332131

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_UniformWasserstein
import Theorems.Thm_DerivativeChainPrefixLaws_nonnegative_linear_fiber_isCompact_of_bound
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
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace DerivativeChainPrefixLaws
noncomputable section



theorem nonnegative_linear_min_of_bound {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : (ι → ℝ) →ₗ[ℝ] F) (b : F) (c B w0 : ι → ℝ)
    (hw0 : ∀ i,0 ≤ w0 i) (hA0 : A w0=b)
    (hbound : ∀ w : ι → ℝ,(∀ i,0 ≤ w i) → A w=b → ∀ i,w i ≤ B i) :
    ∃ p : ι → ℝ,(∀ i,0 ≤ p i) ∧ A p=b ∧
      ∀ q : ι → ℝ,(∀ i,0 ≤ q i) → A q=b → (∑ i,p i*c i) ≤ ∑ i,q i*c i := by
  obtain ⟨p,hp,hmin⟩ := (nonnegative_linear_fiber_isCompact_of_bound A b B hbound).exists_isMinOn
    ⟨w0,hw0,hA0⟩ (show ContinuousOn (fun w : ι → ℝ => ∑ i,w i*c i)
      {w | (∀ i,0 ≤ w i) ∧ A w=b} by fun_prop)
  exact ⟨p,hp.1,hp.2,fun q hq hAq => hmin ⟨hq,hAq⟩⟩



end
end DerivativeChainPrefixLaws



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open DerivativeChainPrefixLaws
open DerivativeChainPhaseLock








theorem solution {m n : ℕ} (x : Fin (m+1) → ℂ) (y : Fin (n+1) → ℂ) :
    ∃ K : Fin (m+1) → Fin (n+1) → ℝ,_root_.DerivativeChainPhaseLock.UniformKernel m n K ∧
      ∀ Q,_root_.DerivativeChainPhaseLock.UniformKernel m n Q → _root_.DerivativeChainPhaseLock.uniformKernelCost x y K ≤ _root_.DerivativeChainPhaseLock.uniformKernelCost x y Q := by
  classical
  let b : (Fin (m+1) → ℝ) × (Fin (n+1) → ℝ) :=
    (fun _ => (m+1:ℝ)⁻¹,fun _ => (n+1:ℝ)⁻¹)
  let p0 : Fin (m+1) × Fin (n+1) → ℝ := fun _ => (m+1:ℝ)⁻¹*(n+1:ℝ)⁻¹
  have h0 : ∀ ij,0 ≤ p0 ij := by intro ij; dsimp [p0]; positivity
  have hM : ∀ m : ℕ,(∑ _ : Fin (m+1),(m+1:ℝ)⁻¹)=1 := by
    intro m
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    push_cast
    exact mul_inv_cancel₀ (by positivity : (m+1:ℝ) ≠ 0)
  have hA0 : _root_.DerivativeChainPhaseLock.jointMarginals m n p0=b := by
    apply Prod.ext <;> funext i
    · change (∑ j : Fin (n+1),(m+1:ℝ)⁻¹*(n+1:ℝ)⁻¹)=(m+1:ℝ)⁻¹
      rw [← Finset.mul_sum,hM,mul_one]
    · change (∑ j : Fin (m+1),(m+1:ℝ)⁻¹*(n+1:ℝ)⁻¹)=(n+1:ℝ)⁻¹
      rw [← Finset.sum_mul,hM,one_mul]
  have hbound : ∀ p : Fin (m+1) × Fin (n+1) → ℝ,
      (∀ ij,0 ≤ p ij) → _root_.DerivativeChainPhaseLock.jointMarginals m n p=b → ∀ ij,p ij ≤ 1 := by
    intro p hp hA ij
    have hr : (∑ j,p (ij.1,j))=(m+1:ℝ)⁻¹ := congrFun (congrArg Prod.fst hA) ij.1
    have hi := Finset.single_le_sum (fun j _ => hp (ij.1,j)) (Finset.mem_univ ij.2)
    have hb : (m+1:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m)))
    exact hi.trans (hr.trans_le hb)
  obtain ⟨p,hp,hA,hmin⟩ := _root_.DerivativeChainPrefixLaws.nonnegative_linear_min_of_bound (_root_.DerivativeChainPhaseLock.jointMarginals m n) b
    (fun ij => ‖y ij.2-x ij.1‖) (fun _ => 1) p0 h0 hA0 hbound
  let K : Fin (m+1) → Fin (n+1) → ℝ := fun i j => (m+1:ℝ)*p (i,j)
  have hrow (i : Fin (m+1)) : (∑ j,p (i,j))=(m+1:ℝ)⁻¹ := congrFun (congrArg Prod.fst hA) i
  have hcol (j : Fin (n+1)) : (∑ i,p (i,j))=(n+1:ℝ)⁻¹ := congrFun (congrArg Prod.snd hA) j
  have hn : (m+1:ℝ) ≠ 0 := by positivity
  have hmass (i j) : (m+1:ℝ)⁻¹*K i j=p (i,j) := by dsimp [K]; rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]
  have hK : _root_.DerivativeChainPhaseLock.UniformKernel m n K := by
    refine ⟨?_,?_,?_⟩
    · intro i j; exact mul_nonneg (by positivity) (hp (i,j))
    · intro i; dsimp [K]; rw [← Finset.mul_sum,hrow,mul_inv_cancel₀ hn]
    · intro j; simp only [hmass,hcol]
  refine ⟨K,hK,?_⟩
  intro Q hQ
  let q : Fin (m+1) × Fin (n+1) → ℝ := fun ij => (m+1:ℝ)⁻¹*Q ij.1 ij.2
  have hq : ∀ ij,0 ≤ q ij := by intro ij; exact mul_nonneg (by positivity) (hQ.1 _ _)
  have hqA : _root_.DerivativeChainPhaseLock.jointMarginals m n q=b := by
    apply Prod.ext <;> funext i
    · change (∑ j,(m+1:ℝ)⁻¹*Q i j)=(m+1:ℝ)⁻¹
      rw [← Finset.mul_sum,hQ.2.1,mul_one]
    · exact hQ.2.2 i
  have h := hmin q hq hqA
  simpa only [_root_.DerivativeChainPhaseLock.uniformKernelCost,Finset.mul_sum,← mul_assoc,hmass,
    Fintype.sum_prod_type,q] using h
