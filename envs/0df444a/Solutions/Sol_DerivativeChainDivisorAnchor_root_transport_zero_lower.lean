-- Prove2me | solution 1 for DerivativeChainDivisorAnchor.root_transport_zero_lower
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:41:10.869348+00:00
-- url     : https://prove2.me/submissions/c361ae9a-a902-495b-bd48-6784bcf8ac47

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorAnchorFunctional
import Definitions.Def_DerivativeChainGini_DivisorRootTransport
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainDivisorAnchor
end DerivativeChainDivisorAnchor
namespace DerivativeChainGini
end DerivativeChainGini
namespace DerivativeChainGiniCircle
end DerivativeChainGiniCircle
namespace DerivativeChainGiniFamily
end DerivativeChainGiniFamily
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section
attribute [local instance] Classical.propDecidable





theorem rootSum_coe (P : ℂ[X]) (f : ℂ → ℝ) : rootSum P f = ∑ i : P.roots, f (i:ℂ) := by
  symm
  change ((Finset.univ : Finset P.roots).val.map (fun i : P.roots => f (i:ℂ))).sum = _
  rw [Multiset.map_univ]
  rfl

theorem root_card (P : ℂ[X]) : Fintype.card P.roots = P.natDegree := by
  rw [Multiset.card_coe, ← (IsAlgClosed.splits P).natDegree_eq_card_roots]

theorem product_root_coupling (P Q : ℂ[X]) (hP : 0 < P.natDegree) (hQ : 0 < Q.natDegree) :
    UniformRootCoupling P Q (fun _ _ => (1/(P.natDegree:ℝ))*(1/(Q.natDegree:ℝ))) := by
  have hp : (P.natDegree:ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  have hq : (Q.natDegree:ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  constructor
  · intro i j
    positivity
  constructor
  · intro i
    simp only [Finset.sum_const, Finset.card_univ, root_card, nsmul_eq_mul]
    field_simp
  · intro j
    simp only [Finset.sum_const, Finset.card_univ, root_card, nsmul_eq_mul]
    field_simp















end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
open DerivativeChainDivisorAnchor

attribute [local instance] Classical.propDecidable











theorem solution (P Q : ℂ[X]) (hP : 0 < P.natDegree) (hQ : 0 < Q.natDegree)
    (a : ℝ) (ha : 0 ≤ a) (hmin : ∀ i : P.roots, a ≤ ‖(i:ℂ)‖) :
    a*(rootSum Q (fun y => if y=0 then 1 else 0)/(Q.natDegree:ℝ)) ≤ uniformRootW1 P Q := by
  apply le_csInf
  · exact ⟨_, ⟨_, product_root_coupling P Q hP hQ, rfl⟩⟩
  rintro t ⟨q, hq, rfl⟩
  have hterm (i : P.roots) (j : Q.roots) :
      (a*(if (j:ℂ)=0 then 1 else 0))*q i j ≤ q i j*‖(i:ℂ)-(j:ℂ)‖ := by
    split_ifs with hj
    · simpa [hj, mul_comm] using mul_le_mul_of_nonneg_left (hmin i) (hq.1 i j)
    · simp only [mul_zero, zero_mul]
      exact mul_nonneg (hq.1 i j) (norm_nonneg _)
  calc
    _ = ∑ j : Q.roots, (a*(if (j:ℂ)=0 then 1 else 0))*(∑ i : P.roots, q i j) := by
      simp only [hq.2.2, rootSum_coe, ← Finset.sum_mul, ← Finset.mul_sum]
      ring
    _ = ∑ i : P.roots, ∑ j : Q.roots, (a*(if (j:ℂ)=0 then 1 else 0))*q i j := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
