-- Prove2me | solution 1 for Formalism.L2.Th1.H.InterInv_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:40.756314+00:00
-- url     : https://prove2.me/submissions/40441326-3b9a-43dd-9cd9-fba4fac56bcb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence
import Theorems.Thm_Formalism_L2_Th1_H_Inv_sum_reps
import Theorems.Thm_Formalism_L2_Th1_H_Inv_opU_const_mul
import Theorems.Thm_Formalism_L2_Th1_H_Inv_opU_finset_sum
import Theorems.Thm_Formalism_L2_Th1_H_characterSum
import Theorems.Thm_Formalism_L2_Th1_H_IndexEq_of
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.H
namespace Inv
variable {V : Type} [AddCommGroup V] [Module ℂ V]
private theorem inv_sqrt_mul_inv_sqrt_mul_natCast_mul {n : ℕ} (hn : n ≠ 0) (w : ℂ) :
    ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ * (((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ * ((n : ℂ) * w)) = w := by
  have hs : ((Real.sqrt (n : ℝ) : ℝ) : ℂ) * ((Real.sqrt (n : ℝ) : ℝ) : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have hne : ((Real.sqrt (n : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)))
  rw [← hs, show ∀ s : ℂ, s⁻¹ * (s⁻¹ * (s * s * w)) = (s⁻¹ * s) * (s⁻¹ * s) * w from fun s => by ring,
    inv_mul_cancel₀ hne, one_mul, one_mul]
end Inv
open Inv
end Formalism.L2.Th1.H
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Inv
namespace Formalism.L2.Th1.H
theorem _root_.solution (hcomm : OpUComm) (hreps : InterReps) (hfix : InterFixed) (hr : RepsExist) :
    InterInv := by
  intro V _ _ H hH Λ₁ Λ₂ α h₁ h₂ hα₁ hα₂ h12 h21 F hF z
  have hidx : relIdx Λ₁ Λ₂ = relIdx Λ₂ Λ₁ :=
    IndexEq_of characterSum hr V H hH Λ₁ Λ₂ h₁ h₂ h12 h21
  obtain ⟨⟨S₂, hS₂⟩, -⟩ := hr V Λ₁ Λ₂ h12
  obtain ⟨⟨S₁, hS₁⟩, hcard₁⟩ := hr V Λ₂ Λ₁ h21
  have hF' : ∀ x ∈ Λ₁, ∀ w, α x * opU H x F w = F w := hF
  have hG := hfix V H hH Λ₁ Λ₂ α hα₂ h12 F hF
  have hIF : inter H α Λ₁ Λ₂ F = fun v =>
      ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹ * ∑ y ∈ S₂, α y * opU H y F v := by
    funext v
    exact hreps V H hH Λ₁ Λ₂ α hα₂ F hF S₂ hS₂ v
  have hfixop : ∀ x ∈ Λ₁, ∀ y, α x * opU H y (opU H x F) z = opU H y F z := by
    intro x hx y
    have hfun : (fun v => α x * opU H x F v) = F := funext (hF' x hx)
    rw [← Formalism.L2.Th1.H.Inv.opU_const_mul, hfun]
  have hterm : ∀ x ∈ Λ₁, ∀ y, α x * (α y * opU H x (opU H y F) z)
      = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x y : ℂ)) * (α y * opU H y F z) := by
    intro x hx y
    rw [(hcomm V H hH F z).2 x y, ← hfixop x hx y]
    ring
  have e1 : ∀ x ∈ S₁, α x * opU H x (fun v =>
        ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹ * ∑ y ∈ S₂, α y * opU H y F v) z
      = ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹ * ∑ y ∈ S₂, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x y : ℂ)) * (α y * opU H y F z) := by
    intro x hx
    rw [Formalism.L2.Th1.H.Inv.opU_const_mul, Formalism.L2.Th1.H.Inv.opU_finset_sum, mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Formalism.L2.Th1.H.Inv.opU_const_mul]
    exact hterm x (hS₁.1 x hx) y
  rw [hreps V H hH Λ₂ Λ₁ α hα₁ _ hG S₁ hS₁ z, sumU, hIF, Finset.sum_congr rfl e1,
    ← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.sum_mul]
  obtain ⟨y₀, hy₀S, hy₀, hsum⟩ := Formalism.L2.Th1.H.Inv.sum_reps hS₂
    (fun y => (∑ x ∈ S₁, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x y : ℂ))) * (α y * opU H y F z)) (by
      intro y hy hyn
      rw [characterSum V H hH Λ₁ Λ₂ h₁ h₂ S₁ hS₁ y (hS₂.1 y hy), if_neg hyn, zero_mul])
  rw [hsum, characterSum V H hH Λ₁ Λ₂ h₁ h₂ S₁ hS₁ y₀ (hS₂.1 y₀ hy₀S), if_pos hy₀, hF' y₀ hy₀ z,
    hcard₁ S₁ hS₁, hidx]
  exact _root_.Formalism.L2.Th1.H.Inv.inv_sqrt_mul_inv_sqrt_mul_natCast_mul h21 (F z)
end Formalism.L2.Th1.H
