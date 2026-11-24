-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.compressTraceLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:28.869812+00:00
-- url     : https://prove2.me/submissions/439d5435-0e20-45d2-8fcf-bcd69ed6e190

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_trace_Qm
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_Rs_nonneg
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_Kp_ram
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_ram_gap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
open scoped ComplexOrder
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
section HS
variable {m n k : Type} [Fintype m] [Fintype n] [Fintype k]
end HS
section Fam
variable {ι : Type} [Fintype ι] {D : ℕ} {d : ι → ℕ}
end Fam
section CS
variable {m n : Type} [Fintype m] [Fintype n]
private theorem le_sqrt_of_sq_le' {x y : ℝ} (h : x ^ 2 ≤ y) : x ≤ Real.sqrt y := by
  refine (le_abs_self x).trans ?_
  exact Real.abs_le_sqrt h
end CS
section Tri
variable {m n : Type} [Fintype m] [Fintype n]
end Tri
section Cor
variable {ι : Type} [Fintype ι] {D : ℕ} {d : ι → ℕ}
end Cor
section Compress
variable {m n k : Type} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq k]
end Compress
section Ram
variable {ι : Type} [Fintype ι] {D : ℕ} {d r : ι → ℕ}
end Ram
section RamTr
end RamTr
section RamMain
variable {ι : Type} [Fintype ι] {D : ℕ} {d r : ι → ℕ}
private theorem sum_sqrt_mul_sqrt_le_sqrt_sum_mul' {κ : Type} [Fintype κ] (a b : κ → ℝ) (ha : ∀ u, 0 ≤ a u)
    (hb : ∀ u, 0 ≤ b u) :
    ∑ u, Real.sqrt (a u) * Real.sqrt (b u) ≤ Real.sqrt (∑ u, a u) * Real.sqrt (∑ u, b u) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun u => Real.sqrt (a u))
    (fun u => Real.sqrt (b u))
  have ea : ∀ u, Real.sqrt (a u) ^ 2 = a u := fun u => Real.sq_sqrt (ha u)
  have eb : ∀ u, Real.sqrt (b u) ^ 2 = b u := fun u => Real.sq_sqrt (hb u)
  simp only [ea, eb] at h
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun u _ => ha u)]
  exact le_sqrt_of_sq_le' h
end RamMain
section Num
end Num
section Final
variable {ι : Type} [Fintype ι] {D : ℕ} {d r : ι → ℕ}
end Final
end
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
end

set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
variable {ι : Type} [Fintype ι] {D : ℕ} {d r : ι → ℕ}
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
theorem _root_.solution : RamTrace := by
  intro ι _ D d r B V ga de e0 hV hga hde he hK hsum
  have hV' : ∀ u, (V u)ᴴ * V u = 1 := hV
  have hu : ∀ u, (Kd B ga u).trace.re - (Kd (Bram B V) ga u).trace.re
      ≤ ((d u : ℝ) - r u) + Real.sqrt ((d u : ℝ) - r u) * (Real.sqrt e0 * Real.sqrt (d u)) := by
    intro u
    have e : Kd (Bram B V) ga u = (V u)ᴴ * Kd B ga u * V u :=
      Kp_ram B V ga u u
    rw [e]
    exact (ram_gap (d u) (r u) (Kd B ga u) (V u) (hV' u) he
      (hK u)).2
  have hnn : ∀ u, 0 ≤ (d u : ℝ) - r u := fun u =>
    (ram_gap (d u) (r u) (Kd B ga u) (V u) (hV' u) he (hK u)).1
  have hCS : ∑ u, Real.sqrt ((d u : ℝ) - r u) * Real.sqrt (d u)
      ≤ Real.sqrt (∑ u, ((d u : ℝ) - r u)) * Real.sqrt (Rs d) :=
    sum_sqrt_mul_sqrt_le_sqrt_sum_mul' _ _ hnn (fun u => Nat.cast_nonneg _)
  have h3 : Real.sqrt (∑ u, ((d u : ℝ) - r u)) ≤ Real.sqrt de * Real.sqrt (Rs d) := by
    rw [← Real.sqrt_mul hde]
    exact Real.sqrt_le_sqrt hsum
  have hT : Real.sqrt (Rs d) * Real.sqrt (Rs d) = Rs d :=
    Real.mul_self_sqrt (Rs_nonneg d)
  have h4 : ∑ u, Real.sqrt ((d u : ℝ) - r u) * Real.sqrt (d u) ≤ Real.sqrt de * Rs d := by
    have h := mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg (Rs d))
    rw [mul_assoc, hT] at h
    linarith
  have h5 := mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg e0)
  have h2 : ∑ u, Real.sqrt ((d u : ℝ) - r u) * (Real.sqrt e0 * Real.sqrt (d u))
      = Real.sqrt e0 * ∑ u, Real.sqrt ((d u : ℝ) - r u) * Real.sqrt (d u) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  have hsumu := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) => hu u
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, h2] at hsumu
  rw [trace_Qm B ga hga, trace_Qm (Bram B V) ga hga, Complex.re_sum,
    Complex.re_sum, Real.sqrt_mul hde e0]
  linarith
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
