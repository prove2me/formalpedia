-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.gen_mod_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:17:56.233231+00:00
-- url     : https://prove2.me/submissions/7b029e68-de02-48fc-8aba-7ca4ea56c86f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PStdChar
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_SC_even_im_hermitian_sub
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_SC_half_mem
import Theorems.Thm_Formalism_L2_Th1_F_Cm1_coord
import Theorems.Thm_Formalism_L2_Th1_F_Cm2_even_im_hermitian_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmTheta thetaZeroCharacter semiChar herm)
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
theorem _root_.solution (L : PeriodPair) (x y w : ℂ) (hx : x ∈ L.lattice) (hy : y ∈ L.lattice) (hw : w ∈ L.lattice)
    (h1 : x / 2 ∉ L.lattice) (h2 : y / 2 ∉ L.lattice) (h3 : (x + y) / 2 ∉ L.lattice) :
    ∃ v ∈ L.lattice, w = 2 * v ∨ w = x + 2 * v ∨ w = y + 2 * v ∨ w = x + y + 2 * v := by
  have coord : ∀ z ∈ L.lattice, ∃ m n : ℤ, z = (m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂ := by
    intro z hz
    obtain ⟨m, n, h⟩ := Submodule.mem_span_pair.mp hz
    exact ⟨m, n, by rw [← h]; simp [zsmul_eq_mul]⟩
  obtain ⟨a, b, rfl⟩ := coord x hx
  obtain ⟨c, e, rfl⟩ := coord y hy
  obtain ⟨m, k, rfl⟩ := coord w hw
  have n1 : ¬(2 ∣ a ∧ 2 ∣ b) := fun h => h1 (half_mem L a b h.1 h.2)
  have n2 : ¬(2 ∣ c ∧ 2 ∣ e) := fun h => h2 (half_mem L c e h.1 h.2)
  have n3 : ¬(2 ∣ a + c ∧ 2 ∣ b + e) := by
    intro h
    apply h3
    have eq : ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ + ((c : ℂ) * L.ω₁ + (e : ℂ) * L.ω₂)) / 2 =
        (((a + c : ℤ) : ℂ) * L.ω₁ + ((b + e : ℤ) : ℂ) * L.ω₂) / 2 := by
      push_cast
      ring
    rw [eq]
    exact half_mem L _ _ h.1 h.2
  rcases even_im_hermitian_sub a b c e m k n1 n2 n3 with h | h | h | h
  · refine ⟨((m : ℂ) * L.ω₁ + (k : ℂ) * L.ω₂) / 2, half_mem L m k h.1 h.2, Or.inl ?_⟩
    ring
  · refine ⟨(((m - a : ℤ) : ℂ) * L.ω₁ + ((k - b : ℤ) : ℂ) * L.ω₂) / 2, half_mem L _ _ h.1 h.2,
      Or.inr (Or.inl ?_)⟩
    push_cast
    ring
  · refine ⟨(((m - c : ℤ) : ℂ) * L.ω₁ + ((k - e : ℤ) : ℂ) * L.ω₂) / 2, half_mem L _ _ h.1 h.2,
      Or.inr (Or.inr (Or.inl ?_))⟩
    push_cast
    ring
  · refine ⟨(((m - (a + c) : ℤ) : ℂ) * L.ω₁ + ((k - (b + e) : ℤ) : ℂ) * L.ω₂) / 2,
      half_mem L _ _ h.1 h.2, Or.inr (Or.inr (Or.inr ?_))⟩
    push_cast
    ring
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
