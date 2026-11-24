-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.abs_pair_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:31.583567+00:00
-- url     : https://prove2.me/submissions/0160a3f1-1111-445e-89fd-a0e9d7406007

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqJac
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqPairs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwist
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqMainA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqMainB
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqMain
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_jacobi_class


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (PP : Finset ℕ) (m₀ a₀ n n' : ℕ) (h8 : 8 ∣ m₀) (ha : a₀.Coprime m₀) (hn : 0 < n)
    (hn' : 0 < n') (hPP : ∀ q ∈ PP, q.Prime ∧ q % m₀ = a₀ % m₀ ∧ n * n' < q) :
    |∑ q ∈ PP, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)| =
      |∑ q ∈ PP, (jacobiSym (q : ℤ) (soutPart m₀ (n * n')) : ℝ)| := by
  obtain ⟨σ, hσ, h⟩ := jacobi_class m₀ a₀ (n * n') h8 ha (Nat.mul_pos hn hn')
  have h1 : ∑ q ∈ PP, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ) =
      (σ : ℝ) * ∑ q ∈ PP, (jacobiSym (q : ℤ) (soutPart m₀ (n * n')) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨hp, hm, hlt⟩ := hPP q hq
    have := h q hp hm hlt
    rw [← jacobiSym.mul_left, ← Int.cast_mul, ← this]
    push_cast
    rfl
  rw [h1, abs_mul]
  rcases hσ with h | h <;> simp [h]
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
