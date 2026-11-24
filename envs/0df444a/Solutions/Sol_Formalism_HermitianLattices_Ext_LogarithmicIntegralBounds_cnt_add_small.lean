-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.cnt_add_small
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:22.28033+00:00
-- url     : https://prove2.me/submissions/ab16d586-d42d-45a9-b099-35a4acfd502f

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqOrth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistA

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
theorem _root_.solution (m₀ s a₀ : ℕ) (X : ℝ) (b : ℕ) (hb : b ∈ clsB m₀ s a₀) :
    ((PPset m₀ a₀ X).filter (fun q => q % (m₀ * s) = b)).card + smallCnt X (m₀ * s) b = piAP X (m₀ * s) b := by
  obtain ⟨hbr, hbm, -⟩ : b < m₀ * s ∧ b % m₀ = a₀ % m₀ ∧ b.Coprime s := by
    simpa [clsB] using hb
  have hbM : b % (m₀ * s) = b := Nat.mod_eq_of_lt hbr
  have hmod : ∀ p : ℕ, p % (m₀ * s) = b → p % m₀ = a₀ % m₀ := fun p h => by
    rw [← Nat.mod_mod_of_dvd p (dvd_mul_right m₀ s), h, hbm]
  have key := Finset.card_filter_add_card_filter_not
    (s := (Finset.Icc 1 ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ p % (m₀ * s) = b))
    (fun p : ℕ => X ^ (1 / 2 : ℝ) < (p : ℝ))
  unfold piAP
  rw [hbM, ← key]
  congr 1
  · congr 1
    ext p
    simp only [PPset, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, h2, -, h4⟩, h5⟩
      exact ⟨⟨h1, h2, h5⟩, h4⟩
    · rintro ⟨⟨h1, h2, h5⟩, h4⟩
      exact ⟨⟨h1, h2, hmod p h5, h4⟩, h5⟩
  · unfold smallCnt
    congr 1
    ext p
    simp only [Finset.mem_filter, not_lt]
    constructor
    · rintro ⟨⟨h1, h2, h4⟩, h5⟩
      exact ⟨⟨h1, h2, h5⟩, h4⟩
    · rintro ⟨⟨h1, h2, h5⟩, h4⟩
      exact ⟨⟨h1, h2, h4⟩, h5⟩
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
