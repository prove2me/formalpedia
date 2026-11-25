-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.principal_zeta_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:58:02.564263+00:00
-- url     : https://prove2.me/submissions/92f92f6b-2eb3-4816-ad7c-69e777400526

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLsA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet EtaPartialSums
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
theorem _root_.solution : PrincipalZeta := by
  intro M _ s hs hz
  have hs1 : s ≠ 1 := by
    rcases hz.1 with h | h
    · exact absurd rfl h
    · exact h
  have h := hz.2
  rw [← DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs1] at h
  rcases mul_eq_zero.mp h with h | h
  · exfalso
    rw [Finset.prod_eq_zero_iff] at h
    obtain ⟨p, hp, hp0⟩ := h
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hlt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hpp.pos]
      simp only [Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpp.one_lt) (by linarith)
    have : (p : ℂ) ^ (-s) = 1 := by linear_combination -hp0
    rw [this, norm_one] at hlt
    exact lt_irrefl _ hlt
  · exact h
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
