-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.MeanA.exists_mul_sub_one_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:44:16.917722+00:00
-- url     : https://prove2.me/submissions/b08c2aa5-56d9-4f96-87bb-5863975b0359

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulSubOneMemPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
set_option linter.deprecated false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.MeanA
namespace Formalism.HermitianLattices.Ext.L3.MeanA
theorem _root_.solution {R : Type*} [CommRing R] {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) {t : R}
    (ht : t ∉ 𝔭) (k : ℕ) : ∃ u : R, u * t - 1 ∈ 𝔭 ^ k := by
  obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv ht
  refine ⟨(∑ j ∈ Finset.range k, i ^ j) * y, ?_⟩
  have h1 : (∑ j ∈ Finset.range k, i ^ j) * (i - 1) = i ^ k - 1 := geom_sum_mul i k
  have h2 : (∑ j ∈ Finset.range k, i ^ j) * y * t - 1 = -(i ^ k) := by
    linear_combination (∑ j ∈ Finset.range k, i ^ j) * hyi - h1
  rw [h2]
  exact (𝔭 ^ k).neg_mem (Ideal.pow_mem_pow hi k)
end Formalism.HermitianLattices.Ext.L3.MeanA
