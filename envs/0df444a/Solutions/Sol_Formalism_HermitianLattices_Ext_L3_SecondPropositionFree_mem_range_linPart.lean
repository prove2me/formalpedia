-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.SecondPropositionFree.mem_range_linPart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:49.216127+00:00
-- url     : https://prove2.me/submissions/0cc03c6a-f2ec-4aa2-94f0-29d92d60ff73

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemRangeLinPart
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_linPart_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.SecondPropositionFree
open NormLifting
variable {A B : Type*} [CommRing A] [CommRing B] {σ : A →+* A} {τ : B →+* B} {π : A →+* B}
namespace Formalism.HermitianLattices.Ext.L3.SecondPropositionFree
theorem _root_.solution (I : Ideal A) {M : ℕ} (y : Fin M → A) (i₀ : Fin M)
    {b : A} (hb : σ (y i₀) * b + σ b * y i₀ = 1) {w : A} (hw : w ∈ fixSub σ I) :
    w ∈ (linPart σ I y).range := by
  have hw' : w ∈ I ∧ σ w = w := hw
  obtain ⟨hwI, hσw⟩ := hw'
  classical
  refine ⟨fun i => if i = i₀ then ⟨b * w, I.mul_mem_left b hwI⟩ else 0, ?_⟩
  rw [linPart_apply, Finset.sum_eq_single i₀]
  · rw [if_pos rfl]
    show σ (y i₀) * (b * w) + σ (b * w) * y i₀ = w
    rw [map_mul, hσw]
    linear_combination w * hb
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i₀) h
end Formalism.HermitianLattices.Ext.L3.SecondPropositionFree
