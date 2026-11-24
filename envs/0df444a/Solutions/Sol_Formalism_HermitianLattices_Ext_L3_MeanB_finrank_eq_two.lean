-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.MeanB.finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:04.67717+00:00
-- url     : https://prove2.me/submissions/0e6b3c98-52ba-4ce9-9f42-06933cbba554

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulSubOneMemPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_exists_star_ne
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_star_algebraMap
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.MeanB
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.MeanB
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) : finrank F K = 2 := by
  obtain ⟨θ, hθ⟩ := exists_star_ne hK
  set δ : K := θ - star θ with hδ
  have hδ0 : δ ≠ 0 := fun h => hθ (sub_eq_zero.1 h).symm
  have hsδ : star δ = -δ := by rw [hδ, star_sub, star_star]; ring
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hli : LinearIndependent F ![(1 : K), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t e
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at e
    have e' := congrArg star e
    rw [star_add, star_mul', star_algebraMap hF, star_algebraMap hF, hsδ, star_zero] at e'
    have hs : algebraMap F K s = 0 := by
      have : 2 * algebraMap F K s = 0 := by linear_combination e + e'
      exact (mul_eq_zero.1 this).resolve_left h2
    have ht : algebraMap F K t = 0 := by
      rw [hs, zero_add] at e
      exact (mul_eq_zero.1 e).resolve_right hδ0
    exact ⟨(map_eq_zero _).1 hs, (map_eq_zero _).1 ht⟩
  have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : K), δ]) := by
    intro a _
    obtain ⟨f1, hf1⟩ := (hF ((a + star a) / 2)).1 (by
      rw [star_div₀, star_add, star_star, star_ofNat, add_comm])
    obtain ⟨f2, hf2⟩ := (hF ((a - star a) / (2 * δ))).1 (by
      rw [star_div₀, star_sub, star_star, star_mul', star_ofNat, hsδ]
      field_simp
      ring)
    have : Set.range ![(1 : K), δ] = {1, δ} := by
      simp [Matrix.range_cons, Set.pair_comm]
    rw [this, Submodule.mem_span_pair]
    refine ⟨f1, f2, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, hf1, hf2]
    field_simp
    ring
  have := finrank_eq_card_basis (Basis.mk hli hsp)
  simpa using this
end Formalism.HermitianLattices.Ext.L3.MeanB
