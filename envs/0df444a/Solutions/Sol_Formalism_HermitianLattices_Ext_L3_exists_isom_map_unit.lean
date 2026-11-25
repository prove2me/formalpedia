-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.exists_isom_map_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:14:06.476786+00:00
-- url     : https://prove2.me/submissions/afd97642-d851-4cf7-84dd-75ffccb3f52a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomMapOfEq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_isom_map_of_eq
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {L : Submodule (𝓞 K) V} {n : ℕ} (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n)
    {x y : V} (hx : h x x = 1) (hy : h y y = 1) : ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, g x = y := by
  have hd : IsTotPosDef h := by
    obtain ⟨e, -, hsp, -, he⟩ := hL
    intro x hx φ
    have hxs : x ∈ Submodule.span K (Set.range e) := by rw [hsp]; exact Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hxs
    have hval : h (∑ i, c i • e i) (∑ i, c i • e i) = ∑ i, star (c i) * c i := by
      simp [map_sum, he, Finset.mul_sum, mul_ite, ite_mul, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [starRingEnd_apply, mul_comm]
    rw [hval, map_sum, Complex.re_sum]
    have hc : ∃ i, c i ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hx (by simp [hne])
    obtain ⟨i0, hi0⟩ := hc
    refine Finset.sum_pos' (fun i _ => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
    · rw [map_mul, hK.2.1, ← Complex.normSq_eq_conj_mul_self]
      exact Complex.normSq_nonneg _
    · rw [map_mul, hK.2.1, ← Complex.normSq_eq_conj_mul_self]
      exact Complex.normSq_pos.2 ((map_ne_zero φ).2 hi0)
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  exact exists_isom_map_of_eq hK hs hd hx0 (by rw [hx, hy])
end Formalism.HermitianLattices.Ext.L3
