-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Cell.exists_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:15:53.307017+00:00
-- url     : https://prove2.me/submissions/274ccb18-d359-4116-a8df-dc83f6038907

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormalise
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdLeOneOfBasis
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_isLattice_spanO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_integral_spanO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_vd_le_one_of_basis
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_family
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_symm0
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_GramDeterminantPositive_exists_basis_of_ortho
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_ne_zero_of_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_aniso_of_totPosDef
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_ne_zero_of_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mul_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_WCA____ne_zero_cf941fa073ca
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.Cell
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans WCA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)}
variable [FiniteDimensional K V]
namespace Formalism.HermitianLattices.Ext.L3.Cell
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    (h𝔭 : 𝔭.IsMaximal) {x₀ : V} {n : 𝓞 F} (hx : h x₀ x₀ = κ (ι n)) (hn : n ∉ 𝔭) :
    ∃ L₀ : Submodule (𝓞 K) V, Submodule.IsLattice K L₀ ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h L₀ ∧
      x₀ ∈ L₀ ∧ vd h L₀ 𝔭 ≤ 1 := by
  have hp := h𝔭.isPrime
  have hp0 := ne_bot h𝔭
  have han := LocF.aniso_of_totPosDef hd
  have hx0 : x₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact κι_ne_zero (K := K) (ne_zero_of_notMem hn) hx.symm
  have hm : 0 < finrank K V := Module.finrank_pos_iff_exists_ne_zero.2 ⟨x₀, hx0⟩
  obtain ⟨r, hr⟩ : ∃ r, finrank K V = r + 1 := ⟨finrank K V - 1, by omega⟩
  obtain ⟨y, a, z, c, ho, hzy, hny, hnz, hprod, hc2, hx₀⟩ :=
    exists_family hK hF h𝔭 hs han hx hn r (by omega)
  have hof : ∀ i j, i ≠ j → h ((Fin.cons z y : Fin (r + 1) → V) i) ((Fin.cons z y : Fin (r + 1) → V) j) = 0 := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · intro hij; exact absurd rfl hij
    · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact hzy j
    · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact symm0 hs (hzy i)
    · intro hij
      rw [Fin.cons_succ, Fin.cons_succ]
      exact ho i j fun hh => hij (by rw [hh])
  have hnf : ∀ i, h ((Fin.cons z y : Fin (r + 1) → V) i) ((Fin.cons z y : Fin (r + 1) → V) i) =
      κ (ι ((Fin.cons c a : Fin (r + 1) → 𝓞 F) i)) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [Fin.cons_zero, Fin.cons_zero]; exact hnz
    · rw [Fin.cons_succ, Fin.cons_succ]; exact hny i
  have hP : ∏ i, (Fin.cons c a : Fin (r + 1) → 𝓞 F) i ∉ 𝔭 ^ 2 := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hc2' : c ∉ 𝔭 ^ (1 + 1) := by simpa using hc2
    have hprod' : (∏ i, a i) ∉ 𝔭 ^ (0 + 1) := by simpa using hprod
    have := mul_notMem hp hp0 hc2' hprod'
    simpa using this
  have hne : ∀ i, h ((Fin.cons z y : Fin (r + 1) → V) i) ((Fin.cons z y : Fin (r + 1) → V) i) ≠ 0 := by
    intro i
    rw [hnf]
    refine κι_ne_zero fun h0 => hP ?_
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0]
    exact zero_mem _
  obtain ⟨e, he⟩ := GramDeterminantPositive.exists_basis_of_ortho h _ hr hof hne
  refine ⟨spanO e, isLattice_spanO e,
    integral_spanO e _ (fun i j hij => by rw [he, he]; exact hof i j hij)
      (fun i => by rw [he]; exact hnf i), ?_,
    vd_le_one_of_basis hr e _ (fun i j hij => by rw [he, he]; exact hof i j hij)
      (fun i => by rw [he]; exact hnf i) hP⟩
  rcases hx₀ with rfl | ⟨i, hi⟩
  · exact Submodule.subset_span ⟨0, by rw [he, Fin.cons_zero]⟩
  · exact Submodule.subset_span ⟨i.succ, by rw [he, Fin.cons_succ, hi]⟩
end Formalism.HermitianLattices.Ext.L3.Cell
