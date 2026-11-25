-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Cell.exists_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:24:00.232252+00:00
-- url     : https://prove2.me/submissions/337235e0-d6c8-48ae-83c0-cae9e8ba83c1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOfNormRepCountNeZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandG
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormalise
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_symm0
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_normalise
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_pair
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_Cell____inj_0092c5d8b628
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_InI_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_GramDeterminantPositive_exists_ortho_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_zero
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
open LocalSpans idealPowerSpanBounds localizedQuotients WCA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)}
variable [FiniteDimensional K V]
namespace Formalism.HermitianLattices.Ext.L3.Cell
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (han : ∀ x, h x x = 0 → x = 0) {x₀ : V} {n : 𝓞 F}
    (hx : h x₀ x₀ = κ (ι n)) (hn : n ∉ 𝔭) :
    ∀ r : ℕ, r + 1 ≤ finrank K V → ∃ (y : Fin r → V) (a : Fin r → 𝓞 F) (z : V) (c : 𝓞 F),
      (∀ i j, i ≠ j → h (y i) (y j) = 0) ∧ (∀ i, h z (y i) = 0) ∧
      (∀ i, h (y i) (y i) = κ (ι (a i))) ∧ h z z = κ (ι c) ∧ (∏ i, a i) ∉ 𝔭 ∧ c ∉ 𝔭 ^ 2 ∧
      (z = x₀ ∨ ∃ i, y i = x₀) := by
  have hp := h𝔭.isPrime
  intro r
  induction r with
  | zero =>
    intro _
    refine ⟨fun i => i.elim0, fun i => i.elim0, x₀, n, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, hx, ?_, fun hm => hn (Ideal.pow_le_self two_ne_zero hm), Or.inl rfl⟩
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    exact fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  | succ r ih =>
    intro hr
    obtain ⟨y, a, z, c, ho, hzy, hny, hnz, hprod, hc2, hx₀⟩ := ih (by omega)
    obtain ⟨e₀, he₀, hoe⟩ := GramDeterminantPositive.exists_ortho_ne_zero h (Fin.cons z y : Fin (r + 1) → V)
      (by omega)
    obtain ⟨μ, ae, hne, hae2⟩ := exists_normalise hF h𝔭 hs han he₀
    have hze : h z (μ • e₀) = 0 := by
      have := hoe 0
      rw [Fin.cons_zero] at this
      rw [map_smul, this, smul_zero]
    have hye : ∀ i, h (y i) (μ • e₀) = 0 := fun i => by
      have := hoe i.succ
      rw [Fin.cons_succ] at this
      rw [map_smul, this, smul_zero]
    set e := μ • e₀ with he
    have key : ∃ u w : V, ∃ b₁ b₂ : 𝓞 F, h u u = κ (ι b₁) ∧ h w w = κ (ι b₂) ∧ b₁ ∉ 𝔭 ∧
        b₂ ∉ 𝔭 ^ 2 ∧ h w u = 0 ∧ (∀ i, h u (y i) = 0 ∧ h w (y i) = 0) ∧
        (u = x₀ ∨ ∃ i, y i = x₀) := by
      by_cases hcp : c ∈ 𝔭
      · have hx₀' : ∃ i, y i = x₀ := by
          rcases hx₀ with rfl | h1
          · exact absurd hcp (by rw [κι_inj (hnz.symm.trans hx)]; exact hn)
          · exact h1
        by_cases hap : ae ∈ 𝔭
        · obtain ⟨u, w, b₁, b₂, h1, h2, h3, h4, h5, h6⟩ :=
            exists_pair hK hF h𝔭 hs hze hnz hne hc2 hae2 hcp hap
          exact ⟨u, w, b₁, b₂, h1, h2, h3, h4, h5,
            fun i => h6 _ (hzy i) (symm0 hs (hye i)), Or.inr hx₀'⟩
        · exact ⟨e, z, ae, c, hne, hnz, hap, hc2, hze,
            fun i => ⟨symm0 hs (hye i), hzy i⟩, Or.inr hx₀'⟩
      · exact ⟨z, e, c, ae, hnz, hne, hcp, hae2, symm0 hs hze,
          fun i => ⟨hzy i, symm0 hs (hye i)⟩, hx₀⟩
    obtain ⟨u, w, b₁, b₂, h1, h2, h3, h4, h5, h6, h7⟩ := key
    refine ⟨Fin.cons u y, Fin.cons b₁ a, w, b₂, ?_, ?_, ?_, h2, ?_, h4, Or.inr ?_⟩
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · intro hij; exact absurd rfl hij
      · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact (h6 j).1
      · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact symm0 hs (h6 i).1
      · intro hij
        rw [Fin.cons_succ, Fin.cons_succ]
        exact ho i j fun hh => hij (by rw [hh])
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [Fin.cons_zero]; exact h5
      · rw [Fin.cons_succ]; exact (h6 i).2
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [Fin.cons_zero, Fin.cons_zero]; exact h1
      · rw [Fin.cons_succ, Fin.cons_succ]; exact hny i
    · rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      exact fun hm => (hp.mem_or_mem hm).elim h3 hprod
    · rcases h7 with rfl | ⟨i, hi⟩
      · exact ⟨0, by rw [Fin.cons_zero]⟩
      · exact ⟨i.succ, by rw [Fin.cons_succ]; exact hi⟩
end Formalism.HermitianLattices.Ext.L3.Cell
