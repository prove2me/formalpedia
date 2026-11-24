-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.cnt_biUnion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:41:23.748846+00:00
-- url     : https://prove2.me/submissions/7c253517-0aa5-4a1d-8f1f-f075363f4171

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SigmaCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
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
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ)
    (n : 𝓞 F) (hfin : Finite (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)))
    {ι : Type*} (s : Finset ι) (Ω : ι → Set V)
    (hst : ∀ i ∈ s, ∀ y ∈ Ω i, ∀ z ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V), y + z ∈ Ω i)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (Ω i) (Ω j)) :
    cnt h A 𝔭 k n (⋃ i ∈ s, Ω i) = ∑ i ∈ s, cnt h A 𝔭 k n (Ω i) := by
  classical
  have := Fintype.ofFinite (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A))
  unfold cnt
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_biUnion]
  · congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨y, e, hc, i, hi, hy⟩
      exact ⟨i, hi, y, e, hc, hy⟩
    · rintro ⟨i, hi, y, e, hc, hy⟩
      exact ⟨y, e, hc, i, hi, hy⟩
  · intro i hi j hj hij
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    obtain ⟨y, e, -, hy⟩ := hx
    obtain ⟨y', e', -, hy'⟩ := hx'
    have h1 : y' - y ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A) := by
      rw [← Submodule.Quotient.eq, e, e']
    rw [Submodule.mem_smul_top_iff] at h1
    have h2 := hst i hi y hy _ h1
    have h3 : (y : V) + ((y' - y : ↥A) : V) = y' := by
      simp
    rw [h3] at h2
    exact Set.disjoint_left.1 (hdis i hi j hj hij) h2 hy'
end Formalism.HermitianLattices.Ext.L3.LIOrb
