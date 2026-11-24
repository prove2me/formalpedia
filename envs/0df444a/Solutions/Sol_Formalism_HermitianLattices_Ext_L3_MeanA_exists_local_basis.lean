-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.MeanA.exists_local_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:31.313895+00:00
-- url     : https://prove2.me/submissions/1ee0a109-6128-405e-91d1-878849067092

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
variable {R F V : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
  [IsFractionRing R F] [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
  [FiniteDimensional F V]
namespace Formalism.HermitianLattices.Ext.L3.MeanA
theorem _root_.solution (M : Submodule R V) (hfg : M.FG)
    (hspan : Submodule.span F (M : Set V) = ⊤) {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) :
    ∃ (x : Fin (finrank F V) → M) (s : R), s ∉ 𝔭 ∧ LinearIndependent R x ∧
      ∀ v : M, s • v ∈ Submodule.span R (Set.range x) := by
  have := h𝔭
  let : Field (R ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  have : Module.Finite R M := Module.Finite.iff_fg.2 hfg
  let Q := M ⧸ (𝔭 • ⊤ : Submodule R M)
  have : Module.Finite (R ⧸ 𝔭) Q := Module.Finite.of_restrictScalars_finite R _ _
  let b := Module.finBasis (R ⧸ 𝔭) Q
  choose x hx using fun i => Submodule.Quotient.mk_surjective _ (b i)
  have hli : LinearIndependent F (M.subtype ∘ x) := by
    refine Ideal.FinrankQuotientMap.linearIndependent_of_nontrivial (S := R ⧸ 𝔭) F ?_ M.subtype
      M.injective_subtype (Submodule.mkQ (𝔭 • ⊤ : Submodule R M)) ?_
    · rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]; exact h𝔭.ne_top
    · have : (Submodule.mkQ (𝔭 • ⊤ : Submodule R M)) ∘ x = b := by
        funext i; exact hx i
      rw [this]; exact b.linearIndependent
  have hsup : (⊤ : Submodule R M) ≤ Submodule.span R (Set.range x) ⊔ 𝔭 • ⊤ := by
    intro v _
    have hv : (Submodule.Quotient.mk v : Q) ∈ Submodule.span (R ⧸ 𝔭) (Set.range b) := b.mem_span _
    rw [← @Submodule.restrictScalars_mem R,
      Submodule.restrictScalars_span R (R ⧸ 𝔭) Ideal.Quotient.mk_surjective] at hv
    have hb : Set.range b = (Submodule.mkQ (𝔭 • ⊤ : Submodule R M)) '' Set.range x := by
      rw [← Set.range_comp]; congr 1; funext i; exact (hx i).symm
    rw [hb, ← Submodule.map_span] at hv
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 hv
    rw [Submodule.mkQ_apply, Submodule.Quotient.eq] at e
    have : v = y - (y - v) := by abel
    rw [this]
    exact sub_mem (Submodule.mem_sup_left hy) (Submodule.mem_sup_right e)
  obtain ⟨s, hs1, hs⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (Module.Finite.fg_top (R := R) (M := M)) le_rfl hsup
  have hs𝔭 : s ∉ 𝔭 := fun h => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have := sub_mem h hs1; simpa using this))
  have hsv : ∀ v : M, s • v ∈ Submodule.span R (Set.range x) := fun v =>
    hs (Submodule.smul_mem_pointwise_smul v s ⊤ trivial)
  have hs0 : algebraMap R F s ≠ 0 := by
    intro h0
    have : s = 0 := (IsFractionRing.injective R F) (by rw [h0, map_zero])
    exact hs𝔭 (this ▸ 𝔭.zero_mem)
  have hsp : ⊤ ≤ Submodule.span F (Set.range (M.subtype ∘ x)) := by
    rw [← hspan, Submodule.span_le]
    intro v hv
    have h1 := hsv ⟨v, hv⟩
    have h2 : (s • v : V) ∈ Submodule.span F (Set.range (M.subtype ∘ x)) := by
      have h3 : M.subtype (s • ⟨v, hv⟩) ∈ (Submodule.span R (Set.range x)).map M.subtype :=
        Submodule.mem_map_of_mem h1
      rw [Submodule.map_span, ← Set.range_comp] at h3
      exact Submodule.span_le_restrictScalars R F _ h3
    have h4 : v = (algebraMap R F s)⁻¹ • (s • v) := by
      rw [← algebraMap_smul F s v, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [h4]
    exact Submodule.smul_mem _ _ h2
  have hcard : finrank (R ⧸ 𝔭) Q = finrank F V := by
    have := finrank_eq_card_basis (Basis.mk hli hsp)
    simpa using this.symm
  have hliR : LinearIndependent R x := by
    have := hli.restrict_scalars (R := R) (by
      intro a b hab
      simpa [Algebra.smul_def] using hab |> fun h => (IsFractionRing.injective R F) (by simpa [Algebra.smul_def] using h))
    exact LinearIndependent.of_comp M.subtype this
  refine ⟨x ∘ Fin.cast hcard.symm, s, hs𝔭, hliR.comp _ (Fin.cast_injective _), fun v => ?_⟩
  have : Set.range (x ∘ Fin.cast hcard.symm) = Set.range x :=
    (Fin.castOrderIso hcard.symm).surjective.range_comp x
  rw [this]; exact hsv v
end Formalism.HermitianLattices.Ext.L3.MeanA
