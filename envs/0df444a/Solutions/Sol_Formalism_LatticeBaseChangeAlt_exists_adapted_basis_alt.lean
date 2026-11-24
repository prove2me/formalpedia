-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.exists_adapted_basis_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:51:12.047984+00:00
-- url     : https://prove2.me/submissions/455ebfc6-fba7-41b2-9e7b-b9e912e27e72

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Lemmata_MiscLemmasO_Imports
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_ExistsSmulMemOfMemSpan
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_exists_smul_mem_of_mem_span_alt
import Theorems.Thm_Formalism_LatticeIndexTer_latBasis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    (M : Submodule O V) (V' : Submodule K V) (hM : Formalism.LatticeIndexTer.IsLat O K V M) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (s : Set (Fin (finrank K V))),
      M ≤ Submodule.span O (Set.range b) ∧ (∀ i ∈ s, b i ∈ M ∧ b i ∈ V') ∧
        V' ≤ Submodule.span K (b '' s) := by
  obtain ⟨b0, hb0⟩ := Formalism.LatticeIndexTer.latBasis O K V M hM
  have hli0 : LinearIndependent O b0 :=
    (LinearIndependent.iff_fractionRing O K).mpr b0.linearIndependent
  let bO : Basis (Fin (finrank K V)) O M :=
    (Basis.span hli0).map (LinearEquiv.ofEq _ _ hb0.symm)
  obtain ⟨n, bM, bN, f, a, snf⟩ :=
    Submodule.smithNormalForm bO ((V'.restrictScalars O).comap M.subtype)
  have hliO : LinearIndependent O (fun i => (bM i : V)) :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hliK : LinearIndependent K (fun i => (bM i : V)) :=
    (LinearIndependent.iff_fractionRing O K).mp hliO
  have hspanO : M ≤ Submodule.span O (Set.range (fun i => (bM i : V))) := by
    intro m hm
    have h1 : (⟨m, hm⟩ : M) ∈ Submodule.span O (Set.range bM) := by
      rw [bM.span_eq]; trivial
    have h2 := Submodule.mem_map_of_mem (f := M.subtype) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
  have hspanK : ⊤ ≤ Submodule.span K (Set.range (fun i => (bM i : V))) := by
    rw [← hM.2]
    apply Submodule.span_le.mpr
    intro m hm
    exact Submodule.span_le_restrictScalars O K _ (hspanO hm)
  let b : Basis (Fin (finrank K V)) K V := Basis.mk hliK hspanK
  have hb : ∀ i, b i = (bM i : V) := fun i => by simp [b]
  have hrange : Set.range b = Set.range (fun i => (bM i : V)) := by
    ext x; simp [hb]
  refine ⟨b, Set.range f, ?_, ?_, ?_⟩
  · rw [hrange]; exact hspanO
  · rintro _ ⟨k, rfl⟩
    rw [hb]
    refine ⟨(bM (f k)).2, ?_⟩
    have hmem : ((bN k : M) : V) ∈ V' := (bN k).2
    rw [snf k] at hmem
    have ha : a k ≠ 0 := by
      intro h0
      have : (bN k : M) = 0 := by rw [snf k, h0, zero_smul]
      exact bN.ne_zero k (Subtype.ext this)
    have haK : algebraMap O K (a k) ≠ 0 := by
      simpa using (IsFractionRing.injective O K).ne ha
    have h3 : algebraMap O K (a k) • ((bM (f k) : M) : V) ∈ V' := by
      rw [algebraMap_smul]; simpa using hmem
    exact (V'.smul_mem_iff haK).mp h3
  · intro v hv
    have hv' : v ∈ Submodule.span K (M : Set V) := by rw [hM.2]; trivial
    obtain ⟨c, hc, hcv⟩ := exists_smul_mem_of_mem_span_alt O K V M v hv'
    have hcK : algebraMap O K c ≠ 0 := by
      simpa using (IsFractionRing.injective O K).ne hc
    have hcV : c • v ∈ V' := by
      rw [← algebraMap_smul K c]; exact V'.smul_mem _ hv
    let w : ((V'.restrictScalars O).comap M.subtype : Submodule O M) := ⟨⟨c • v, hcv⟩, hcV⟩
    have hw : w ∈ Submodule.span O (Set.range bN) := by rw [bN.span_eq]; trivial
    have key : ∀ u ∈ Submodule.span O (Set.range bN),
        ((u : M) : V) ∈ Submodule.span K (b '' Set.range f) := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        rw [snf k]
        have : ((a k • bM (f k) : M) : V) = algebraMap O K (a k) • b (f k) := by
          rw [hb, algebraMap_smul]; rfl
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f k, ⟨k, rfl⟩, rfl⟩)
      | zero => simp
      | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        have : (((r • x : _) : M) : V) = algebraMap O K r • ((x : M) : V) := by
          rw [algebraMap_smul]; rfl
        rw [this]
        exact Submodule.smul_mem _ _ hx
    have h4 : algebraMap O K c • v ∈ Submodule.span K (b '' Set.range f) := by
      rw [algebraMap_smul]; exact key w hw
    exact (Submodule.smul_mem_iff _ hcK).mp h4
end Formalism.LatticeBaseChangeAlt
