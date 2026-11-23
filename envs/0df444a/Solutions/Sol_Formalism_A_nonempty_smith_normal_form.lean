-- Prove2me | solution 1 for Formalism.A.nonempty_smith_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:33.48667+00:00
-- url     : https://prove2.me/submissions/b2079426-8b4b-4a87-a647-d06774a4f3ee

import Definitions.Def_Formalism_SmithDeterminants_DefsDVR
import Definitions.Def_Formalism_SmithDeterminants_DivisibilityChains_SmithExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.A
open Module
namespace Formalism.A
theorem _root_.solution {R M : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (y : M →ₗ[R] M) :
    Nonempty (SmithData y (Module.finrank R M)) := by
  classical

  let b0 : Module.Basis (Fin (Module.finrank R M)) R M := Module.finBasis R M
  obtain ⟨n, snf⟩ := Submodule.smithNormalForm b0 (LinearMap.range y)
  obtain ⟨k, bK⟩ := Submodule.basisOfPid b0 (LinearMap.ker y)

  have hx : ∀ i, ∃ x : M, y x = (snf.bN i : M) := fun i => LinearMap.mem_range.mp (snf.bN i).2
  choose x hx using hx
  let s : LinearMap.range y →ₗ[R] M := snf.bN.constr R x
  have hys : y ∘ₗ s = (LinearMap.range y).subtype := by
    refine snf.bN.ext fun i => ?_
    simp [s, hx]
  have hyS : ∀ z : LinearMap.range y, y (s z) = z := fun z => by
    simpa using LinearMap.congr_fun hys z
  have hrr : ∀ m : M, (y.rangeRestrict m : M) = y m := fun m => rfl
  let pK : M →ₗ[R] M := LinearMap.id - s ∘ₗ y.rangeRestrict
  have hpK : ∀ m : M, pK m = m - s (y.rangeRestrict m) := fun m => rfl
  have hker : ∀ m : M, pK m ∈ LinearMap.ker y := by
    intro m
    rw [LinearMap.mem_ker, hpK, map_sub, hyS, hrr, sub_self]
  have hrz : ∀ (c : LinearMap.ker y) (z : LinearMap.range y),
      y.rangeRestrict ((c : M) + s z) = z := by
    intro c z
    apply Subtype.ext
    rw [hrr, map_add, LinearMap.mem_ker.mp c.2, zero_add, hyS]

  let fwd : (LinearMap.ker y × LinearMap.range y) →ₗ[R] M := (LinearMap.ker y).subtype.coprod s
  let bwd : M →ₗ[R] (LinearMap.ker y × LinearMap.range y) :=
    LinearMap.prod (LinearMap.codRestrict (LinearMap.ker y) pK hker)
      y.rangeRestrict
  have hf : ∀ (c : LinearMap.ker y) (z : LinearMap.range y), fwd (c, z) = (c : M) + s z := by
    intro c z
    simp [fwd]
  have h1 : fwd ∘ₗ bwd = LinearMap.id := by
    refine LinearMap.ext fun m => ?_
    show fwd (bwd m) = m
    have hb : bwd m = (⟨m - s (y.rangeRestrict m), hker m⟩, y.rangeRestrict m) := rfl
    rw [hb, hf]
    exact sub_add_cancel m _
  have h2 : bwd ∘ₗ fwd = LinearMap.id := by
    refine LinearMap.ext fun p => ?_
    obtain ⟨c, z⟩ := p
    show bwd (fwd (c, z)) = (c, z)
    rw [hf]
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      show (c : M) + s z - s (y.rangeRestrict ((c : M) + s z)) = c
      rw [hrz]
      exact add_sub_cancel_right _ _
    · exact hrz c z
  let e : (LinearMap.ker y × LinearMap.range y) ≃ₗ[R] M := LinearEquiv.ofLinear fwd bwd h1 h2

  let B : Module.Basis (Fin k ⊕ Fin n) R M := (bK.prod snf.bN).map e
  have hB1 : ∀ l, y (B (Sum.inl l)) = 0 := by
    intro l
    have : B (Sum.inl l) = bK l := by
      simp [B, e, hf]
    rw [this]
    exact LinearMap.mem_ker.mp (bK l).2
  have hB2 : ∀ i, y (B (Sum.inr i)) = snf.a i • snf.bM (snf.f i) := by
    intro i
    have : B (Sum.inr i) = s (snf.bN i) := by
      simp [B, e, hf]
    rw [this, hyS, snf.snf i]

  have hcard : k + n = Module.finrank R M := by
    simpa using (Module.finrank_eq_card_basis B).symm
  have hcompl : Fintype.card (Fin k) = Fintype.card ↥(Set.range snf.f)ᶜ := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective snf.f.injective, Fintype.card_fin,
      Fintype.card_fin, Fintype.card_fin]
    omega
  let τ : Fin k ≃ ↥(Set.range snf.f)ᶜ := Fintype.equivOfCardEq hcompl
  let σ : Fin k ⊕ Fin n ≃ Fin (Module.finrank R M) :=
    (Equiv.sumComm _ _).trans ((Equiv.sumCongr (Equiv.ofInjective snf.f snf.f.injective) τ).trans
      (Equiv.Set.sumCompl (Set.range snf.f)))
  have hσ : ∀ i, σ (Sum.inr i) = snf.f i := by
    intro i
    simp [σ]
  refine ⟨SmithData.mk (B.reindex σ) snf.bM (fun j => Sum.elim (fun _ => 0) snf.a (σ.symm j)) ?_⟩
  intro j
  obtain ⟨z, rfl⟩ := σ.surjective j
  rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  rcases z with l | i
  · rw [hB1 l, Sum.elim_inl, zero_smul]
  · rw [hB2 i, hσ i, Sum.elim_inr]
end Formalism.A
