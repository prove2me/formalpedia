-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.rowColength
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:46:39.414923+00:00
-- url     : https://prove2.me/submissions/7680c742-4055-4e5d-8a12-2dd13d595602

import Definitions.Def_Formalism_WachLatticeTwists_Statement
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_RowCol
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_RowCol_length_le_of_killed_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
namespace Formalism.RepresentationBoundsCohomology
theorem _root_.solution : Formalism.RepresentationBoundsCohomology.StatRowColength := by
  intro O _ _ _ M _ _ _ I ℓ e hI
  classical
  set T := Submodule.torsion O M with hT
  haveI : Module.Free O (M ⧸ T) := Module.free_of_finite_type_torsion_free'
  let bQ := Module.Free.chooseBasis O (M ⧸ T)
  choose m hm using fun i => T.mkQ_surjective (bQ i)
  have hli : LinearIndependent O m := by
    apply LinearIndependent.of_comp T.mkQ
    have hc : T.mkQ ∘ m = bQ := funext hm
    rw [hc]
    exact bQ.linearIndependent
  have hcard := hli.fintype_card_le_finrank
  let G0 : (Module.Free.ChooseBasisIndex O (M ⧸ T) → O) →ₗ[O] M :=
    ∑ i, (LinearMap.toSpanSingleton O M (m i)).comp (LinearMap.proj i)
  have hG0 : ∀ c, G0 c = ∑ i, c i • m i := by
    intro c
    simp [G0]
  let N : Submodule O (M ⧸ I) := LinearMap.range (I.mkQ.comp T.subtype)
  let G : (Module.Free.ChooseBasisIndex O (M ⧸ T) → O) →ₗ[O] ((M ⧸ I) ⧸ N) :=
    N.mkQ.comp (I.mkQ.comp G0)
  have hGs : Function.Surjective G := by
    intro y
    obtain ⟨z, rfl⟩ := N.mkQ_surjective y
    obtain ⟨x, rfl⟩ := I.mkQ_surjective z
    refine ⟨fun i => bQ.repr (T.mkQ x) i, ?_⟩
    have h1 : T.mkQ (G0 (fun i => bQ.repr (T.mkQ x) i)) = T.mkQ x := by
      rw [hG0, map_sum]
      simp only [map_smul, hm]
      exact bQ.sum_repr (T.mkQ x)
    have h2 : G0 (fun i => bQ.repr (T.mkQ x) i) - x ∈ T := by
      rw [← Submodule.Quotient.eq]
      exact h1
    show N.mkQ (I.mkQ (G0 _)) = N.mkQ (I.mkQ x)
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
    apply (Submodule.Quotient.eq N).mpr
    refine LinearMap.mem_range.mpr ⟨⟨_, h2⟩, ?_⟩
    simp
  have hGk : ∀ p : (M ⧸ I) ⧸ N, ((ℓ : O) ^ e) • p = 0 := by
    intro p
    obtain ⟨z, rfl⟩ := N.mkQ_surjective p
    obtain ⟨x, rfl⟩ := I.mkQ_surjective z
    have h0 : I.mkQ (((ℓ : O) ^ e) • x) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hI x
    rw [← map_smul, ← map_smul, h0, map_zero]
  have hP := Formalism.RepresentationBoundsCohomology.RowCol.length_le_of_killed_pow ((ℓ : O)) e G hGs hGk
  have hlen := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
    (LinearMap.exact_subtype_mkQ N)
  have hN : Module.length O N ≤ Module.length O T :=
    Module.length_le_of_surjective (I.mkQ.comp T.subtype).rangeRestrict
      (LinearMap.surjective_rangeRestrict _)
  rw [hlen, add_comm]
  refine add_le_add ?_ hN
  have hcard' : ((Fintype.card (Module.Free.ChooseBasisIndex O (M ⧸ T)) : ℕ) : ℕ∞) ≤
      (Module.finrank O M : ℕ∞) := by exact_mod_cast hcard
  calc _ ≤ (e : ℕ∞) * ((Fintype.card (Module.Free.ChooseBasisIndex O (M ⧸ T)) : ℕ∞) *
        Module.length O (O ⧸ Ideal.span {(ℓ : O)})) := hP
    _ = (Fintype.card (Module.Free.ChooseBasisIndex O (M ⧸ T)) : ℕ∞) *
        ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})) := mul_left_comm _ _ _
    _ ≤ _ := mul_le_mul' hcard' le_rfl
end Formalism.RepresentationBoundsCohomology
