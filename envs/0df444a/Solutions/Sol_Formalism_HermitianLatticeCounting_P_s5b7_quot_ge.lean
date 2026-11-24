-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5b7_quot_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:25.207814+00:00
-- url     : https://prove2.me/submissions/9c660eb7-c106-4c35-b6d9-1f3315e29a27

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module
variable {O : Type} [CommRing O] [IsDedekindDomain O]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (p : Ideal O) [hp : p.IsMaximal] [Finite (O ⧸ p)] (Y : Type) [AddCommGroup Y]
    [Module O Y] [Module.Finite O Y] [Module.IsTorsionFree O Y] :
    Finite (Y ⧸ p • (⊤ : Submodule O Y)) ∧
    Nat.card (O ⧸ p) ^ finrank O Y ≤ Nat.card (Y ⧸ p • (⊤ : Submodule O Y)) := by
  classical
  let : Field (O ⧸ p) := Ideal.Quotient.field p
  have : Module.Finite (O ⧸ p) (Y ⧸ p • (⊤ : Submodule O Y)) :=
    Module.Finite.of_restrictScalars_finite O _ _
  have hfin : Finite (Y ⧸ p • (⊤ : Submodule O Y)) := Module.finite_of_finite (O ⧸ p)
  refine ⟨hfin, ?_⟩
  rw [Module.natCard_eq_pow_finrank (K := O ⧸ p) (V := Y ⧸ p • (⊤ : Submodule O Y))]
  apply Nat.pow_le_pow_right Nat.card_pos
  set a := finrank (O ⧸ p) (Y ⧸ p • (⊤ : Submodule O Y)) with ha
  let b := Module.finBasis (O ⧸ p) (Y ⧸ p • (⊤ : Submodule O Y))
  choose y hy using fun i => Submodule.Quotient.mk_surjective _ (b i)
  set N := Submodule.span O (Set.range y) with hN
  have hsup : ∀ z : Y, ∃ n ∈ N, z - n ∈ p • (⊤ : Submodule O Y) := by
    intro z
    choose c hc using fun i => Ideal.Quotient.mk_surjective (b.repr (Submodule.Quotient.mk z) i)
    refine ⟨∑ i, c i • y i, Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
    conv_lhs => rw [← b.sum_repr (Submodule.Quotient.mk z)]
    have e1 : (Submodule.Quotient.mk (∑ i, c i • y i) : Y ⧸ p • (⊤ : Submodule O Y)) =
        ∑ i, Submodule.Quotient.mk (c i • y i) := map_sum (Submodule.mkQ (p • ⊤)) _ _
    rw [e1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.Quotient.mk_smul, hy, ← hc]
    rfl
  have htop : (⊤ : Submodule O (Y ⧸ N)) ≤ p • (⊤ : Submodule O (Y ⧸ N)) := by
    intro q _
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨n, hn, hz⟩ := hsup z
    have h1 : (Submodule.Quotient.mk z : Y ⧸ N) = N.mkQ (z - n) := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero N).mpr hn,
        sub_zero]
    rw [h1]
    have h2 : (p • (⊤ : Submodule O Y)).map N.mkQ ≤ p • (⊤ : Submodule O (Y ⧸ N)) := by
      rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
    exact h2 ⟨_, hz, rfl⟩
  obtain ⟨s, hs1, hs⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul p
    (⊤ : Submodule O (Y ⧸ N)) Module.Finite.fg_top htop
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hp.ne_top
    rw [Ideal.eq_top_iff_one]
    simpa using p.neg_mem hs1
  have hsN : ∀ z : Y, s • z ∈ N := by
    intro z
    have := hs (Submodule.Quotient.mk z) trivial
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
  let F : Y →ₗ[O] N := (LinearMap.lsmul O Y s).codRestrict N hsN
  have hF : Function.Injective F := by
    intro u v huv
    have : s • u = s • v := congrArg Subtype.val huv
    exact (smul_right_injective Y hs0) this
  have : IsNoetherian O Y := isNoetherian_of_isNoetherianRing_of_finite O Y
  calc finrank O Y ≤ finrank O N := LinearMap.finrank_le_finrank_of_injective hF
    _ ≤ Fintype.card (Fin a) := finrank_range_le_card y
    _ = a := Fintype.card_fin a
end Formalism.HermitianLatticeCounting.P
