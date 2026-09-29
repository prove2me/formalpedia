-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_sub_mem_and_firstOrder_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0ee7928d-0852-5542-9aa3-7426ae4f61e0

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_MvPowerSeries_span_range_X_eq_ker_constantCoeff
import Theorems.Thm_HopfAlgebra_le_span_coinvariant_and_exists_coinvariant_sub_mem
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_levelCoaction_of_subgroup_ideal_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_sub_mem_and_firstOrder_invariant

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped TensorProduct

noncomputable section

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    (hmul : ∀ f ∈ I, MvPowerSeries.subst X.F.toPowerSeries f ∈
      Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)) ∪
         (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B))))
    {L : Type} [CommRing L] [HopfAlgebra B L]
    (π : MvPowerSeries (Fin 2) B →ₐ[B] L) (hπ : Function.Surjective π) (hker : RingHom.ker π = I)
    (hπnil : ∀ i, IsNilpotent (π (MvPowerSeries.X i)))
    (hev : ∀ G, π G = MvFormalGroup.adicEval (⊥ : Ideal L) (fun i => π (MvPowerSeries.X i)) G)
    (hcomul : ∀ i, Coalgebra.comul (R := B) (π (MvPowerSeries.X i)) =
        MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[B] L))
          (Sum.elim (fun j => π (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : L) ⊗ₜ[B] π (MvPowerSeries.X j)))
          (X.F.toPowerSeries i))
    (hcounit : ∀ G, Coalgebra.counit (R := B) (π G) = MvPowerSeries.constantCoeff G)
    [Module.Free B L] [Module.Finite B L]
    (δ : (MvPowerSeries (Fin 2) B ⧸ I ^ (2)) →ₐ[B] (MvPowerSeries (Fin 2) B ⧸ I ^ (2)) ⊗[B] L)
    (hδ : ∀ G, δ (Ideal.Quotient.mk (I ^ (2)) G) =
        MvFormalGroup.adicEval (⊥ : Ideal ((MvPowerSeries (Fin 2) B ⧸ I ^ (2)) ⊗[B] L))
          (fun i => MvFormalGroup.adicEval (⊥ : Ideal ((MvPowerSeries (Fin 2) B ⧸ I ^ (2)) ⊗[B] L))
            (Sum.elim (fun j => Ideal.Quotient.mk (I ^ (2)) (MvPowerSeries.X j) ⊗ₜ[B] (1 : L))
              (fun j => (1 : (MvPowerSeries (Fin 2) B ⧸ I ^ (2))) ⊗ₜ[B] π (MvPowerSeries.X j)))
            (X.F.toPowerSeries i)) G)
    (f : MvPowerSeries (Fin 2) B) (hf : f ∈ I) :
    ∃ f' : MvPowerSeries (Fin 2) B, f' ∈ I ∧
      f - f' ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B)) * I ∧
      δ (Ideal.Quotient.mk (I ^ 2) f') = Ideal.Quotient.mk (I ^ 2) f' ⊗ₜ[B] (1 : L) := by
  classical

  have hIle : I ≤ Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B)) := by
    intro g hg
    have hπg : π g = 0 := by
      have : g ∈ RingHom.ker π := by rw [hker]; exact hg
      exact this
    rw [MvPowerSeries.span_range_X_eq_ker_constantCoeff, RingHom.mem_ker, ← hcounit, hπg, map_zero]

  obtain ⟨δ₁, hδ₁, hco, hcu, hcontI, hlift⟩ :=
    CerednikDrinfeld.FormalODModule.exists_levelCoaction_of_subgroup_ideal_of_ne_zero p X I hnil hmul π hπ hker hπnil hev
      hcomul hcounit 2 two_ne_zero

  have heq : δ₁ = δ := by
    apply AlgHom.ext
    intro s
    obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective s
    rw [hδ₁ G, hδ G]
  subst heq

  have hI2 : ∀ a, a ∈ I ^ 2 → π a = 0 := fun a ha => by
    have : a ∈ RingHom.ker π := by rw [hker]; exact Ideal.pow_le_self two_ne_zero ha
    exact this
  obtain ⟨q, hq_def⟩ : ∃ q : (MvPowerSeries (Fin 2) B ⧸ I ^ 2) →ₐ[B] L, q = Ideal.Quotient.liftₐ (I ^ 2) π hI2 :=
    ⟨_, rfl⟩
  have hq_mk : ∀ G, q (Ideal.Quotient.mk (I ^ 2) G) = π G := fun G => by
    rw [hq_def, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]; rfl
  have hq_surj : Function.Surjective q := fun l => by
    obtain ⟨G, hG⟩ := hπ l
    exact ⟨Ideal.Quotient.mk (I ^ 2) G, (hq_mk G).trans hG⟩
  have hqδ : ∀ s, Algebra.TensorProduct.map q (AlgHom.id B L) (δ₁ s) = Coalgebra.comul (R := B) (q s) := by
    intro s
    obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective s
    rw [hq_mk, ← hlift G, hq_def]
  have hkerq : RingHom.ker q = I.map (Ideal.Quotient.mk (I ^ 2)) := by
    have h1 : RingHom.ker q = RingHom.ker (Ideal.Quotient.lift (I ^ 2) (π : MvPowerSeries (Fin 2) B →+* L) hI2) :=
      Ideal.ext fun x => by rw [RingHom.mem_ker, RingHom.mem_ker, hq_def, Ideal.Quotient.liftₐ_apply]
    have h2 : RingHom.ker (π : MvPowerSeries (Fin 2) B →+* L) = I :=
      Ideal.ext fun x => by rw [RingHom.mem_ker, ← hker, RingHom.mem_ker]; rfl
    rw [h1, Ideal.ker_quotient_lift, h2]
  have hM : RingHom.ker q * I.map (Ideal.Quotient.mk (I ^ 2)) = ⊥ := by
    rw [hkerq, ← Ideal.map_mul, ← pow_two, Ideal.map_quotient_self]

  obtain ⟨-, hH3⟩ := HopfAlgebra.le_span_coinvariant_and_exists_coinvariant_sub_mem (R := B) (L := L)
    (S := MvPowerSeries (Fin 2) B ⧸ I ^ 2) δ₁ hco hcu q hq_surj hqδ (I.map (Ideal.Quotient.mk (I ^ 2))) hM (by
      intro m hm
      obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hm
      have h1 := hcontI 1 g (by rwa [pow_one])
      rw [pow_one] at h1
      refine (Ideal.span_le.mpr ?_) h1
      rintro _ ⟨s, hs, rfl⟩
      refine Ideal.subset_span ⟨s, hs, ?_⟩
      simp [Algebra.TensorProduct.algebraMap_apply])
  obtain ⟨m₀, hm₀M, hm₀inv, hdiff⟩ := hH3 (Ideal.Quotient.mk (I ^ 2) f) (Ideal.mem_map_of_mem _ hf)
  obtain ⟨f₀, hf₀I, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hm₀M
  refine ⟨f₀, hf₀I, ?_, hm₀inv⟩

  have hcomp : (((Bialgebra.counitAlgHom B L).comp q : (MvPowerSeries (Fin 2) B ⧸ I ^ 2) →ₐ[B] B) :
        (MvPowerSeries (Fin 2) B ⧸ I ^ 2) →+* B).comp (Ideal.Quotient.mk (I ^ 2)) =
      (MvPowerSeries.constantCoeff : MvPowerSeries (Fin 2) B →+* B) := by
    ext G
    show Bialgebra.counitAlgHom B L (q (Ideal.Quotient.mk (I ^ 2) G)) = MvPowerSeries.constantCoeff G
    rw [Bialgebra.counitAlgHom_apply, hq_mk, hcounit]
  have hkerεq : RingHom.ker (((Bialgebra.counitAlgHom B L).comp q : (MvPowerSeries (Fin 2) B ⧸ I ^ 2) →ₐ[B] B) :
        (MvPowerSeries (Fin 2) B ⧸ I ^ 2) →+* B) =
      (Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B))).map (Ideal.Quotient.mk (I ^ 2)) := by
    rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk (I ^ 2)) Ideal.Quotient.mk_surjective (RingHom.ker _),
      RingHom.comap_ker, hcomp, MvPowerSeries.span_range_X_eq_ker_constantCoeff]
  rw [hkerεq, ← Ideal.map_mul, ← map_sub] at hdiff
  obtain ⟨g, hg, hgEq⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hdiff
  have h2 : g - (f - f₀) ∈ I ^ 2 := Ideal.Quotient.eq.mp hgEq
  have hI2le : I ^ 2 ≤ Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B)) * I := by
    rw [pow_two]; exact Ideal.mul_mono hIle le_rfl
  have hrw : f - f₀ = g - (g - (f - f₀)) := by ring
  rw [hrw]
  exact Ideal.sub_mem _ hg (hI2le h2)

end

end S_CerednikDrinfeld_FormalODModule_exists_sub_mem_and_firstOrder_invariant
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_sub_mem_and_firstOrder_invariant (solution)
