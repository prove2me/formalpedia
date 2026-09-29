-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.isOpen_setOf_edgeNondegAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/6d29cdaf-43d0-5496-a104-fa8d92cc3852

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_isOpen_setOf_edgeNondegAt

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace OpenLocus

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem isOpen_setOf_not_mem_sup (L : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B L))
    (hN : Module.Invertible B (latticeBaseChange 𝒪 K B L ⧸ N)) (x : latticeBaseChange 𝒪 K B L) :
    IsOpen {𝔭 : PrimeSpectrum B | x ∉ N ⊔ (𝔭.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L))} := by
  haveI := hN
  rw [isOpen_iff_forall_mem_open]
  intro 𝔭 h𝔭
  have hq : N.mkQ x ∉ (𝔭.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L ⧸ N)) := by
    intro hq
    apply h𝔭
    have : x ∈ ((𝔭.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L)).map N.mkQ).comap N.mkQ := by
      rw [Submodule.mem_comap, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]; exact hq
    rwa [Submodule.comap_map_mkQ] at this
  obtain ⟨φ, hφ⟩ := exists_linearMap_apply_not_mem 𝔭.asIdeal (N.mkQ x) hq
  refine ⟨(PrimeSpectrum.basicOpen (φ (N.mkQ x)) : Set (PrimeSpectrum B)), ?_, (PrimeSpectrum.basicOpen _).isOpen,
    (PrimeSpectrum.mem_basicOpen _ _).2 hφ⟩
  intro 𝔮 h𝔮 hmem
  apply (PrimeSpectrum.mem_basicOpen _ _).1 h𝔮
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
  have hz' : N.mkQ z ∈ (𝔮.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L ⧸ N)) := by
    have := Submodule.mem_map_of_mem (f := N.mkQ) hz
    rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this
  have hxz : N.mkQ x = N.mkQ z := by
    rw [← hyz, map_add, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2 hy, zero_add]
  rw [hxz]
  refine Submodule.smul_induction_on (p := fun y => φ y ∈ 𝔮.asIdeal) hz' (fun r hr n _ => ?_) (fun a b ha hb => ?_)
  · show φ (r • n) ∈ 𝔮.asIdeal
    rw [LinearMap.map_smul, smul_eq_mul]; exact Ideal.mul_mem_right _ _ hr
  · show φ (a + b) ∈ 𝔮.asIdeal
    rw [LinearMap.map_add]; exact Ideal.add_mem _ ha hb

theorem tmul_add_smul_not_mem_iff (L : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B L))
    (𝔭 : Ideal B) (hπ : algebraMap 𝒪 B π ∈ 𝔭) (t w : ↥L.1) :
    ((1 : B) ⊗ₜ[𝒪] (t + π • w) ∉ N ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L))) ↔
      ((1 : B) ⊗ₜ[𝒪] t ∉ N ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L))) := by
  have he : (1 : B) ⊗ₜ[𝒪] (π • w) ∈ N ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L)) := by
    apply Submodule.mem_sup_right
    rw [TensorProduct.tmul_smul, ← algebraMap_smul B π ((1 : B) ⊗ₜ[𝒪] w)]
    exact Submodule.smul_mem_smul hπ Submodule.mem_top
  rw [TensorProduct.tmul_add]
  constructor
  · intro h ht
    exact h (Submodule.add_mem _ ht he)
  · intro h hs
    apply h
    have := Submodule.sub_mem _ hs he
    rwa [add_sub_cancel_right] at this

theorem exists_finite_reps (L : FullLattice 𝒪 K) [Finite (𝒪 ⧸ Ideal.span {π})] :
    ∃ T : Set ↥L.1, T.Finite ∧ ∀ v : ↥L.1, ∃ t ∈ T, ∃ w : ↥L.1, v = t + π • w := by
  classical
  haveI : Module.Finite 𝒪 ↥L.1 := Module.Finite.iff_fg.mpr L.2.1
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := 𝒪) (M := ↥L.1)

  let σ : 𝒪 ⧸ Ideal.span {π} → 𝒪 := fun c => (Ideal.Quotient.mk_surjective c).choose
  have hσ : ∀ c, Ideal.Quotient.mk (Ideal.span {π}) (σ c) = c := fun c => (Ideal.Quotient.mk_surjective c).choose_spec
  refine ⟨Set.range (fun c : Fin n → 𝒪 ⧸ Ideal.span {π} => ∑ i, σ (c i) • g i), Set.finite_range _, ?_⟩
  intro v
  have hv : v ∈ Submodule.span 𝒪 (Set.range g) := by rw [hg]; exact Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun 𝒪).1 hv

  have hb : ∀ i, ∃ b : 𝒪, a i - σ (Ideal.Quotient.mk (Ideal.span {π}) (a i)) = π * b := by
    intro i
    have : a i - σ (Ideal.Quotient.mk (Ideal.span {π}) (a i)) ∈ Ideal.span {π} := by
      rw [← Ideal.Quotient.eq, hσ]
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨b, by rw [← hb, mul_comm]⟩
  choose b hb using hb
  refine ⟨_, ⟨fun i => Ideal.Quotient.mk _ (a i), rfl⟩, ∑ i, b i • g i, ?_⟩
  rw [Finset.smul_sum, ← Finset.sum_add_distrib, ← ha]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, ← add_smul]
  congr 1
  have := hb i
  linear_combination this

theorem algebraMap_mem_of_isNilpotent (hB : IsNilpotent (algebraMap 𝒪 B π)) (𝔭 : PrimeSpectrum B) :
    algebraMap 𝒪 B π ∈ 𝔭.asIdeal := by
  obtain ⟨n, hn⟩ := hB
  exact 𝔭.isPrime.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)

end OpenLocus

open OpenLocus in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪) [Finite (𝒪 ⧸ Ideal.span {π})]
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K) :
    IsOpen {𝔭 : PrimeSpectrum B | d.EdgeNondegAt π 𝔭.asIdeal M' M} := by
  classical
  by_cases h12 : M'.1 ≤ M.1 ∧ ∀ v : ↥M.1, (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ M'.1
  swap
  ·
    have : {𝔭 : PrimeSpectrum B | d.EdgeNondegAt π 𝔭.asIdeal M' M} = ∅ := by
      ext 𝔭
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact h12 ⟨h.1, h.2.1⟩
    rw [this]; exact isOpen_empty
  obtain ⟨h1, h2⟩ := h12

  let S₃ : Set (PrimeSpectrum B) := {𝔭 | ∀ v : ↥M.1, (v : Fin 2 → K) ∉ M'.1 →
      (1 : B) ⊗ₜ[𝒪] v ∉ d.line M ⊔ (𝔭.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))}
  let S₄ : Set (PrimeSpectrum B) := {𝔭 | ∀ v' : ↥M'.1,
      (¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K)) →
      (1 : B) ⊗ₜ[𝒪] v' ∉ d.line M' ⊔ (𝔭.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M'))}
  have hset : {𝔭 : PrimeSpectrum B | d.EdgeNondegAt π 𝔭.asIdeal M' M} = S₃ ∩ S₄ := by
    ext 𝔭
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, S₃, S₄, DeligneDatum.EdgeNondegAt]
    exact ⟨fun h => ⟨h.2.2.1, h.2.2.2⟩, fun h => ⟨h1, h2, h.1, h.2⟩⟩
  rw [hset]
  have hπ𝔭 : ∀ 𝔭 : PrimeSpectrum B, algebraMap 𝒪 B π ∈ 𝔭.asIdeal := algebraMap_mem_of_isNilpotent hB

  have hcoe : ∀ (L : FullLattice 𝒪 K) (w : ↥L.1), ((π • w : ↥L.1) : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K) := by
    intro L w
    rw [Submodule.coe_smul, algebraMap_smul]
  refine IsOpen.inter ?_ ?_
  ·
    obtain ⟨T, hT, hrep⟩ := exists_finite_reps (π := π) M
    have hS : S₃ = ⋂ t ∈ {t ∈ T | (t : Fin 2 → K) ∉ M'.1},
        {𝔭 : PrimeSpectrum B | (1 : B) ⊗ₜ[𝒪] t ∉ d.line M ⊔ (𝔭.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))} := by
      ext 𝔭
      simp only [S₃, Set.mem_setOf_eq, Set.mem_iInter, and_imp]
      constructor
      · intro h t _ ht
        exact h t ht
      · intro h v hv
        obtain ⟨t, htT, w, rfl⟩ := hrep v
        have ht : (t : Fin 2 → K) ∉ M'.1 := by
          intro ht
          apply hv
          rw [Submodule.coe_add, hcoe]
          exact M'.1.add_mem ht (h2 w)
        exact (tmul_add_smul_not_mem_iff M (d.line M) 𝔭.asIdeal (hπ𝔭 𝔭) t w).2 (h t htT ht)
    rw [hS]
    exact Set.Finite.isOpen_biInter (hT.subset (Set.sep_subset _ _))
      (fun t _ => isOpen_setOf_not_mem_sup M (d.line M) (d.invertible M) _)
  ·
    obtain ⟨T', hT', hrep'⟩ := exists_finite_reps (π := π) M'
    have hS : S₄ = ⋂ t ∈ {t ∈ T' | ¬ ∃ w : ↥M.1, (t : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K)},
        {𝔭 : PrimeSpectrum B | (1 : B) ⊗ₜ[𝒪] t ∉ d.line M' ⊔ (𝔭.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M'))} := by
      ext 𝔭
      simp only [S₄, Set.mem_setOf_eq, Set.mem_iInter, and_imp]
      constructor
      · intro h t _ ht
        exact h t ht
      · intro h v' hv'
        obtain ⟨t, htT, w', rfl⟩ := hrep' v'
        have ht : ¬ ∃ w : ↥M.1, (t : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K) := by
          rintro ⟨w, hw⟩
          apply hv'
          refine ⟨w + ⟨(w' : Fin 2 → K), h1 w'.2⟩, ?_⟩
          rw [Submodule.coe_add, hcoe, hw, Submodule.coe_add, smul_add]
        exact (tmul_add_smul_not_mem_iff M' (d.line M') 𝔭.asIdeal (hπ𝔭 𝔭) t w').2 (h t htT ht)
    rw [hS]
    exact Set.Finite.isOpen_biInter (hT'.subset (Set.sep_subset _ _))
      (fun t _ => isOpen_setOf_not_mem_sup M' (d.line M') (d.invertible M') _)

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_isOpen_setOf_edgeNondegAt
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_isOpen_setOf_edgeNondegAt (solution)
