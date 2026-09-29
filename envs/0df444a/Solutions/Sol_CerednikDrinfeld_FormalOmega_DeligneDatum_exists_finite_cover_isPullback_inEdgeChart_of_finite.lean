-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.exists_finite_cover_isPullback_inEdgeChart_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/429d7404-a44d-5d91-a54f-21e73ba79b3c

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isPullback_inEdgeChart_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finite_cover_isPullback_inEdgeChart_of_finite

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace ASM21
namespace COV

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem rTensor_mem_sup {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B') (M : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B M)) (𝔭' : Ideal B') (x : latticeBaseChange 𝒪 K B M)
    (hx : x ∈ N ⊔ (Ideal.comap f 𝔭' • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) :
    LinearMap.rTensor (↥M.1) f.toLinearMap x ∈
      lineBaseChange f M N ⊔ (𝔭' • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' M)) := by
  have aux : ∀ t ∈ (Ideal.comap f 𝔭' • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)),
      LinearMap.rTensor (↥M.1) f.toLinearMap t ∈ (𝔭' • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' M)) := by
    intro t ht
    induction ht using Submodule.smul_induction_on' with
    | smul a ha y _ =>
      rw [rTensor_smul_left]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    | add y _ z _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  obtain ⟨n, hn, t, ht, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  exact Submodule.add_mem_sup (Submodule.subset_span ⟨n, hn, rfl⟩) (aux t ht)

theorem edgeNondegAt_of_map {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B') (D : DeligneDatum (K := K) π B)
    (𝔭' : Ideal B') (M' M : FullLattice 𝒪 K) (h : (DeligneDatum.map π f D).EdgeNondegAt π 𝔭' M' M) :
    D.EdgeNondegAt π (Ideal.comap f 𝔭') M' M := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun v hv hmem => h3 v hv ?_, fun v' hv' hmem => h4 v' hv' ?_⟩
  · have := rTensor_mem_sup f M (D.line M) 𝔭' _ hmem
    rwa [rTensor_one_tmul] at this
  · have := rTensor_mem_sup f M' (D.line M') 𝔭' _ hmem
    rwa [rTensor_one_tmul] at this

theorem isOpen_setOf_not_mem_sup {V : Type} [AddCommGroup V] [Module B V] (N : Submodule B V)
    [Module.Projective B (V ⧸ N)] (x : V) :
    IsOpen {𝔮 : PrimeSpectrum B | x ∉ N ⊔ (𝔮.asIdeal • ⊤ : Submodule B V)} := by
  have key : ∀ 𝔮 : PrimeSpectrum B, x ∉ N ⊔ (𝔮.asIdeal • ⊤ : Submodule B V) ↔
      ∃ φ : (V ⧸ N) →ₗ[B] B, φ (N.mkQ x) ∉ 𝔮.asIdeal := by
    intro 𝔮
    constructor
    · intro hx
      apply exists_linearMap_apply_not_mem
      intro hq
      apply hx
      have : x ∈ ((𝔮.asIdeal • ⊤ : Submodule B V).map N.mkQ).comap N.mkQ := by
        rw [Submodule.mem_comap, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]; exact hq
      rwa [Submodule.comap_map_mkQ] at this
    · rintro ⟨φ, hφ⟩ hx
      apply hφ
      obtain ⟨n, hn, t, ht, rfl⟩ := Submodule.mem_sup.1 hx
      have hn0 : N.mkQ n = 0 := by simpa using hn
      rw [map_add, hn0, zero_add]
      have ht' : N.mkQ t ∈ (𝔮.asIdeal • ⊤ : Submodule B (V ⧸ N)) := by
        rw [← Submodule.range_mkQ, ← Submodule.map_top, ← Submodule.map_smul'']
        exact Submodule.mem_map_of_mem ht
      have := Submodule.mem_map_of_mem (f := φ) ht'
      rw [Submodule.map_smul''] at this
      have : φ (N.mkQ t) ∈ (𝔮.asIdeal • ⊤ : Submodule B B) := Submodule.smul_mono le_rfl le_top this
      simpa [Ideal.mul_top] using this
  have : {𝔮 : PrimeSpectrum B | x ∉ N ⊔ (𝔮.asIdeal • ⊤ : Submodule B V)} =
      ⋃ φ : (V ⧸ N) →ₗ[B] B, (PrimeSpectrum.basicOpen (φ (N.mkQ x)) : Set (PrimeSpectrum B)) := by
    ext 𝔮; simp only [Set.mem_setOf_eq, Set.mem_iUnion, key]; rfl
  rw [this]
  exact isOpen_iUnion fun φ => (PrimeSpectrum.basicOpen _).isOpen

end ASM21.COV

namespace ASM21
namespace COV

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem one_tmul_mem_of_mem_smul_top (L : FullLattice 𝒪 K) (𝔮 : Ideal B) (hπ𝔮 : algebraMap 𝒪 B π ∈ 𝔮)
    (t : ↥L.1) (ht : t ∈ (Ideal.span {π} • ⊤ : Submodule 𝒪 ↥L.1)) :
    (1 : B) ⊗ₜ[𝒪] t ∈ (𝔮 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L)) := by
  induction ht using Submodule.smul_induction_on' with
  | smul a ha y _ =>
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
      show (algebraMap 𝒪 B (c * π)) ⊗ₜ[𝒪] y = algebraMap 𝒪 B (c * π) • ((1 : B) ⊗ₜ[𝒪] y) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [map_mul]; exact 𝔮.mul_mem_left _ hπ𝔮
  | add y _ z _ hy hz => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hy hz

set_option maxHeartbeats 4000000 in

theorem isOpen_setOf_forall_not_mem [Finite (𝒪 ⧸ Ideal.span {π})] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (L : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B L))
    [Module.Projective B (latticeBaseChange 𝒪 K B L ⧸ N)] (T : Set ↥L.1) :
    IsOpen {𝔮 : PrimeSpectrum B | ∀ v ∈ T, (1 : B) ⊗ₜ[𝒪] v ∉ N ⊔ (𝔮.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L))} := by
  classical
  haveI : Module.Finite 𝒪 ↥L.1 := Module.Finite.iff_fg.2 L.2.1
  haveI hfq : Finite (↥L.1 ⧸ ((Ideal.span {π} : Ideal 𝒪) • ⊤ : Submodule 𝒪 ↥L.1)) :=
    Module.finite_of_finite (𝒪 ⧸ (Ideal.span {π} : Ideal 𝒪))
  have hπ𝔮 : ∀ 𝔮 : PrimeSpectrum B, algebraMap 𝒪 B π ∈ 𝔮.asIdeal := fun 𝔮 => by
    obtain ⟨n, hn⟩ := hB; exact 𝔮.isPrime.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)

  have hinv : ∀ (𝔮 : PrimeSpectrum B) (v v' : ↥L.1),
      ((Ideal.span {π} : Ideal 𝒪) • ⊤ : Submodule 𝒪 ↥L.1).mkQ v = ((Ideal.span {π} : Ideal 𝒪) • ⊤ : Submodule 𝒪 ↥L.1).mkQ v' →
      ((1 : B) ⊗ₜ[𝒪] v ∉ N ⊔ (𝔮.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L)) ↔
       (1 : B) ⊗ₜ[𝒪] v' ∉ N ⊔ (𝔮.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L))) := by
    intro 𝔮 v v' h
    have hvv' : v - v' ∈ ((Ideal.span {π} : Ideal 𝒪) • ⊤ : Submodule 𝒪 ↥L.1) := (Submodule.Quotient.eq _).1 h
    have hmem := one_tmul_mem_of_mem_smul_top π L 𝔮.asIdeal (hπ𝔮 𝔮) _ hvv'
    rw [TensorProduct.tmul_sub] at hmem
    constructor
    · intro hv hv'
      exact hv (by simpa using Submodule.add_mem _ (Submodule.mem_sup_right hmem) hv')
    · intro hv' hv
      exact hv' (by simpa using Submodule.sub_mem _ hv (Submodule.mem_sup_right hmem))

  have hrep : ∀ c ∈ ((Ideal.span {π} : Ideal 𝒪) • ⊤ : Submodule 𝒪 ↥L.1).mkQ '' T,
      ∃ v ∈ T, ((Ideal.span {π} : Ideal 𝒪) • ⊤ : Submodule 𝒪 ↥L.1).mkQ v = c := fun c hc => hc
  choose rep hrepT hrepmk using hrep
  have hfin : (((Ideal.span {π} : Ideal 𝒪) • ⊤ : Submodule 𝒪 ↥L.1).mkQ '' T).Finite := Set.toFinite _
  have heq : {𝔮 : PrimeSpectrum B | ∀ v ∈ T, (1 : B) ⊗ₜ[𝒪] v ∉ N ⊔ (𝔮.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L))} =
      ⋂ c ∈ ((Ideal.span {π} : Ideal 𝒪) • ⊤ : Submodule 𝒪 ↥L.1).mkQ '' T,
        {𝔮 : PrimeSpectrum B | ∀ hc : c ∈ ((Ideal.span {π} : Ideal 𝒪) • ⊤ : Submodule 𝒪 ↥L.1).mkQ '' T,
          (1 : B) ⊗ₜ[𝒪] (rep c hc) ∉ N ⊔ (𝔮.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L))} := by
    ext 𝔮
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h c hc hc'; exact h _ (hrepT c hc')
    · intro h v hv
      exact (hinv 𝔮 _ _ (hrepmk _ ⟨v, hv, rfl⟩)).1 (h _ ⟨v, hv, rfl⟩ ⟨v, hv, rfl⟩)
  rw [heq]
  refine hfin.isOpen_biInter fun c hc => ?_
  have : {𝔮 : PrimeSpectrum B | ∀ hc : c ∈ ((Ideal.span {π} : Ideal 𝒪) • ⊤ : Submodule 𝒪 ↥L.1).mkQ '' T,
          (1 : B) ⊗ₜ[𝒪] (rep c hc) ∉ N ⊔ (𝔮.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L))} =
      {𝔮 : PrimeSpectrum B | (1 : B) ⊗ₜ[𝒪] (rep c hc) ∉ N ⊔ (𝔮.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L))} := by
    ext 𝔮; simp only [Set.mem_setOf_eq]; exact ⟨fun h => h hc, fun h _ => h⟩
  rw [this]
  exact isOpen_setOf_not_mem_sup N _

theorem isOpen_setOf_edgeNondegAt [Finite (𝒪 ⧸ Ideal.span {π})] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (D : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K) :
    IsOpen {𝔮 : PrimeSpectrum B | D.EdgeNondegAt π 𝔮.asIdeal M' M} := by
  classical
  haveI := D.invertible M; haveI := D.invertible M'
  by_cases hc : M'.1 ≤ M.1 ∧ (∀ v : ↥M.1, (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ M'.1)
  · have heq : {𝔮 : PrimeSpectrum B | D.EdgeNondegAt π 𝔮.asIdeal M' M} =
        {𝔮 : PrimeSpectrum B | ∀ v ∈ {v : ↥M.1 | (v : Fin 2 → K) ∉ M'.1},
            (1 : B) ⊗ₜ[𝒪] v ∉ D.line M ⊔ (𝔮.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))} ∩
        {𝔮 : PrimeSpectrum B | ∀ v' ∈ {v' : ↥M'.1 | ¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K)},
            (1 : B) ⊗ₜ[𝒪] v' ∉ D.line M' ⊔ (𝔮.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M'))} := by
      ext 𝔮
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, DeligneDatum.EdgeNondegAt]
      exact ⟨fun h => ⟨h.2.2.1, h.2.2.2⟩, fun h => ⟨hc.1, hc.2, h.1, h.2⟩⟩
    rw [heq]
    exact (isOpen_setOf_forall_not_mem π hB M (D.line M) _).inter (isOpen_setOf_forall_not_mem π hB M' (D.line M') _)
  · have heq : {𝔮 : PrimeSpectrum B | D.EdgeNondegAt π 𝔮.asIdeal M' M} = ∅ := by
      ext 𝔮
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, DeligneDatum.EdgeNondegAt]
      exact fun h => hc ⟨h.1, h.2.1⟩
    rw [heq]; exact isOpen_empty

end ASM21.COV

open ASM21.COV in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) [Finite (𝒪 ⧸ Ideal.span {π})]
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : DeligneDatum (K := K) π B) :
    ∃ (k : ℕ) (f : Fin k → B) (_ : Ideal.span (Set.range f) = ⊤) (h : Fin k → Matrix.GeneralLinearGroup (Fin 2) K),
      ∀ (i : Fin k) (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] [IsLocalization.Away (f i) C],
        ∃ d' : DeligneDatum (K := K) π C,
          DeligneDatum.IsPullback (K := K) (π := π) C (h i) ((Omega K π).map (IsScalarTower.toAlgHom 𝒪 B C) d) d' ∧
          d'.InEdgeChart π (FullLattice.act g (stdFullLattice K)) (stdFullLattice K) := by
  classical

  have hloc : ∀ 𝔭 : PrimeSpectrum B, ∃ h : Matrix.GeneralLinearGroup (Fin 2) K,
      (DeligneDatum.pullback π B h d).EdgeNondegAt π 𝔭.asIdeal (FullLattice.act g (stdFullLattice K)) (stdFullLattice K) := by
    intro 𝔭
    let Bp := Localization.AtPrime 𝔭.asIdeal
    have hBp : IsNilpotent (algebraMap 𝒪 Bp π) := by
      rw [IsScalarTower.algebraMap_apply 𝒪 B Bp]; exact hB.map _
    obtain ⟨h, d', hpb, hch⟩ :=
      DeligneDatum.exists_isPullback_inEdgeChart_of_isLocalRing π hπ g hg Bp hBp
        ((Omega K π).map (IsScalarTower.toAlgHom 𝒪 B Bp) d)
    refine ⟨h, ?_⟩
    have hd' : d' = DeligneDatum.map π (IsScalarTower.toAlgHom 𝒪 B Bp) (DeligneDatum.pullback π B h d) := by
      rw [DeligneDatum.map_pullback]; exact DeligneDatum.ext' (funext hpb)
    have hmax := hch (IsLocalRing.maximalIdeal Bp) inferInstance
    rw [hd'] at hmax
    have := edgeNondegAt_of_map π (IsScalarTower.toAlgHom 𝒪 B Bp) _ _ _ _ hmax
    rwa [show Ideal.comap (IsScalarTower.toAlgHom 𝒪 B Bp) (IsLocalRing.maximalIdeal Bp) = 𝔭.asIdeal from
      Localization.AtPrime.comap_maximalIdeal (I := 𝔭.asIdeal)] at this
  choose hsel hhsel using hloc

  let U : PrimeSpectrum B → Set (PrimeSpectrum B) := fun 𝔭 =>
    {𝔮 | (DeligneDatum.pullback π B (hsel 𝔭) d).EdgeNondegAt π 𝔮.asIdeal (FullLattice.act g (stdFullLattice K)) (stdFullLattice K)}
  have hUopen : ∀ 𝔭, IsOpen (U 𝔭) := fun 𝔭 => isOpen_setOf_edgeNondegAt π hB _ _ _
  have hUmem : ∀ 𝔭, 𝔭 ∈ U 𝔭 := fun 𝔭 => hhsel 𝔭
  have hbasic : ∀ 𝔭 : PrimeSpectrum B, ∃ f : B, 𝔭 ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)) ∧
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)) ⊆ U 𝔭 := by
    intro 𝔭
    obtain ⟨_, ⟨f, rfl⟩, hmem, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (hUmem 𝔭) (hUopen 𝔭)
    exact ⟨f, hmem, hsub⟩
  choose fsel hfmem hfsub using hbasic
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun 𝔭 : PrimeSpectrum B => (PrimeSpectrum.basicOpen (fsel 𝔭) : Set (PrimeSpectrum B)))
    (fun 𝔭 => (PrimeSpectrum.basicOpen _).isOpen) (fun 𝔭 _ => Set.mem_iUnion.2 ⟨𝔭, hfmem 𝔭⟩)

  let k := t.card
  let e : Fin k ≃ ↥t := t.equivFin.symm
  let f : Fin k → B := fun i => fsel (e i)
  let hh : Fin k → Matrix.GeneralLinearGroup (Fin 2) K := fun i => hsel (e i)
  have hcover : ∀ 𝔮 : PrimeSpectrum B, ∃ i : Fin k, 𝔮 ∈ (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum B)) := by
    intro 𝔮
    obtain ⟨𝔭, h𝔭⟩ := Set.mem_iUnion.1 (ht (Set.mem_univ 𝔮))
    obtain ⟨h𝔭t, h𝔮⟩ := Set.mem_iUnion.1 h𝔭
    exact ⟨e.symm ⟨𝔭, h𝔭t⟩, by simpa [f] using h𝔮⟩
  have hspan : Ideal.span (Set.range f) = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    rw [eq_top_iff]
    intro 𝔮 _
    obtain ⟨i, hi⟩ := hcover 𝔮
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  refine ⟨k, f, hspan, hh, ?_⟩

  intro i C _ _ _ _ _
  refine ⟨DeligneDatum.pullback π C (hh i) ((Omega K π).map (IsScalarTower.toAlgHom 𝒪 B C) d), fun M => rfl, ?_⟩
  intro Q hQ
  haveI := hQ

  have hfi : f i ∉ Ideal.comap (algebraMap B C) Q := by
    intro hmem
    rw [Ideal.mem_comap] at hmem
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem (IsLocalization.Away.algebraMap_isUnit (f i)))
  let 𝔮 : PrimeSpectrum B := ⟨Ideal.comap (algebraMap B C) Q, Ideal.IsPrime.comap _⟩
  have h𝔮U : 𝔮 ∈ U (e i) := hfsub (e i) (show 𝔮 ∈ (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum B)) from hfi)
  obtain ⟨c1, c2, c3, c4⟩ := h𝔮U
  have hmp : DeligneDatum.pullback π C (hh i) ((Omega K π).map (IsScalarTower.toAlgHom 𝒪 B C) d) =
      DeligneDatum.map π (IsScalarTower.toAlgHom 𝒪 B C) (DeligneDatum.pullback π B (hh i) d) := by
    rw [DeligneDatum.map_pullback]; rfl
  rw [hmp]
  refine ⟨c1, c2, fun v hv => ?_, fun v' hv' => ?_⟩
  · have := rTensor_not_mem_lineBaseChange_sup (IsScalarTower.toAlgHom 𝒪 B C) (stdFullLattice K)
      ((DeligneDatum.pullback π B (hh i) d).line (stdFullLattice K)) ((DeligneDatum.pullback π B (hh i) d).invertible _) Q
      ((1 : B) ⊗ₜ[𝒪] v) (c3 v hv)
    rwa [rTensor_one_tmul] at this
  · have := rTensor_not_mem_lineBaseChange_sup (IsScalarTower.toAlgHom 𝒪 B C) (FullLattice.act g (stdFullLattice K))
      ((DeligneDatum.pullback π B (hh i) d).line _) ((DeligneDatum.pullback π B (hh i) d).invertible _) Q
      ((1 : B) ⊗ₜ[𝒪] v') (c4 v' hv')
    rwa [rTensor_one_tmul] at this

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finite_cover_isPullback_inEdgeChart_of_finite
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finite_cover_isPullback_inEdgeChart_of_finite (solution)
