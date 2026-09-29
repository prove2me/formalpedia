-- Prove2me | solution 1 for CohCarrier.HeckeData.exists_corner_of_genMap_of_forall_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/75794204-bdbb-5c9f-9dd7-66730babb1a3

import Definitions.Def_CohCarrier_HeckeData
import Definitions.Def_IharaLemma_IdempotentSplitting
import Theorems.Thm_IharaLemma_nonempty_idempotentSplitting_of_finite
import Theorems.Thm_IharaLemma_IdempotentSplitting_eq_smul_of_smul_eq_zero
import Theorems.Thm_IharaLemma_IdempotentSplitting_mem_maxIdeal_iff_apply_toCornerRing_eq_zero
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_HeckeData_exists_corner_of_genMap_of_forall_isMaximal

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open IsLocalRing IharaLemma
open scoped IsMulCommutative

namespace NonSplit

section basic
variable {B : Type} [CommRing B] (Sp : IdempotentSplitting B) (i : Fin Sp.n)

private theorem toCornerRing_surjective : Function.Surjective (Sp.toCornerRing i) := by
  intro z
  obtain ⟨_, a, rfl⟩ := z
  exact ⟨a, rfl⟩

private theorem toCornerRing_eq_zero_iff (x : B) : Sp.toCornerRing i x = 0 ↔ Sp.e i * x = 0 := by
  constructor
  · intro h
    have h' : Sp.e i * x * Sp.e i = 0 := congrArg Subtype.val h
    rwa [mul_right_comm, (Sp.idem i).eq] at h'
  · intro h
    apply Subtype.ext
    show Sp.e i * x * Sp.e i = 0
    rw [h, zero_mul]

private theorem toCornerRing_mem_maximalIdeal {x : B} (hx : x ∈ Sp.𝔪 i) :
    Sp.toCornerRing i x ∈ maximalIdeal (Sp.CornerRing i) :=
  (IsLocalization.AtPrime.to_map_mem_maximal_iff (Sp.CornerRing i) (Sp.𝔪 i) x).mpr hx

private theorem eq_e_of_notMem_of_forall_mem {f : B} (hf : IsIdempotentElem f) (hfi : f ∉ Sp.𝔪 i)
    (hfj : ∀ j, j ≠ i → f ∈ Sp.𝔪 j) : f = Sp.e i := by

  have ha : f = Sp.e i * f := by
    have hu : (1 - f) • f = 0 := by rw [smul_eq_mul, sub_mul, one_mul, hf.eq, sub_self]
    have := Sp.eq_smul_of_smul_eq_zero hu i (fun j hj hmem => (Sp.isMaximal j).ne_top
      ((Ideal.eq_top_iff_one _).mpr (by
        have := (Sp.𝔪 j).add_mem hmem (hfj j hj)
        rwa [sub_add_cancel] at this)))
    rwa [smul_eq_mul] at this

  have h1f : 1 - f ∈ Sp.𝔪 i := by
    have h0 : f * (1 - f) = 0 := by rw [mul_sub, mul_one, hf.eq, sub_self]
    rcases (Sp.isMaximal i).isPrime.mem_or_mem (show f * (1 - f) ∈ Sp.𝔪 i by rw [h0]; exact zero_mem _)
      with h | h
    · exact absurd h hfi
    · exact h
  have hb : Sp.e i * (1 - f) = 0 := by
    set z := Sp.toCornerRing i (1 - f) with hz
    have hzmax : z ∈ maximalIdeal (Sp.CornerRing i) := toCornerRing_mem_maximalIdeal Sp i h1f
    have hzid : z * z = z := by
      have hid : (1 - f) * (1 - f) = 1 - f := by
        rw [sub_mul, one_mul, mul_sub, mul_one, hf.eq, sub_self, sub_zero]
      rw [hz, ← map_mul, hid]
    have hz0 : z = 0 := by
      have hu : IsUnit (1 - z) := by
        rw [IsLocalRing.mem_maximalIdeal] at hzmax
        exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits z hzmax
      have : (1 - z) * z = 0 := by rw [sub_mul, one_mul, hzid, sub_self]
      exact (hu.mul_right_eq_zero).mp this
    exact (toCornerRing_eq_zero_iff Sp i _).mp hz0
  rw [mul_sub, mul_one, sub_eq_zero] at hb
  rw [ha, ← hb]

end basic

section RES
variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
variable (Sp : IdempotentSplitting B) (i : Fin Sp.n)

private theorem exists_residuePoint (hsc : ∀ b : B, ∃ c : 𝒪, b - algebraMap 𝒪 B c ∈ Sp.𝔪 i) :
    ∃ π : Sp.CornerRing i →ₐ[𝒪] ResidueField 𝒪,
      ∀ (b : B) (c : 𝒪), b - algebraMap 𝒪 B c ∈ Sp.𝔪 i → π (Sp.toCornerRing i b) = residue 𝒪 c := by
  let C := Sp.CornerRing i
  let ρ : C →ₐ[𝒪] ResidueField C := { IsLocalRing.residue C with commutes' := fun _ => rfl }
  have hρ : ∀ z, ρ z = residue C z := fun _ => rfl
  have hkey : ∀ (b : B) (c : 𝒪), b - algebraMap 𝒪 B c ∈ Sp.𝔪 i →
      residue C (Sp.toCornerRing i b) = algebraMap 𝒪 (ResidueField C) c := by
    intro b c hbc
    have h1 : Sp.toCornerRing i (b - algebraMap 𝒪 B c) ∈ maximalIdeal C :=
      toCornerRing_mem_maximalIdeal Sp i hbc
    rw [map_sub] at h1
    have h2 : residue C (Sp.toCornerRing i b) = residue C (Sp.toCornerRing i (algebraMap 𝒪 B c)) := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact h1
    rw [h2]
    rfl
  let g₀ : 𝒪 →ₐ[𝒪] ResidueField C := Algebra.ofId 𝒪 (ResidueField C)
  have hg₀surj : Function.Surjective g₀ := by
    intro w
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective w
    obtain ⟨b, rfl⟩ := toCornerRing_surjective Sp i z
    obtain ⟨c, hc⟩ := hsc b
    exact ⟨c, (hkey b c hc).symm⟩
  have hker : ∀ a ∈ maximalIdeal 𝒪, g₀ a = 0 := by
    intro a ha
    have hmax : (RingHom.ker g₀.toRingHom).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective g₀.toRingHom hg₀surj
    have : RingHom.ker g₀.toRingHom = maximalIdeal 𝒪 := IsLocalRing.eq_maximalIdeal hmax
    have ha' : a ∈ RingHom.ker g₀.toRingHom := this ▸ ha
    exact ha'
  let g : ResidueField 𝒪 →ₐ[𝒪] ResidueField C :=
    Ideal.Quotient.liftₐ (maximalIdeal 𝒪) g₀ hker
  have hg : ∀ c : 𝒪, g (residue 𝒪 c) = g₀ c := fun _ => rfl
  have hgbij : Function.Bijective g := by
    refine ⟨g.toRingHom.injective, fun w => ?_⟩
    obtain ⟨c, rfl⟩ := hg₀surj w
    exact ⟨residue 𝒪 c, hg c⟩
  let ge := AlgEquiv.ofBijective g hgbij
  refine ⟨(ge.symm : ResidueField C →ₐ[𝒪] ResidueField 𝒪).comp ρ, fun b c hbc => ?_⟩
  rw [AlgHom.comp_apply, hρ, hkey b c hbc]
  apply ge.injective
  rw [AlgEquiv.coe_algHom, AlgEquiv.apply_symm_apply]
  show _ = g (residue 𝒪 c)
  rw [hg]
  rfl

omit [IsLocalRing 𝒪] in

private theorem forall_exists_sub_algebraMap_mem (I : Ideal B) (G : Set B)
    (hGc : ∀ g ∈ G, ∃ c : 𝒪, g - algebraMap 𝒪 B c ∈ I) :
    ∀ b ∈ Algebra.adjoin 𝒪 G, ∃ c : 𝒪, b - algebraMap 𝒪 B c ∈ I := by
  intro b hb
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact hGc x hx
  | algebraMap r => exact ⟨r, by rw [sub_self]; exact I.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx; obtain ⟨d, hd⟩ := hy
    exact ⟨c + d, by rw [map_add]; convert I.add_mem hc hd using 1; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx; obtain ⟨d, hd⟩ := hy
    refine ⟨c * d, ?_⟩
    have : x * y - algebraMap 𝒪 B (c * d) =
        (x - algebraMap 𝒪 B c) * y + algebraMap 𝒪 B c * (y - algebraMap 𝒪 B d) := by
      rw [map_mul]; ring
    rw [this]
    exact I.add_mem (I.mul_mem_right _ hc) (I.mul_mem_left _ hd)

end RES

end NonSplit

open scoped IsMulCommutative in

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]
    (D D' : CohCarrier.HeckeData 𝒪 V (ResidueField 𝒪))
    (φ : D.Gen → D'.Gen) (hop : ∀ g, D'.op (φ g) = D.op g)
    (Sp : IharaLemma.IdempotentSplitting ↥D.opSubalgebra) (i : Fin Sp.n)
    (πk : Sp.CornerRing i →ₐ[𝒪] ResidueField 𝒪)
    (hπk : ∀ g : D.Gen, πk (Sp.toCornerRing i ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) = D.θbar g)
    (hnew : ∀ 𝔪' : Ideal ↥D'.opSubalgebra, 𝔪'.IsMaximal →
      (∀ (g : D.Gen) (c : 𝒪), IsLocalRing.residue 𝒪 c = D.θbar g →
        ((⟨D'.op (φ g), Algebra.subset_adjoin (Set.mem_range_self (φ g))⟩ : ↥D'.opSubalgebra)
          - algebraMap 𝒪 ↥D'.opSubalgebra c) ∈ 𝔪') →
      ∀ g' : D'.Gen, ∃ c' : 𝒪, IsLocalRing.residue 𝒪 c' = D'.θbar g' ∧
        ((⟨D'.op g', Algebra.subset_adjoin (Set.mem_range_self g')⟩ : ↥D'.opSubalgebra)
          - algebraMap 𝒪 ↥D'.opSubalgebra c') ∈ 𝔪') :
    ∃ (Sp' : IharaLemma.IdempotentSplitting ↥D'.opSubalgebra) (i' : Fin Sp'.n)
      (πk' : Sp'.CornerRing i' →ₐ[𝒪] ResidueField 𝒪),
      (∀ g' : D'.Gen, πk' (Sp'.toCornerRing i'
        ⟨D'.op g', Algebra.subset_adjoin (Set.mem_range_self g')⟩) = D'.θbar g') ∧
      (∀ v : V, v ∈ IharaLemma.cornerSubmodule (M := V) (Sp.e i) ↔
        v ∈ IharaLemma.cornerSubmodule (M := V) (Sp'.e i')) := by
  classical

  have hBB' : D.opSubalgebra ≤ D'.opSubalgebra :=
    Algebra.adjoin_mono (by rintro _ ⟨g, rfl⟩; exact ⟨φ g, hop g⟩)
  let ι : ↥D.opSubalgebra →ₐ[𝒪] ↥D'.opSubalgebra := Subalgebra.inclusion hBB'
  letI : Algebra ↥D.opSubalgebra ↥D'.opSubalgebra := ι.toRingHom.toAlgebra
  have hιalg : ∀ x, algebraMap ↥D.opSubalgebra ↥D'.opSubalgebra x = ι x := fun _ => rfl
  haveI : IsScalarTower 𝒪 ↥D.opSubalgebra ↥D'.opSubalgebra :=
    IsScalarTower.of_algebraMap_eq (fun r => by rw [hιalg, AlgHom.commutes])

  haveI : IsNoetherian 𝒪 (Module.End 𝒪 V) := isNoetherian_of_isNoetherianRing_of_finite 𝒪 _
  haveI : Module.Finite 𝒪 ↥D'.opSubalgebra :=
    Module.Finite.of_injective D'.opSubalgebra.val.toLinearMap Subtype.val_injective
  obtain ⟨Sp'⟩ := IharaLemma.nonempty_idempotentSplitting_of_finite 𝒪 ↥D'.opSubalgebra
  haveI : Module.Finite ↥D.opSubalgebra ↥D'.opSubalgebra :=
    Module.Finite.of_restrictScalars_finite 𝒪 _ _
  haveI : Algebra.IsIntegral ↥D.opSubalgebra ↥D'.opSubalgebra := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsIntegral 𝒪 ↥D'.opSubalgebra := Algebra.IsIntegral.of_finite _ _

  have h𝒪 : ∀ (j : Fin Sp'.n) (c : 𝒪), c ∈ maximalIdeal 𝒪 → algebraMap 𝒪 ↥D'.opSubalgebra c ∈ Sp'.𝔪 j := by
    intro j c hc
    haveI := Sp'.isMaximal j
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := 𝒪) (Sp'.𝔪 j)
    have heq : Ideal.comap (algebraMap 𝒪 ↥D'.opSubalgebra) (Sp'.𝔪 j) = maximalIdeal 𝒪 :=
      IsLocalRing.eq_maximalIdeal hmax
    have : c ∈ Ideal.comap (algebraMap 𝒪 ↥D'.opSubalgebra) (Sp'.𝔪 j) := heq ▸ hc
    exact Ideal.mem_comap.mp this

  have hold : ∀ (g : D.Gen) (c : 𝒪), residue 𝒪 c = D.θbar g →
      ((⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩ : ↥D.opSubalgebra)
        - algebraMap 𝒪 ↥D.opSubalgebra c) ∈ Sp.𝔪 i := by
    intro g c hc
    have e1 : πk (Sp.toCornerRing i (algebraMap 𝒪 ↥D.opSubalgebra c)) = residue 𝒪 c := by
      rw [← IsLocalRing.ResidueField.algebraMap_eq]
      exact πk.commutes c
    rw [Sp.mem_maxIdeal_iff_apply_toCornerRing_eq_zero i πk, map_sub, map_sub, hπk g, e1, hc, sub_self]

  set e' : ↥D'.opSubalgebra := ι (Sp.e i) with he'
  have he'idem : IsIdempotentElem e' := (Sp.idem i).map ι
  have he'val : ((e' : ↥D'.opSubalgebra) : Module.End 𝒪 V) = ((Sp.e i : ↥D.opSubalgebra) : Module.End 𝒪 V) := rfl

  have hcomap : ∀ j : Fin Sp'.n, e' ∉ Sp'.𝔪 j →
      Ideal.comap (algebraMap ↥D.opSubalgebra ↥D'.opSubalgebra) (Sp'.𝔪 j) = Sp.𝔪 i := by
    intro j hj
    haveI := Sp'.isMaximal j
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := ↥D.opSubalgebra) (Sp'.𝔪 j)
    obtain ⟨l, hl⟩ := Sp.exists_eq _ hmax
    have hli : l = i := by
      by_contra hli
      have : Sp.e i ∈ Sp.𝔪 l := Sp.mem_of_ne (fun h => hli h.symm)
      rw [hl, Ideal.mem_comap] at this
      exact hj this
    rw [← hl, hli]

  obtain ⟨lift, hlift⟩ : ∃ lift : D'.Gen → 𝒪, ∀ g', residue 𝒪 (lift g') = D'.θbar g' :=
    ⟨fun g' => (IsLocalRing.residue_surjective (D'.θbar g')).choose,
      fun g' => (IsLocalRing.residue_surjective (D'.θbar g')).choose_spec⟩
  have hgenJ : ∀ j : Fin Sp'.n, e' ∉ Sp'.𝔪 j → ∀ g' : D'.Gen,
      ((⟨D'.op g', Algebra.subset_adjoin (Set.mem_range_self g')⟩ : ↥D'.opSubalgebra)
        - algebraMap 𝒪 ↥D'.opSubalgebra (lift g')) ∈ Sp'.𝔪 j := by
    intro j hj g'
    have holdj : ∀ (g : D.Gen) (c : 𝒪), residue 𝒪 c = D.θbar g →
        ((⟨D'.op (φ g), Algebra.subset_adjoin (Set.mem_range_self (φ g))⟩ : ↥D'.opSubalgebra)
          - algebraMap 𝒪 ↥D'.opSubalgebra c) ∈ Sp'.𝔪 j := by
      intro g c hc
      have h1 := hold g c hc
      rw [← hcomap j hj, Ideal.mem_comap, map_sub, hιalg, ← IsScalarTower.algebraMap_apply] at h1
      have h2 : ι ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩ =
          (⟨D'.op (φ g), Algebra.subset_adjoin (Set.mem_range_self (φ g))⟩ : ↥D'.opSubalgebra) :=
        Subtype.ext (hop g).symm
      rwa [h2] at h1
    obtain ⟨c', hc', hmem⟩ := hnew (Sp'.𝔪 j) (Sp'.isMaximal j) holdj g'

    have hdiff : algebraMap 𝒪 ↥D'.opSubalgebra (c' - lift g') ∈ Sp'.𝔪 j := by
      apply h𝒪 j
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hc', hlift, sub_self]
    have := (Sp'.𝔪 j).add_mem hmem hdiff
    rwa [map_sub, sub_add_sub_cancel] at this

  let K : Ideal ↥D'.opSubalgebra := ⨅ (j : Fin Sp'.n) (_ : e' ∉ Sp'.𝔪 j), Sp'.𝔪 j
  have hKle : ∀ j, e' ∉ Sp'.𝔪 j → K ≤ Sp'.𝔪 j := fun j hj => (iInf_le _ j).trans (iInf_le _ hj)
  have hmemK : ∀ x, (∀ j, e' ∉ Sp'.𝔪 j → x ∈ Sp'.𝔪 j) → x ∈ K := by
    intro x hx
    simp only [K, Submodule.mem_iInf]
    exact hx
  have htop : Algebra.adjoin 𝒪 (Set.range fun g' : D'.Gen =>
      ((⟨D'.op g', Algebra.subset_adjoin (Set.mem_range_self g')⟩ : ↥D'.opSubalgebra))) = ⊤ := by
    apply Subalgebra.map_injective (f := D'.opSubalgebra.val) Subtype.val_injective
    rw [← Algebra.adjoin_image, Algebra.map_top, Subalgebra.range_val, ← Set.range_comp]
    rfl
  have hscal : ∀ b : ↥D'.opSubalgebra, ∃ c : 𝒪, b - algebraMap 𝒪 ↥D'.opSubalgebra c ∈ K := by
    intro b
    refine NonSplit.forall_exists_sub_algebraMap_mem K _ ?_ b (by rw [htop]; exact Algebra.mem_top)
    rintro _ ⟨g', rfl⟩
    exact ⟨lift g', hmemK _ (fun j hj => hgenJ j hj g')⟩

  have huniq : ∀ j₁ j₂ : Fin Sp'.n, e' ∉ Sp'.𝔪 j₁ → e' ∉ Sp'.𝔪 j₂ → j₁ = j₂ := by
    intro j₁ j₂ h₁ h₂
    apply Sp'.𝔪_injective
    apply (Sp'.isMaximal j₁).eq_of_le (Sp'.isMaximal j₂).ne_top
    intro x hx
    obtain ⟨c, hc⟩ := hscal x
    have hc₁ : algebraMap 𝒪 ↥D'.opSubalgebra c ∈ Sp'.𝔪 j₁ := by
      have := (Sp'.𝔪 j₁).sub_mem hx (hKle j₁ h₁ hc)
      rwa [sub_sub_cancel] at this
    have hcm : c ∈ maximalIdeal 𝒪 := by
      by_contra hcu
      have hu : IsUnit (algebraMap 𝒪 ↥D'.opSubalgebra c) :=
        (IsLocalRing.notMem_maximalIdeal.mp hcu).map _
      exact (Sp'.isMaximal j₁).ne_top ((Sp'.𝔪 j₁).eq_top_of_isUnit_mem hc₁ hu)
    have := (Sp'.𝔪 j₂).add_mem (hKle j₂ h₂ hc) (h𝒪 j₂ c hcm)
    rwa [sub_add_cancel] at this
  have hex : ∃ j : Fin Sp'.n, e' ∉ Sp'.𝔪 j := by
    by_contra hall
    push Not at hall
    have hu : IsUnit (1 - e') := by
      by_contra hnu
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {1 - e'})
        (by rwa [Ne, Ideal.span_singleton_eq_top])
      obtain ⟨j, hj⟩ := Sp'.exists_eq M hM
      have h1 : 1 - e' ∈ Sp'.𝔪 j := hj ▸ hle (Ideal.mem_span_singleton_self _)
      have := (Sp'.𝔪 j).add_mem h1 (hall j)
      rw [sub_add_cancel] at this
      exact (Sp'.isMaximal j).ne_top ((Ideal.eq_top_iff_one _).mpr this)
    have h0 : (1 - e') * e' = 0 := by rw [sub_mul, one_mul, he'idem.eq, sub_self]
    have he0 : e' = 0 := (hu.mul_right_eq_zero).mp h0
    apply Sp.notMem i
    have : Sp.e i = 0 := (injective_iff_map_eq_zero ι).mp (Subalgebra.inclusion_injective hBB') _ he0
    rw [this]
    exact (Sp.𝔪 i).zero_mem
  obtain ⟨i', hi'⟩ := hex
  have hothers : ∀ j, j ≠ i' → e' ∈ Sp'.𝔪 j := fun j hj => by
    by_contra h
    exact hj (huniq j i' h hi')

  have hee : e' = Sp'.e i' := NonSplit.eq_e_of_notMem_of_forall_mem Sp' i' he'idem hi' hothers

  obtain ⟨π, hπ⟩ := NonSplit.exists_residuePoint Sp' i' (fun b => by
    obtain ⟨c, hc⟩ := hscal b
    exact ⟨c, hKle i' hi' hc⟩)
  refine ⟨Sp', i', π, fun g' => ?_, fun v => ?_⟩
  · rw [hπ _ (lift g') (hgenJ i' hi' g'), hlift]
  · constructor
    · rintro ⟨w, rfl⟩
      refine ⟨(Sp.e i : ↥D.opSubalgebra) • w, ?_⟩
      show ((Sp'.e i' : ↥D'.opSubalgebra) : Module.End 𝒪 V) (((Sp.e i : ↥D.opSubalgebra) : Module.End 𝒪 V) w) = _
      rw [← hee, he'val, ← Module.End.mul_apply, ← Subalgebra.coe_mul, (Sp.idem i).eq]
      rfl
    · rintro ⟨w, rfl⟩
      refine ⟨(Sp'.e i' : ↥D'.opSubalgebra) • w, ?_⟩
      show ((Sp.e i : ↥D.opSubalgebra) : Module.End 𝒪 V) (((Sp'.e i' : ↥D'.opSubalgebra) : Module.End 𝒪 V) w) = _
      rw [← he'val, hee, ← Module.End.mul_apply, ← Subalgebra.coe_mul, (Sp'.idem i').eq]
      rfl

end S_CohCarrier_HeckeData_exists_corner_of_genMap_of_forall_isMaximal
end P2MW
export P2MW.S_CohCarrier_HeckeData_exists_corner_of_genMap_of_forall_isMaximal (solution)
