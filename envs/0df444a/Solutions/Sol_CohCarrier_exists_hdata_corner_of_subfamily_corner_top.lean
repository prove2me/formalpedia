-- Prove2me | solution 1 for CohCarrier.exists_hdata_corner_of_subfamily_corner_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/7b56d728-8e3e-52e1-8686-6e5988963c4e

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Theorems.Thm_IharaLemma_nonempty_idempotentSplitting_of_finite
import Theorems.Thm_IharaLemma_IdempotentSplitting_eq_smul_of_smul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_hdata_corner_of_subfamily_corner_top

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open IsLocalRing CohCarrier IharaLemma
open scoped IsMulCommutative

namespace E5Bridge

section basic
variable {B : Type} [CommRing B] (Sp : IdempotentSplitting B) (i : Fin Sp.n)

theorem one_sub_e_mem : 1 - Sp.e i ∈ Sp.𝔪 i := by
  have h0 : Sp.e i * (1 - Sp.e i) = 0 := by rw [mul_sub, mul_one, (Sp.idem i).eq, sub_self]
  have hmem : Sp.e i * (1 - Sp.e i) ∈ Sp.𝔪 i := by rw [h0]; exact (Sp.𝔪 i).zero_mem
  rcases (Sp.isMaximal i).isPrime.mem_or_mem hmem with h | h
  · exact absurd h (Sp.notMem i)
  · exact h

theorem toCornerRing_surjective : Function.Surjective (Sp.toCornerRing i) := by
  intro z
  obtain ⟨_, a, rfl⟩ := z
  exact ⟨a, rfl⟩

theorem toCornerRing_eq_zero_iff (x : B) : Sp.toCornerRing i x = 0 ↔ Sp.e i * x = 0 := by
  constructor
  · intro h
    have h' : Sp.e i * x * Sp.e i = 0 := congrArg Subtype.val h
    rwa [mul_right_comm, (Sp.idem i).eq] at h'
  · intro h
    apply Subtype.ext
    show Sp.e i * x * Sp.e i = 0
    rw [h, zero_mul]

theorem toCornerRing_mem_maximalIdeal {x : B} (hx : x ∈ Sp.𝔪 i) :
    Sp.toCornerRing i x ∈ maximalIdeal (Sp.CornerRing i) := by
  have := (IsLocalization.AtPrime.to_map_mem_maximal_iff (Sp.CornerRing i) (Sp.𝔪 i) x).mpr hx
  exact this

theorem isUnit_toCornerRing_of_notMem {x : B} (hx : x ∉ Sp.𝔪 i) : IsUnit (Sp.toCornerRing i x) :=
  IsLocalization.map_units (Sp.CornerRing i) (⟨x, hx⟩ : (Sp.𝔪 i).primeCompl)

end basic

section CT
variable {𝒪 : Type} [CommRing 𝒪] {A B : Type} [CommRing A] [CommRing B] [Algebra 𝒪 A] [Algebra 𝒪 B]
variable (ψ : A →ₐ[𝒪] B) (hψ : Function.Surjective ψ)
variable (Sp : IdempotentSplitting A) (i : Fin Sp.n) (Sp' : IdempotentSplitting B) (i₀ : Fin Sp'.n)
variable (hker0 : ∀ x : A, ψ x = 0 → Sp.e i * x = 0) (hmap : Sp'.𝔪 i₀ = Ideal.map ψ (Sp.𝔪 i))

include hker0 in
theorem ker_le : ∀ x : A, ψ x = 0 → x ∈ Sp.𝔪 i := by
  intro x hx
  have : x = (1 - Sp.e i) * x := by rw [sub_mul, one_mul, hker0 x hx, sub_zero]
  rw [this]
  exact (Sp.𝔪 i).mul_mem_right x (one_sub_e_mem Sp i)

include hψ hker0 in

theorem mem_of_map_mem {x : A} (hx : ψ x ∈ Ideal.map ψ (Sp.𝔪 i)) : x ∈ Sp.𝔪 i := by
  rw [Ideal.mem_map_iff_of_surjective ψ hψ] at hx
  obtain ⟨m, hm, hmx⟩ := hx
  have : x - m ∈ Sp.𝔪 i := ker_le ψ Sp i hker0 (x - m) (by rw [map_sub, hmx, sub_self])
  simpa using (Sp.𝔪 i).add_mem this hm

include hψ hker0 hmap in
theorem map_e_notMem : ψ (Sp.e i) ∉ Sp'.𝔪 i₀ := by
  rw [hmap]
  exact fun h => Sp.notMem i (mem_of_map_mem ψ hψ Sp i hker0 h)

include hψ hker0 hmap in
theorem map_e_mem_of_ne (j : Fin Sp'.n) (hj : j ≠ i₀) : ψ (Sp.e i) ∈ Sp'.𝔪 j := by

  have hmax : (Ideal.comap ψ (Sp'.𝔪 j)).IsMaximal := Ideal.comap_isMaximal_of_surjective ψ hψ
  obtain ⟨l, hl⟩ := Sp.exists_eq _ hmax
  by_cases hli : l = i
  · subst hli
    exfalso
    apply hj
    apply Sp'.𝔪_injective
    have h1 : Ideal.map ψ (Sp.𝔪 l) ≤ Sp'.𝔪 j := by rw [hl]; exact Ideal.map_comap_le
    rw [← hmap] at h1
    exact ((Sp'.isMaximal i₀).eq_of_le (Sp'.isMaximal j).ne_top h1).symm
  · have : Sp.e i ∈ Sp.𝔪 l := Sp.mem_of_ne (fun h => hli h.symm)
    rw [hl] at this
    exact this

include hψ hker0 hmap in
theorem map_e_eq : ψ (Sp.e i) = Sp'.e i₀ := by

  have ha : ψ (Sp.e i) = Sp'.e i₀ * ψ (Sp.e i) := by
    have hu : (1 - ψ (Sp.e i)) • ψ (Sp.e i) = 0 := by
      rw [smul_eq_mul, sub_mul, one_mul, ← map_mul, (Sp.idem i).eq, sub_self]
    have := Sp'.eq_smul_of_smul_eq_zero hu i₀ (fun j hj hmem => (Sp'.isMaximal j).ne_top
      ((Ideal.eq_top_iff_one _).mpr (by
        have := (Sp'.𝔪 j).add_mem hmem (map_e_mem_of_ne ψ hψ Sp i Sp' i₀ hker0 hmap j hj)
        rwa [sub_add_cancel] at this)))
    rwa [smul_eq_mul] at this

  have hb : Sp'.e i₀ * ψ (1 - Sp.e i) = 0 := by
    have hmem : ψ (1 - Sp.e i) ∈ Sp'.𝔪 i₀ := by
      rw [hmap]; exact Ideal.mem_map_of_mem _ (one_sub_e_mem Sp i)
    set z := Sp'.toCornerRing i₀ (ψ (1 - Sp.e i)) with hz
    have hzmax : z ∈ maximalIdeal (Sp'.CornerRing i₀) := toCornerRing_mem_maximalIdeal Sp' i₀ hmem
    have hzid : z * z = z := by
      have hid : (1 - Sp.e i) * (1 - Sp.e i) = 1 - Sp.e i := by
        have := (Sp.idem i).eq
        rw [sub_mul, one_mul, mul_sub, mul_one, this, sub_self, sub_zero]
      rw [hz, ← map_mul, ← map_mul, hid]
    have hz0 : z = 0 := by
      have hu : IsUnit (1 - z) := by
        rw [IsLocalRing.mem_maximalIdeal] at hzmax
        exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits z hzmax
      have : (1 - z) * z = 0 := by rw [sub_mul, one_mul, hzid, sub_self]
      exact (hu.mul_right_eq_zero).mp this
    exact (toCornerRing_eq_zero_iff Sp' i₀ _).mp hz0
  rw [map_sub, map_one, mul_sub, mul_one, sub_eq_zero] at hb
  rw [ha, ← hb]

include hψ hker0 hmap in

theorem exists_cornerEquiv :
    ∃ eB : Sp.CornerRing i ≃ₐ[𝒪] Sp'.CornerRing i₀,
      ∀ x : A, eB (Sp.toCornerRing i x) = Sp'.toCornerRing i₀ (ψ x) := by
  let h : A →+* Sp'.CornerRing i₀ := (Sp'.toCornerRing i₀).comp ψ.toRingHom
  have hunits : ∀ s : (Sp.𝔪 i).primeCompl, IsUnit (h s) := by
    intro s
    apply isUnit_toCornerRing_of_notMem Sp' i₀
    rw [hmap]
    exact fun hs => s.2 (mem_of_map_mem ψ hψ Sp i hker0 hs)
  let f : Sp.CornerRing i →+* Sp'.CornerRing i₀ := IsLocalization.lift (M := (Sp.𝔪 i).primeCompl) hunits
  have hf : ∀ x : A, f (Sp.toCornerRing i x) = Sp'.toCornerRing i₀ (ψ x) := fun x =>
    IsLocalization.lift_eq (M := (Sp.𝔪 i).primeCompl) hunits x
  have hcomm : ∀ r : 𝒪, f (algebraMap 𝒪 (Sp.CornerRing i) r) = algebraMap 𝒪 (Sp'.CornerRing i₀) r := by
    intro r
    rw [IsScalarTower.algebraMap_apply 𝒪 A (Sp.CornerRing i),
      IsScalarTower.algebraMap_apply 𝒪 B (Sp'.CornerRing i₀)]
    show f (Sp.toCornerRing i _) = Sp'.toCornerRing i₀ _
    rw [hf, AlgHom.commutes]
  let fa : Sp.CornerRing i →ₐ[𝒪] Sp'.CornerRing i₀ := ⟨f, hcomm⟩
  have hfa : ∀ z, fa z = f z := fun _ => rfl
  have hsurj : Function.Surjective fa := by
    intro z
    obtain ⟨b, rfl⟩ := toCornerRing_surjective Sp' i₀ z
    obtain ⟨a, rfl⟩ := hψ b
    exact ⟨Sp.toCornerRing i a, by rw [hfa, hf]⟩
  have hinj : Function.Injective fa := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨a, rfl⟩ := toCornerRing_surjective Sp i z
    rw [hfa, hf, toCornerRing_eq_zero_iff, ← map_e_eq ψ hψ Sp i Sp' i₀ hker0 hmap, ← map_mul] at hz
    have := hker0 _ hz
    rw [← mul_assoc, (Sp.idem i).eq] at this
    exact (toCornerRing_eq_zero_iff Sp i a).mpr this
  exact ⟨AlgEquiv.ofBijective fa ⟨hinj, hsurj⟩, fun x => by
    rw [AlgEquiv.ofBijective_apply, hfa, hf]⟩

end CT

section RES
variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
variable (Sp : IdempotentSplitting B) (i : Fin Sp.n)

theorem exists_residuePoint (hsc : ∀ b : B, ∃ c : 𝒪, b - algebraMap 𝒪 B c ∈ Sp.𝔪 i) :
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

theorem forall_exists_sub_algebraMap_mem (G : Set B)
    (hGc : ∀ g ∈ G, ∃ c : 𝒪, g - algebraMap 𝒪 B c ∈ Sp.𝔪 i) :
    ∀ b ∈ Algebra.adjoin 𝒪 G, ∃ c : 𝒪, b - algebraMap 𝒪 B c ∈ Sp.𝔪 i := by
  intro b hb
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact hGc x hx
  | algebraMap r => exact ⟨r, by rw [sub_self]; exact (Sp.𝔪 i).zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx; obtain ⟨d, hd⟩ := hy
    exact ⟨c + d, by rw [map_add]; convert (Sp.𝔪 i).add_mem hc hd using 1; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx; obtain ⟨d, hd⟩ := hy
    refine ⟨c * d, ?_⟩
    have : x * y - algebraMap 𝒪 B (c * d) =
        (x - algebraMap 𝒪 B c) * y + algebraMap 𝒪 B c * (y - algebraMap 𝒪 B d) := by
      rw [map_mul]; ring
    rw [this]
    exact (Sp.𝔪 i).add_mem ((Sp.𝔪 i).mul_mem_right _ hc) ((Sp.𝔪 i).mul_mem_left _ hd)

end RES

section CORE
variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
variable {A B V : Type} [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] [CommRing B] [Algebra 𝒪 B]
variable [AddCommGroup V] [Module 𝒪 V] [Module A V] [IsScalarTower 𝒪 A V] [Module B V] [IsScalarTower 𝒪 B V]

theorem mem_cornerSubmodule_iff {e : A} (he : IsIdempotentElem e) (v : V) :
    v ∈ cornerSubmodule (M := V) e ↔ e • v = v := by
  constructor
  · rintro ⟨w, rfl⟩
    show e • (e • w) = e • w
    rw [smul_smul, he.eq]
  · intro h
    exact ⟨v, h⟩

theorem bridge_core
    (ψ : A →ₐ[𝒪] B) (hψ : Function.Surjective ψ) (hψact : ∀ (a : A) (v : V), ψ a • v = a • v)
    (hBfaith : ∀ b : B, (∀ v : V, b • v = 0) → b = 0)
    (Sp : IdempotentSplitting A) (i : Fin Sp.n)
    (hfaith : ∀ x : Sp.CornerRing i, (∀ m : ↥(cornerSubmodule (M := V) (Sp.e i)), x • m = 0) → x = 0)
    {ι : Type} (gen : ι → A) (c : ι → 𝒪) (hc : ∀ j, gen j - algebraMap 𝒪 A (c j) ∈ Sp.𝔪 i)
    (hBgen : ∀ b : B, ∃ a ∈ Algebra.adjoin 𝒪 (Set.range gen), ψ a = b) :
    ∃ (Sp' : IdempotentSplitting B) (i₀ : Fin Sp'.n) (π : Sp'.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪)
      (eB : Sp.CornerRing i ≃ₐ[𝒪] Sp'.CornerRing i₀),
      (∀ j, π (Sp'.toCornerRing i₀ (ψ (gen j))) = residue 𝒪 (c j)) ∧
      ψ (Sp.e i) = Sp'.e i₀ ∧
      (∀ x : A, eB (Sp.toCornerRing i x) = Sp'.toCornerRing i₀ (ψ x)) ∧
      (∀ x : Sp.CornerRing i, ((eB x : Sp'.CornerRing i₀) : B) = ψ (x : A)) ∧
      (∀ v : V, v ∈ cornerSubmodule (M := V) (Sp.e i) ↔ v ∈ cornerSubmodule (M := V) (Sp'.e i₀)) ∧
      (∀ (x : Sp.CornerRing i) (m : ↥(cornerSubmodule (M := V) (Sp.e i)))
          (m' : ↥(cornerSubmodule (M := V) (Sp'.e i₀))),
        (m : V) = m' → ((x • m : ↥(cornerSubmodule (M := V) (Sp.e i))) : V) =
          ((eB x • m' : ↥(cornerSubmodule (M := V) (Sp'.e i₀))) : V)) := by
  classical

  haveI : Module.Finite 𝒪 B := Module.Finite.of_surjective ψ.toLinearMap hψ
  obtain ⟨Sp'⟩ := IharaLemma.nonempty_idempotentSplitting_of_finite 𝒪 B

  have hker0 : ∀ x : A, ψ x = 0 → Sp.e i * x = 0 := by
    intro x hx
    have hx0 : ∀ v : V, x • v = 0 := fun v => by rw [← hψact, hx, zero_smul]
    have : Sp.toCornerRing i x = 0 := by
      apply hfaith
      intro m
      apply Subtype.ext
      rw [IdempotentSplitting.coe_cornerSmul, IdempotentSplitting.coe_toCornerRing, mul_smul, mul_smul,
        hx0, smul_zero, ZeroMemClass.coe_zero]
    exact (toCornerRing_eq_zero_iff Sp i x).mp this

  have hmax : (Ideal.map ψ (Sp.𝔪 i)).IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective ψ hψ (Sp.isMaximal i) with h | h
    · exfalso
      apply (Sp.isMaximal i).ne_top
      rw [Ideal.eq_top_iff_one]
      have h1 : ψ 1 ∈ Ideal.map ψ (Sp.𝔪 i) := by rw [h]; exact Submodule.mem_top
      exact mem_of_map_mem ψ hψ Sp i hker0 h1
    · exact h
  obtain ⟨i₀, hi₀⟩ := Sp'.exists_eq _ hmax

  have hsc : ∀ b : B, ∃ c : 𝒪, b - algebraMap 𝒪 B c ∈ Sp'.𝔪 i₀ := by
    intro b
    obtain ⟨a, ha, rfl⟩ := hBgen b
    obtain ⟨c, hc⟩ := forall_exists_sub_algebraMap_mem Sp i (Set.range gen)
      (by rintro _ ⟨j, rfl⟩; exact ⟨c j, hc j⟩) a ha
    refine ⟨c, ?_⟩
    rw [hi₀, ← ψ.commutes, ← map_sub]
    exact Ideal.mem_map_of_mem _ hc
  obtain ⟨π, hπ⟩ := exists_residuePoint Sp' i₀ hsc
  obtain ⟨eB, heB⟩ := exists_cornerEquiv ψ hψ Sp i Sp' i₀ hker0 hi₀
  have hee : ψ (Sp.e i) = Sp'.e i₀ := map_e_eq ψ hψ Sp i Sp' i₀ hker0 hi₀
  have hcoe : ∀ x : Sp.CornerRing i, ((eB x : Sp'.CornerRing i₀) : B) = ψ (x : A) := by
    intro x
    obtain ⟨a, rfl⟩ := toCornerRing_surjective Sp i x
    rw [heB, IdempotentSplitting.coe_toCornerRing, IdempotentSplitting.coe_toCornerRing, map_mul, map_mul, hee]
  refine ⟨Sp', i₀, π, eB, fun j => ?_, hee, heB, hcoe, fun v => ?_, fun x m m' hmm' => ?_⟩
  ·
    apply hπ
    rw [hi₀, ← ψ.commutes, ← map_sub]
    exact Ideal.mem_map_of_mem _ (hc j)
  ·
    rw [mem_cornerSubmodule_iff (Sp.idem i), mem_cornerSubmodule_iff (Sp'.idem i₀), ← hee, hψact]
  ·
    rw [IdempotentSplitting.coe_cornerSmul, IdempotentSplitting.coe_cornerSmul, hcoe, hψact, hmm']

end CORE

section translate
variable {M : ℕ} {S : Finset ℕ} {S₀ : Set ℕ}
  (hSS₀ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → (ℓ ∈ S₀ ↔ ℓ ∈ (↑S : Set ℕ)))

def τ : CohCarrier.Gen M S₀ → CohCarrier.Gen M (↑S : Set ℕ)
  | .T ℓ hℓ hℓS₀ hℓM => .T ℓ hℓ (fun h => hℓS₀ ((hSS₀ ℓ hℓ hℓM).2 h)) hℓM
  | .U q hq hqM => .U q hq hqM
  | .dia d => .dia d

def τ' : CohCarrier.Gen M (↑S : Set ℕ) → CohCarrier.Gen M S₀
  | .T ℓ hℓ hℓS hℓM => .T ℓ hℓ (fun h => hℓS ((hSS₀ ℓ hℓ hℓM).1 h)) hℓM
  | .U q hq hqM => .U q hq hqM
  | .dia d => .dia d

variable [NeZero M] (H : Subgroup (ZMod M)ˣ) (𝒪 : Type) [CommRing 𝒪]

theorem opFamily_τ (g : CohCarrier.Gen M S₀) :
    CohCarrier.opFamily M H (↑S : Set ℕ) 𝒪 (τ hSS₀ g) = CohCarrier.opFamily M H S₀ 𝒪 g := by
  cases g <;> rfl

theorem opFamily_τ' (g : CohCarrier.Gen M (↑S : Set ℕ)) :
    CohCarrier.opFamily M H S₀ 𝒪 (τ' hSS₀ g) = CohCarrier.opFamily M H (↑S : Set ℕ) 𝒪 g := by
  cases g <;> rfl

include hSS₀ in
theorem range_opFamily_eq :
    Set.range (CohCarrier.opFamily M H S₀ 𝒪) = Set.range (CohCarrier.opFamily M H (↑S : Set ℕ) 𝒪) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩; exact ⟨τ hSS₀ g, opFamily_τ hSS₀ H 𝒪 g⟩
  · rintro ⟨g, rfl⟩; exact ⟨τ' hSS₀ g, opFamily_τ' hSS₀ H 𝒪 g⟩

end translate

section theta
variable {M : ℕ} {S : Finset ℕ} {S₀ : Set ℕ}
  (hSS₀ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → (ℓ ∈ S₀ ↔ ℓ ∈ (↑S : Set ℕ)))
  {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] (cfull : CohCarrier.Gen M (↑S : Set ℕ) → 𝒪)

noncomputable def θb : CohCarrier.Gen M S₀ → ResidueField 𝒪
  | .T ℓ hℓ hℓS₀ hℓM => residue 𝒪 (cfull (.T ℓ hℓ (fun h => hℓS₀ ((hSS₀ ℓ hℓ hℓM).2 h)) hℓM))
  | .U q hq hqM => residue 𝒪 (cfull (.U q hq hqM))
  | .dia _ => 1

theorem θb_eq (hcd : ∀ d : (ZMod M)ˣ, cfull (.dia d) - 1 ∈ maximalIdeal 𝒪) (g : CohCarrier.Gen M S₀) :
    θb hSS₀ cfull g = residue 𝒪 (cfull (τ hSS₀ g)) := by
  cases g with
  | T ℓ hℓ hℓS₀ hℓM => rfl
  | U q hq hqM => rfl
  | dia d =>
    show (1 : ResidueField 𝒪) = residue 𝒪 (cfull (.dia d))
    rw [eq_comm, ← (residue 𝒪).map_one, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hcd d

end theta

end E5Bridge

open IsLocalRing CohCarrier IharaLemma E5Bridge in
open scoped IsMulCommutative in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (M : ℕ) [NeZero M]

    (S : Finset ℕ) (S₀ : Set ℕ) (hS₀fin : S₀.Finite)
    (hS₀M : ∀ q : ℕ, q.Prime → q ∣ M → q ∉ S₀)
    (hSS₀ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → (ℓ ∈ S₀ ↔ ℓ ∈ (↑S : Set ℕ)))

    (hcomm : ∀ g h : CohCarrier.Gen M S₀,
      CohCarrier.opFamily M ⊤ S₀ 𝒪 g * CohCarrier.opFamily M ⊤ S₀ 𝒪 h =
        CohCarrier.opFamily M ⊤ S₀ 𝒪 h * CohCarrier.opFamily M ⊤ S₀ 𝒪 g)

    {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 M ⊤ 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 M ⊤ 𝒪)]
    [Module.Finite 𝒪 𝕋]
    (Sp : IdempotentSplitting 𝕋) (i : Fin Sp.n)
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp.e i))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp.e i))]
    (tfull : CohCarrier.Gen M (↑S : Set ℕ) → 𝕋) (cfull : CohCarrier.Gen M (↑S : Set ℕ) → 𝒪)
    (hgen : ∀ x : 𝕋, ∃ f ∈ Algebra.adjoin 𝒪 (Set.range (CohCarrier.opFamily M ⊤ (↑S : Set ℕ) 𝒪)),
      ∀ m : H1 M ⊤ 𝒪, x • m = f m)
    (htfull : ∀ g, ∀ m : H1 M ⊤ 𝒪, tfull g • m = CohCarrier.opFamily M ⊤ (↑S : Set ℕ) 𝒪 g m)
    (hcfull : ∀ g, tfull g - algebraMap 𝒪 𝕋 (cfull g) ∈ Sp.𝔪 i)
    (hcofull : ∀ v : H1 M ⊤ 𝒪, (∀ g, ∀ k : ℕ, ∃ n : ℕ, ((tfull g - algebraMap 𝒪 𝕋 (cfull g)) ^ n) • v ∈
        ((maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 M ⊤ 𝒪))) →
      v ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp.e i))
    (hcd : ∀ d : (ZMod M)ˣ, cfull (.dia d) - 1 ∈ maximalIdeal 𝒪)
    (hocc : cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp.e i) ≠ ⊥)
    (hfaith : ∀ x : Sp.CornerRing i,
      (∀ m : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp.e i)), x • m = 0) → x = 0) :
    ∃ (θbar : CohCarrier.Gen M S₀ → ResidueField 𝒪)

      (_ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS₀ : ℓ ∉ S₀) (hℓM : ¬ ℓ ∣ M),
        θbar (.T ℓ hℓ hℓS₀ hℓM) =
          residue 𝒪 (cfull (.T ℓ hℓ (fun h => hℓS₀ ((hSS₀ ℓ hℓ hℓM).2 h)) hℓM)))
      (_ : ∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M), θbar (.U q hq hqM) = residue 𝒪 (cfull (.U q hq hqM)))
      (_ : ∀ d : (ZMod M)ˣ, θbar (.dia d) = 1)
      (Sp' : IdempotentSplitting ↥(CohCarrier.hdata M ⊤ S₀ 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
      (i₀ : Fin Sp'.n) (πk : Sp'.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪)
      (_ : ∀ g : CohCarrier.Gen M S₀, πk (Sp'.toCornerRing i₀
        ⟨(CohCarrier.hdata M ⊤ S₀ 𝒪 (ResidueField 𝒪) hcomm θbar).op g,
          Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
      (eB : Sp.CornerRing i ≃ₐ[𝒪] Sp'.CornerRing i₀),

      (∀ v : H1 M ⊤ 𝒪, v ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp.e i) ↔
        v ∈ cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp'.e i₀)) ∧

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M),
        eB (Sp.toCornerRing i (tfull (.T ℓ hℓ hℓS hℓM))) =
          Sp'.toCornerRing i₀
            ⟨(CohCarrier.hdata M ⊤ S₀ 𝒪 (ResidueField 𝒪) hcomm θbar).op
                (.T ℓ hℓ (fun h => hℓS ((hSS₀ ℓ hℓ hℓM).1 h)) hℓM),
              Algebra.subset_adjoin (Set.mem_range_self _)⟩) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M),
        eB (Sp.toCornerRing i (tfull (.U q hq hqM))) =
          Sp'.toCornerRing i₀
            ⟨(CohCarrier.hdata M ⊤ S₀ 𝒪 (ResidueField 𝒪) hcomm θbar).op (.U q hq hqM),
              Algebra.subset_adjoin (Set.mem_range_self _)⟩) ∧

      (∀ (x : Sp.CornerRing i) (m : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp.e i)))
          (m' : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp'.e i₀))),
        (m : H1 M ⊤ 𝒪) = m' → ((x • m : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp.e i))) : H1 M ⊤ 𝒪) =
          ((eB x • m' : ↥(cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp'.e i₀))) : H1 M ⊤ 𝒪)) := by
  classical

  let θbar : CohCarrier.Gen M S₀ → ResidueField 𝒪 := θb hSS₀ cfull
  let D := CohCarrier.hdata M ⊤ S₀ 𝒪 (ResidueField 𝒪) hcomm θbar
  have hDop : D.opSubalgebra = Algebra.adjoin 𝒪 (Set.range (CohCarrier.opFamily M ⊤ S₀ 𝒪)) := rfl
  haveI : IsScalarTower 𝒪 ↥D.opSubalgebra (H1 M ⊤ 𝒪) := ⟨fun _ _ _ => rfl⟩

  let φ : 𝕋 →ₐ[𝒪] Module.End 𝒪 (H1 M ⊤ 𝒪) := Algebra.lsmul 𝒪 𝒪 (H1 M ⊤ 𝒪)
  have hφ : ∀ (x : 𝕋) (m : H1 M ⊤ 𝒪), φ x m = x • m := fun _ _ => rfl
  have hφtfull : ∀ g : CohCarrier.Gen M (↑S : Set ℕ), φ (tfull g) = CohCarrier.opFamily M ⊤ (↑S : Set ℕ) 𝒪 g :=
    fun g => LinearMap.ext (htfull g)
  have hrange : ∀ x : 𝕋, φ x ∈ D.opSubalgebra := by
    intro x
    obtain ⟨f, hf, hfx⟩ := hgen x
    have : φ x = f := LinearMap.ext hfx
    rw [this, hDop, range_opFamily_eq hSS₀ ⊤ 𝒪]
    exact hf
  let ψ : 𝕋 →ₐ[𝒪] ↥D.opSubalgebra := φ.codRestrict D.opSubalgebra hrange
  have hψval : ∀ x : 𝕋, ((ψ x : ↥D.opSubalgebra) : Module.End 𝒪 (H1 M ⊤ 𝒪)) = φ x := fun _ => rfl
  have hψgen : ∀ g : CohCarrier.Gen M S₀,
      ψ (tfull (τ hSS₀ g)) = ⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩ := by
    intro g
    apply Subtype.ext
    rw [hψval, hφtfull, opFamily_τ]
    rfl

  have hBgen : ∀ b : ↥D.opSubalgebra,
      ∃ a ∈ Algebra.adjoin 𝒪 (Set.range (fun g : CohCarrier.Gen M S₀ => tfull (τ hSS₀ g))), ψ a = b := by
    rintro ⟨f, hf⟩
    have key : ∀ (f : Module.End 𝒪 (H1 M ⊤ 𝒪))
        (hf : f ∈ Algebra.adjoin 𝒪 (Set.range (CohCarrier.opFamily M ⊤ S₀ 𝒪))),
        ∃ a ∈ Algebra.adjoin 𝒪 (Set.range (fun g : CohCarrier.Gen M S₀ => tfull (τ hSS₀ g))), φ a = f := by
      intro f hf
      induction hf using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        exact ⟨tfull (τ hSS₀ g), Algebra.subset_adjoin (Set.mem_range_self g), by rw [hφtfull, opFamily_τ]⟩
      | algebraMap r => exact ⟨algebraMap 𝒪 𝕋 r, Subalgebra.algebraMap_mem _ r, AlgHom.commutes φ r⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, hax⟩ := hx; obtain ⟨b, hb, hby⟩ := hy
        exact ⟨a + b, Subalgebra.add_mem _ ha hb, by rw [map_add, hax, hby]⟩
      | mul x y _ _ hx hy =>
        obtain ⟨a, ha, hax⟩ := hx; obtain ⟨b, hb, hby⟩ := hy
        exact ⟨a * b, Subalgebra.mul_mem _ ha hb, by rw [map_mul, hax, hby]⟩
    obtain ⟨a, ha, hfa⟩ := key f (hDop ▸ hf)
    exact ⟨a, ha, Subtype.ext hfa⟩
  have hψsurj : Function.Surjective ψ := fun b => by
    obtain ⟨a, _, ha⟩ := hBgen b
    exact ⟨a, ha⟩

  have hψact : ∀ (a : 𝕋) (v : H1 M ⊤ 𝒪), ψ a • v = a • v := fun _ _ => rfl
  have hBfaith : ∀ b : ↥D.opSubalgebra, (∀ v : H1 M ⊤ 𝒪, b • v = 0) → b = 0 :=
    fun b hb => Subtype.ext (LinearMap.ext hb)
  have hcgen : ∀ g : CohCarrier.Gen M S₀,
      tfull (τ hSS₀ g) - algebraMap 𝒪 𝕋 (cfull (τ hSS₀ g)) ∈ Sp.𝔪 i := fun g => hcfull _
  obtain ⟨Sp', i₀, πk, eB, hπk, hee, heB, hcoe, hmod, hact⟩ :=
    bridge_core (A := 𝕋) (B := ↥D.opSubalgebra) (V := H1 M ⊤ 𝒪) ψ hψsurj hψact hBfaith Sp i hfaith
      (fun g : CohCarrier.Gen M S₀ => tfull (τ hSS₀ g)) (fun g => cfull (τ hSS₀ g)) hcgen hBgen
  refine ⟨θbar, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, Sp', i₀, πk, ?_, eB, hmod, ?_, ?_, hact⟩
  ·
    intro g
    rw [← hψgen, hπk g]
    exact (θb_eq hSS₀ cfull hcd g).symm
  ·
    intro ℓ hℓ hℓS hℓM
    rw [heB]
    congr 1
    exact hψgen (.T ℓ hℓ (fun h => hℓS ((hSS₀ ℓ hℓ hℓM).1 h)) hℓM)
  ·
    intro q hq hqM
    rw [heB]
    congr 1
    exact hψgen (.U q hq hqM)

end S_CohCarrier_exists_hdata_corner_of_subfamily_corner_top
end P2MW
export P2MW.S_CohCarrier_exists_hdata_corner_of_subfamily_corner_top (solution)
