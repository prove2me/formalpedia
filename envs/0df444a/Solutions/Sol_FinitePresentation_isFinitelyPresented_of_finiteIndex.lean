-- Prove2me | solution 1 for FinitePresentation.isFinitelyPresented_of_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-23T20:24:49.247348+00:00
-- url     : https://prove2.me/submissions/c6b9083d-3346-4160-a23d-70641f6600a6

import Mathlib
import Theorems.Thm_GroupFiniteness_ker_isFinitelyNormallyGenerated_of_surjective

/-!
# A group with a finitely presented subgroup of finite index is finitely presented

Map a free group `F` of finite rank onto `G`, and let `F_H` be the preimage of `H`. It has finite
index in `F`, so it is finitely generated (Schreier). Composing a surjection from a free group of
finite rank onto `F_H` with `F_H → H`, the published change-of-generators theorem makes the kernel
finitely normally generated; pushed forward, the kernel of `F_H → H`, which is the kernel of
`F → G`, is the normal closure in `F_H` of a finite set, hence also its normal closure in `F`.
-/

namespace FinitePresentation.Lib

open Subgroup

/-- A group with a finitely generated subgroup of finite index is finitely generated: the
subgroup's generators together with one representative of each coset generate. -/
theorem fg_of_fg_finiteIndex {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]
    [hH : Group.FG H] : Group.FG G := by
  obtain ⟨S, hSH, hSfin⟩ := H.fg_iff.mp ((Group.fg_iff_subgroup_fg H).mp hH)
  refine Group.fg_iff.mpr ⟨S ∪ Set.range (fun q : G ⧸ H => q.out), ?_,
    hSfin.union (Set.finite_range _)⟩
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  have hg : g = (QuotientGroup.mk g : G ⧸ H).out * (h : G)⁻¹ := by rw [hh]; group
  rw [hg]
  refine mul_mem (subset_closure (Or.inr ⟨_, rfl⟩)) (inv_mem ?_)
  exact closure_mono Set.subset_union_left (hSH ▸ h.2)

/-- A finitely generated group is the image of a free group on `Fin n`. -/
theorem exists_fin_surjective {K : Type*} [Group K] (hK : Group.FG K) :
    ∃ (n : ℕ) (φ : FreeGroup (Fin n) →* K), Function.Surjective φ := by
  obtain ⟨α, _, φ, hφ⟩ := Group.fg_iff_exists_freeGroup_hom_surjective_finite.mp hK
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  exact ⟨n, φ.comp (FreeGroup.freeGroupCongr e).symm.toMonoidHom,
    hφ.comp (FreeGroup.freeGroupCongr e).symm.surjective⟩

/-- The image of a normal closure lies in the normal closure of the image. -/
theorem map_normalClosure_le {A B : Type*} [Group A] [Group B] (f : A →* B) (S : Set A) :
    (normalClosure S).map f ≤ normalClosure (f '' S) :=
  map_le_iff_le_comap.mpr (normalClosure_le_normal fun s hs => subset_normalClosure ⟨s, hs, rfl⟩)

theorem isFinitelyPresented_of_finiteIndex' {G : Type*} [Group G] (H : Subgroup G)
    [H.FiniteIndex] [hHfp : Group.IsFinitelyPresented H] : Group.IsFinitelyPresented G := by
  have hHfg : Group.FG H := by
    obtain ⟨n, φ, hφ, -⟩ := hHfp.out
    exact Group.fg_of_surjective hφ
  obtain ⟨n, π, hπ⟩ := exists_fin_surjective (fg_of_fg_finiteIndex H)
  -- the preimage of `H` in the free group: finite index, hence finitely generated
  set FH : Subgroup (FreeGroup (Fin n)) := H.comap π with hFH
  have : FH.FiniteIndex := ⟨by rw [hFH, index_comap_of_surjective H hπ]; exact FiniteIndex.index_ne_zero⟩
  obtain ⟨m, ψ, hψ⟩ := exists_fin_surjective (inferInstance : Group.FG FH)
  -- `π` restricted to `FH`, onto `H`
  let ρ : FH →* H := (π.comp FH.subtype).codRestrict H (fun x => x.2)
  have hρ : Function.Surjective ρ := by
    intro h
    obtain ⟨x, hx⟩ := hπ h
    exact ⟨⟨x, show π x ∈ H by rw [hx]; exact h.2⟩, Subtype.ext hx⟩
  -- its kernel is finitely normally generated in `FH`
  have hK : ρ.ker.IsFinitelyNormallyGenerated := by
    have h1 := (GroupFiniteness.ker_isFinitelyNormallyGenerated_of_surjective (ρ.comp ψ)
      (hρ.comp hψ)).map hψ
    rwa [← MonoidHom.comap_ker, map_comap_eq_self_of_surjective hψ] at h1
  obtain ⟨S, hSfin, hS⟩ := hK
  refine ⟨n, π, hπ, FH.subtype '' S, hSfin.image _, le_antisymm ?_ ?_⟩
  · refine normalClosure_le_normal ?_
    rintro _ ⟨s, hs, rfl⟩
    have : s ∈ ρ.ker := hS ▸ subset_normalClosure hs
    rw [MonoidHom.mem_ker] at this
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    exact congrArg Subtype.val this
  · intro x hx
    have hxFH : x ∈ FH := by
      rw [MonoidHom.mem_ker] at hx
      show π x ∈ H
      rw [hx]; exact H.one_mem
    have hker : (⟨x, hxFH⟩ : FH) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]; exact Subtype.ext hx
    rw [← hS] at hker
    exact map_normalClosure_le FH.subtype S ⟨_, hker, rfl⟩

end FinitePresentation.Lib

theorem solution {G : Type*} [Group G] (H : Subgroup G)
    [H.FiniteIndex] [Group.IsFinitelyPresented H] : Group.IsFinitelyPresented G :=
  FinitePresentation.Lib.isFinitelyPresented_of_finiteIndex' H
