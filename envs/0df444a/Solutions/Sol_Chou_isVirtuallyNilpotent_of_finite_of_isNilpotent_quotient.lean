-- Prove2me | solution 1 for Chou.isVirtuallyNilpotent_of_finite_of_isNilpotent_quotient
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-19T12:16:38.957462+00:00
-- url     : https://prove2.me/submissions/12257738-1510-45ed-9698-984dfbec3b15

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Definitions.Def_Chou_Growth
import Mathlib

/-! # Chou §3, p. 399: finite-by-nilpotent groups are almost nilpotent -/

universe u

namespace Chou
namespace Lib

open Subgroup QuotientGroup

/-- The centralizer of an element of a finite normal subgroup has finite index: `G ⧸ C(s)` injects
into `N` via `g ↦ g s g⁻¹`. -/
lemma finiteIndex_centralizer_of_mem_finite_normal {G : Type*} [Group G] (N : Subgroup G)
    [N.Normal] [Finite N] (s : G) (hs : s ∈ N) : (centralizer ({s} : Set G)).FiniteIndex := by
  let f : G ⧸ centralizer ({s} : Set G) → N :=
    Quotient.lift (fun g => ⟨g * s * g⁻¹, ‹N.Normal›.conj_mem s hs g⟩) (by
      intro g h hgh
      have hgh' : g⁻¹ * h ∈ centralizer ({s} : Set G) := QuotientGroup.leftRel_apply.mp hgh
      rw [mem_centralizer_iff] at hgh'
      have := hgh' s (Set.mem_singleton s)
      apply Subtype.ext
      show g * s * g⁻¹ = h * s * h⁻¹
      calc g * s * g⁻¹ = g * (s * (g⁻¹ * h)) * h⁻¹ := by group
        _ = g * ((g⁻¹ * h) * s) * h⁻¹ := by rw [this]
        _ = h * s * h⁻¹ := by group)
  haveI : Finite (G ⧸ centralizer ({s} : Set G)) := by
    refine Finite.of_injective f ?_
    intro x y hxy
    induction x using Quotient.inductionOn with
    | h g =>
    induction y using Quotient.inductionOn with
    | h h =>
    apply Quotient.sound
    refine QuotientGroup.leftRel_apply.mpr ?_
    rw [mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    have hxy' : g * t * g⁻¹ = h * t * h⁻¹ := congrArg Subtype.val hxy
    calc t * (g⁻¹ * h) = g⁻¹ * (g * t * g⁻¹) * h := by group
      _ = g⁻¹ * (h * t * h⁻¹) * h := by rw [hxy']
      _ = (g⁻¹ * h) * t := by group
  exact Subgroup.finiteIndex_of_finite_quotient

/-- p. 399: a finite-by-nilpotent group is almost nilpotent. -/
theorem isVirtuallyNilpotent_of_finite_of_isNilpotent_quotient' {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] [Finite N] (h : Group.IsNilpotent (G ⧸ N)) :
    Group.IsVirtuallyNilpotent G := by
  classical
  -- `K`, the centralizer of `N`, as an intersection of finitely many centralizers
  let K : Subgroup G := ⨅ s : N, centralizer ({(s : G)} : Set G)
  haveI hK : K.FiniteIndex :=
    Subgroup.finiteIndex_iInf (fun s : N => finiteIndex_centralizer_of_mem_finite_normal N s s.2)
  have hKcomm : ∀ k ∈ K, ∀ n ∈ N, n * k = k * n := by
    intro k hk n hn
    have := Subgroup.mem_iInf.mp hk ⟨n, hn⟩
    rw [mem_centralizer_iff] at this
    exact this n (Set.mem_singleton _)
  refine ⟨K, ?_, hK⟩
  -- `K ⧸ (K ∩ N)` embeds in `G ⧸ N`; `K ∩ N` is central in `K`
  let f : K →* G ⧸ N := (mk' N).comp K.subtype
  haveI : Group.IsNilpotent (G ⧸ N) := h
  refine _root_.isNilpotent_of_ker_le_center f ?_
  intro k hk
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, coe_subtype] at hk
  have hk' : (k : G) ∈ N := (QuotientGroup.eq_one_iff (k : G)).mp hk
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (hKcomm g g.2 k hk').symm

end Lib
end Chou

open Chou

theorem solution {G : Type*} [Group G] (N : Subgroup G) [N.Normal] [Finite N]
    (h : Group.IsNilpotent (G ⧸ N)) : Group.IsVirtuallyNilpotent G :=
  Chou.Lib.isVirtuallyNilpotent_of_finite_of_isNilpotent_quotient' N h
