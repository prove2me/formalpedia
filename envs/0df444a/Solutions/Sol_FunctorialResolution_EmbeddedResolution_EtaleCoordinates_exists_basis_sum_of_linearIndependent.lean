-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.exists_basis_sum_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:22.245803+00:00
-- url     : https://prove2.me/submissions/0d440345-fd3c-47d1-bd39-386a89823ad9

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_JacobianCriterion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_FormallyEtaleCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped TensorProduct
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates
section
private theorem exists_minimal_spanning_finset {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {ι : Type*} [DecidableEq ι] (C : Set V) (bb : ι → V) :
    ∀ (n : ℕ) (J : Finset ι), J.card ≤ n →
      Submodule.span K (C ∪ bb '' (↑J : Set ι)) = ⊤ →
      ∃ J' : Finset ι, Submodule.span K (C ∪ bb '' (↑J' : Set ι)) = ⊤ ∧
        ∀ j ∈ J', Submodule.span K (C ∪ bb '' (↑(J'.erase j) : Set ι)) ≠ ⊤ := by
  intro n
  induction n with
  | zero =>
      intro J hcard hJ
      refine ⟨J, hJ, fun j hj => ?_⟩
      have hpos : 0 < J.card := Finset.card_pos.mpr ⟨j, hj⟩
      exact absurd hcard (by omega)
  | succ n ih =>
      intro J hcard hJ
      by_cases hs : ∃ j ∈ J, Submodule.span K (C ∪ bb '' (↑(J.erase j) : Set ι)) = ⊤
      · obtain ⟨j, hjJ, hPj⟩ := hs
        refine ih (J.erase j) ?_ hPj
        have hce : (J.erase j).card = J.card - 1 := Finset.card_erase_of_mem hjJ
        omega
      · push Not at hs
        exact ⟨J, hJ, hs⟩
private theorem span_union_image_erase_eq_top {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {ι : Type*} [DecidableEq ι] {C : Set V} {bb : ι → V} {J : Finset ι} {j0 : ι}
    (hJtop : Submodule.span K (C ∪ bb '' (↑J : Set ι)) = ⊤)
    (hb : bb j0 ∈ Submodule.span K (C ∪ bb '' (↑(J.erase j0) : Set ι))) :
    Submodule.span K (C ∪ bb '' (↑(J.erase j0) : Set ι)) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← hJtop, Submodule.span_le]
  rintro v (hv | ⟨j, hj, rfl⟩)
  · exact Submodule.subset_span (Set.mem_union_left _ hv)
  · by_cases hjj : j = j0
    · rw [hjj]
      exact hb
    · exact Submodule.subset_span (Set.mem_union_right _
        ⟨j, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hjj, Finset.mem_coe.mp hj⟩), rfl⟩)
end
section
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S] (S' : Type*) [CommRing S']
  [Algebra (MvPolynomial ι k) S] [Algebra (MvPolynomial ι k) S'] [Algebra S S']
  [IsScalarTower (MvPolynomial ι k) S S']
end
section
variable (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
  (S : Type*) [CommRing S] (S' : Type*) [CommRing S']
  [Algebra k S] [Algebra k S'] [Algebra (MvPolynomial ι k) S] [Algebra (MvPolynomial ι k) S']
  [Algebra S S'] [IsScalarTower k (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S']
  [IsScalarTower k S S'] [IsScalarTower (MvPolynomial ι k) S S']
  [Algebra.FormallyEtale (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S']
end
section
end
section
end
end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (h : ℕ)
    (c : Fin h → V) (hc : LinearIndependent K c) :
    ∃ (J : Finset ι) (B : Module.Basis (Fin h ⊕ {j : ι // j ∈ J}) K V),
      (∀ i : Fin h, B (Sum.inl i) = c i) ∧
        ∀ j : {j : ι // j ∈ J}, B (Sum.inr j) = b (j : ι) := by
  classical
  have hPuniv : Submodule.span K
      (Set.range c ∪ (⇑b) '' (↑(Finset.univ : Finset ι) : Set ι)) = ⊤ := by
    refine le_antisymm le_top ?_
    have hsub : Set.range (⇑b) ⊆ Set.range c ∪ (⇑b) '' (↑(Finset.univ : Finset ι) : Set ι) := by
      rintro _ ⟨i, rfl⟩
      exact Set.mem_union_right _ ⟨i, Finset.mem_coe.mpr (Finset.mem_univ i), rfl⟩
    calc (⊤ : Submodule K V) = Submodule.span K (Set.range (⇑b)) := b.span_eq.symm
      _ ≤ _ := Submodule.span_mono hsub
  obtain ⟨J, hJtop, hJmin⟩ :=
    exists_minimal_spanning_finset (K := K) (Set.range c) (⇑b)
      (Finset.univ : Finset ι).card Finset.univ le_rfl hPuniv
  have hrange : Set.range (Sum.elim c (fun j : {j : ι // j ∈ J} => b (j : ι)))
      = Set.range c ∪ (⇑b) '' (↑J : Set ι) := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      cases x with
      | inl i => exact Set.mem_union_left _ ⟨i, rfl⟩
      | inr j => exact Set.mem_union_right _ ⟨(j : ι), Finset.mem_coe.mpr j.2, rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr ⟨j, Finset.mem_coe.mp hj⟩, rfl⟩
  have hli : LinearIndependent K (Sum.elim c (fun j : {j : ι // j ∈ J} => b (j : ι))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : (∑ i : Fin h, g (Sum.inl i) • c i)
        + (∑ j : {j : ι // j ∈ J}, g (Sum.inr j) • b (j : ι)) = 0 := by
      rw [Fintype.sum_sum_type] at hg
      exact hg
    have hz : ∀ j : {j : ι // j ∈ J}, g (Sum.inr j) = 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨j0, hj0⟩ := hcon
      have hsplit : (∑ j : {j : ι // j ∈ J}, g (Sum.inr j) • b (j : ι))
          = g (Sum.inr j0) • b (j0 : ι)
            + ∑ j ∈ Finset.univ.erase j0, g (Sum.inr j) • b (j : ι) :=
        (Finset.add_sum_erase Finset.univ
          (fun j : {j : ι // j ∈ J} => g (Sum.inr j) • b (j : ι)) (Finset.mem_univ j0)).symm
      rw [hsplit] at hg'
      have hA : (∑ i : Fin h, g (Sum.inl i) • c i)
          ∈ Submodule.span K (Set.range c ∪ (⇑b) '' (↑(J.erase (j0 : ι)) : Set ι)) := by
        refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
        exact Submodule.subset_span (Set.mem_union_left _ ⟨i, rfl⟩)
      have hB : (∑ j ∈ Finset.univ.erase j0, g (Sum.inr j) • b (j : ι))
          ∈ Submodule.span K (Set.range c ∪ (⇑b) '' (↑(J.erase (j0 : ι)) : Set ι)) := by
        refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
        have hne : (j : ι) ≠ (j0 : ι) := by
          intro hh
          exact (Finset.ne_of_mem_erase hj) (Subtype.ext hh)
        exact Submodule.subset_span (Set.mem_union_right _
          ⟨(j : ι), Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne, j.2⟩), rfl⟩)
      have hxmem : g (Sum.inr j0) • b (j0 : ι)
          ∈ Submodule.span K (Set.range c ∪ (⇑b) '' (↑(J.erase (j0 : ι)) : Set ι)) := by
        have hid : g (Sum.inr j0) • b (j0 : ι)
            = ((∑ i : Fin h, g (Sum.inl i) • c i)
                + (g (Sum.inr j0) • b (j0 : ι)
                  + ∑ j ∈ Finset.univ.erase j0, g (Sum.inr j) • b (j : ι)))
              - (∑ i : Fin h, g (Sum.inl i) • c i)
              - ∑ j ∈ Finset.univ.erase j0, g (Sum.inr j) • b (j : ι) := by
          abel
        rw [hid, hg']
        exact Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.zero_mem _) hA) hB
      have hbj0 : b (j0 : ι)
          ∈ Submodule.span K (Set.range c ∪ (⇑b) '' (↑(J.erase (j0 : ι)) : Set ι)) := by
        have hsm := Submodule.smul_mem _ (g (Sum.inr j0))⁻¹ hxmem
        rwa [smul_smul, inv_mul_cancel₀ hj0, one_smul] at hsm
      exact hJmin (j0 : ι) j0.2 (span_union_image_erase_eq_top hJtop hbj0)
    intro x
    cases x with
    | inl i =>
        have hzero : (∑ j : {j : ι // j ∈ J}, g (Sum.inr j) • b (j : ι)) = 0 :=
          Finset.sum_eq_zero fun j _ => by rw [hz j, zero_smul]
        rw [hzero, add_zero] at hg'
        exact Fintype.linearIndependent_iff.mp hc (fun i => g (Sum.inl i)) hg' i
    | inr j => exact hz j
  have hsp : (⊤ : Submodule K V)
      ≤ Submodule.span K (Set.range (Sum.elim c (fun j : {j : ι // j ∈ J} => b (j : ι)))) := by
    rw [hrange]
    exact le_of_eq hJtop.symm
  refine ⟨J, Module.Basis.mk hli hsp, fun i => ?_, fun j => ?_⟩
  · exact Module.Basis.mk_apply hli hsp (Sum.inl i)
  · exact Module.Basis.mk_apply hli hsp (Sum.inr j)
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
