-- Prove2me | solution 1 for Formalism.L2.Th1.H.fundamentalDomainExists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:19.006531+00:00
-- url     : https://prove2.me/submissions/f6cc6e1a-a446-4f22-a807-e655ac10dbd9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexEqAbsDetReal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionFiltrationStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators ComplexConjugate Pointwise
open MeasureTheory Module
namespace Formalism.L2.Th1.H
private theorem exists_real_basis_span_int_eq_of_isLat {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (Λ : AddSubgroup V) (hΛ : IsLat Λ) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ V),
      (Submodule.span ℤ (Set.range b)).toAddSubgroup = Λ := by
  obtain ⟨hdisc, hspan⟩ := hΛ
  let L : Submodule ℤ V := AddSubgroup.toIntSubmodule Λ
  haveI : DiscreteTopology L := hdisc
  haveI : IsZLattice ℝ L := ⟨hspan⟩
  refine ⟨_, inferInstance, (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L, ?_⟩
  rw [Module.Basis.ofZLatticeBasis_span]
  rfl
end Formalism.L2.Th1.H
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Pointwise
open MeasureTheory Module
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution : FundDomain := by
  intro V _ _ _ _ _ μ _ Λ hΛ
  obtain ⟨ι, _, b, hb⟩ := exists_real_basis_span_int_eq_of_isLat Λ hΛ
  subst hb
  set L := (Submodule.span ℤ (Set.range b)).toAddSubgroup with hL
  set D := ZSpan.fundamentalDomain b with hDdef
  have hFD : IsAddFundamentalDomain L D μ := ZSpan.isAddFundamentalDomain b μ
  have hbdd : Bornology.IsBounded D := ZSpan.fundamentalDomain_isBounded b
  have hmeas : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet b
  have hne : μ D ≠ 0 := ZSpan.measure_fundamentalDomain_ne_zero b
  have htop : μ D ≠ ⊤ := hbdd.measure_lt_top.ne
  refine ⟨D, hFD, hbdd, ENNReal.toReal_pos hne htop, ?_⟩
  intro Λ' hle hidx
  have hmem : ∀ v : V, v ∈ L → ∀ x : V, (v + x ∈ D ↔ v = -(ZSpan.floor b x : V)) := by
    intro v hv x
    have := ZSpan.vadd_mem_fundamentalDomain b ⟨v, hv⟩ x
    rw [Subtype.ext_iff, Submodule.coe_neg] at this
    exact this
  have hfl : ∀ x : V, (ZSpan.floor b x : V) ∈ L := fun x => (ZSpan.floor b x).2
  set H := Λ'.addSubgroupOf L with hH
  have hcardQ : Nat.card (L ⧸ H) = relIdx Λ' L := rfl
  haveI : Finite (L ⧸ H) := Nat.finite_of_card_ne_zero (by rw [hcardQ]; exact hidx)
  letI : Fintype (L ⧸ H) := Fintype.ofFinite _
  let rep : L ⧸ H → V := fun q => ((Quotient.out q : L) : V)
  have hrepL : ∀ q, rep q ∈ L := fun q => (Quotient.out q).2
  have hrep : ∀ q : L ⧸ H, ((Quotient.out q : L) : L ⧸ H) = q := fun q => QuotientAddGroup.out_eq' q
  have hdisj : Pairwise (Function.onFun Disjoint fun q : L ⧸ H => rep q +ᵥ D) := by
    intro p q hpq
    rw [Function.onFun, Set.disjoint_left]
    intro y hyp hyq
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] at hyp hyq
    have e1 := (hmem _ (L.neg_mem (hrepL p)) y).mp hyp
    have e2 := (hmem _ (L.neg_mem (hrepL q)) y).mp hyq
    apply hpq
    have hpq' : rep p = rep q := by
      rw [← neg_neg (rep p), e1, ← e2, neg_neg]
    rw [← hrep p, ← hrep q]
    congr 1
    exact Subtype.ext hpq'
  refine ⟨⋃ q : L ⧸ H, rep q +ᵥ D, ?_, ?_, ?_⟩
  · refine IsAddFundamentalDomain.mk' (MeasurableSet.iUnion fun q => hmeas.const_vadd _).nullMeasurableSet ?_
    intro x
    set l0 : V := -(ZSpan.floor b x : V) with hl0def
    have hl0 : l0 ∈ L := L.neg_mem (hfl x)
    set q0 : L ⧸ H := ((⟨-l0, L.neg_mem hl0⟩ : L) : L ⧸ H) with hq0def
    have hq0 : rep q0 + l0 ∈ Λ' := by
      have h1 := hrep q0
      rw [hq0def, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
      have h2 : -(-(rep q0) + -l0) ∈ Λ' := Λ'.neg_mem (by simpa [rep] using h1)
      rwa [neg_add_rev, neg_neg, neg_neg, add_comm] at h2
    refine ⟨⟨rep q0 + l0, hq0⟩, ?_, ?_⟩
    · show rep q0 + l0 + x ∈ ⋃ q : L ⧸ H, rep q +ᵥ D
      refine Set.mem_iUnion.mpr ⟨q0, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
        show -rep q0 + (rep q0 + l0 + x) = l0 + x by abel]
      exact (hmem l0 hl0 x).mpr rfl
    · intro g hg
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hg
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] at hq
      have hgx : -rep q + (g : V) + x ∈ D := by
        rw [add_assoc]
        exact hq
      have hv : -rep q + (g : V) ∈ L := L.add_mem (L.neg_mem (hrepL q)) (hle g.2)
      have e1 : -rep q + (g : V) = l0 := (hmem _ hv x).mp hgx
      have hqq : q = q0 := by
        rw [← hrep q, hq0def, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
        have h3 : -rep q + -l0 = -(g : V) := by
          rw [← e1]
          abel
        have h4 : -(g : V) ∈ Λ' := Λ'.neg_mem g.2
        simpa [rep, h3] using h4
      apply Subtype.ext
      show (g : V) = rep q0 + l0
      rw [← hqq, ← e1]
      abel
  · exact Bornology.isBounded_iUnion.mpr fun q => hbdd.vadd (rep q)
  · have hμ : μ (⋃ q : L ⧸ H, rep q +ᵥ D) = (Fintype.card (L ⧸ H) : ENNReal) * μ D := by
      rw [measure_iUnion hdisj (fun q => hmeas.const_vadd _), tsum_fintype]
      simp [measure_vadd]
    rw [hμ, ENNReal.toReal_mul, ENNReal.toReal_natCast, ← hcardQ, Nat.card_eq_fintype_card]
end Formalism.L2.Th1.H
