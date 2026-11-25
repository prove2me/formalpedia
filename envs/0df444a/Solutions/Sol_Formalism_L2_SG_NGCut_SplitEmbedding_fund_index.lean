-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.SplitEmbedding.fund_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:23:40.066949+00:00
-- url     : https://prove2.me/submissions/7b04b675-ad64-4af3-9876-a9a334494900

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MassSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory
namespace Formalism.L2.SG.NGCut.SplitEmbedding
private theorem isAddFundamentalDomain_of_existsUnique {V : Type} [AddCommGroup V]
    [MeasurableSpace V] (μ : Measure V) (L : AddSubgroup V) (F : Set V) (hF : MeasurableSet F)
    (h : ∀ v, ∃! l : L, (l : V) + v ∈ F) : IsAddFundamentalDomain L F μ :=
  IsAddFundamentalDomain.mk' hF.nullMeasurableSet fun v => h v
private theorem existsUnique_neg_section_add_mem {V : Type} [AddCommGroup V]
    (L Λ : AddSubgroup V) (σ : L ⧸ Λ.addSubgroupOf L → L)
    (hσ : ∀ q, (QuotientAddGroup.mk (σ q) : L ⧸ Λ.addSubgroupOf L) = q)
    (m : V) (hm : m ∈ L) : ∃! q : L ⧸ Λ.addSubgroupOf L, -((σ q : L) : V) + m ∈ Λ := by
  have key : ∀ q : L ⧸ Λ.addSubgroupOf L,
      (-((σ q : L) : V) + m ∈ Λ ↔ q = QuotientAddGroup.mk ⟨m, hm⟩) := by
    intro q
    have e : q = QuotientAddGroup.mk ⟨m, hm⟩ ↔
        (QuotientAddGroup.mk (σ q) : L ⧸ Λ.addSubgroupOf L) = QuotientAddGroup.mk ⟨m, hm⟩ := by
      rw [hσ q]
    rw [e]
    first
    | rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    | rw [QuotientAddGroup.eq', AddSubgroup.mem_addSubgroupOf]
    first
    | exact Iff.rfl
    | simp
  exact ⟨QuotientAddGroup.mk ⟨m, hm⟩, (key _).2 rfl, fun q hq => (key q).1 hq⟩
private theorem existsUnique_mem_iUnion_translate_preimage {V : Type} [AddCommGroup V]
    (L Λ : AddSubgroup V) (hle : Λ ≤ L) (FL : Set V) (hdL : ∀ v, ∃! l : L, (l : V) + v ∈ FL)
    {ι : Type*} (ρ : ι → V) (hρL : ∀ i, ρ i ∈ L) (hρ : ∀ m ∈ L, ∃! i, ρ i + m ∈ Λ) (v : V) :
    ∃! a : Λ, (a : V) + v ∈ ⋃ i, (fun w => ρ i + w) ⁻¹' FL := by
  obtain ⟨l, hl, hlu⟩ := hdL v
  obtain ⟨i, hi, hiu⟩ := hρ (-(l : V)) (L.neg_mem l.2)
  have ha : (l : V) - ρ i ∈ Λ := by
    have e : (l : V) - ρ i = -(ρ i + -(l : V)) := by abel
    rw [e]
    exact Λ.neg_mem hi
  refine ⟨⟨(l : V) - ρ i, ha⟩, ?_, ?_⟩
  · refine Set.mem_iUnion.2 ⟨i, ?_⟩
    show ρ i + (((l : V) - ρ i) + v) ∈ FL
    rw [show ρ i + (((l : V) - ρ i) + v) = (l : V) + v by abel]
    exact hl
  · intro b hb
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hb
    have hj' : ((⟨ρ j + (b : V), L.add_mem (hρL j) (hle b.2)⟩ : L) : V) + v ∈ FL := by
      show ρ j + (b : V) + v ∈ FL
      rw [add_assoc]
      exact hj
    have hy : ρ j + (b : V) = l := congrArg Subtype.val (hlu _ hj')
    have hj2 : ρ j + -(l : V) ∈ Λ := by
      have e : ρ j + -(l : V) = -(b : V) := by rw [← hy]; abel
      rw [e]
      exact Λ.neg_mem b.2
    have hji : j = i := hiu j hj2
    rw [hji] at hy
    apply Subtype.ext
    show (b : V) = (l : V) - ρ i
    rw [← hy]
    abel
private theorem pairwise_disjoint_translate_preimage {V : Type} [AddCommGroup V]
    (L Λ : AddSubgroup V) (FL : Set V) (hdL : ∀ v, ∃! l : L, (l : V) + v ∈ FL)
    {ι : Type*} (ρ : ι → V) (hρL : ∀ i, ρ i ∈ L) (hρ : ∀ m ∈ L, ∃! i, ρ i + m ∈ Λ) :
    Pairwise (Function.onFun Disjoint fun i => (fun w => ρ i + w) ⁻¹' FL) := by
  intro i j hij
  refine Set.disjoint_left.2 fun w hi hj => hij ?_
  have e : (⟨ρ i, hρL i⟩ : L) = ⟨ρ j, hρL j⟩ :=
    (hdL w).unique (show ((⟨ρ i, hρL i⟩ : L) : V) + w ∈ FL from hi)
      (show ((⟨ρ j, hρL j⟩ : L) : V) + w ∈ FL from hj)
  have e' : ρ i = ρ j := congrArg Subtype.val e
  obtain ⟨q, -, hq⟩ := hρ (-ρ i) (L.neg_mem (hρL i))
  have h1 : i = q := hq i (by simp)
  have h2 : j = q := hq j (by show ρ j + -ρ i ∈ Λ; rw [← e']; simp)
  rw [h1, h2]
end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.SplitEmbedding
namespace Formalism.L2.SG.NGCut.SplitEmbedding
theorem _root_.solution {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V)
    [μ.IsAddLeftInvariant] (L Λ : AddSubgroup V) [Countable L] (hle : Λ ≤ L) (k : ℕ)
    (hk : Λ.relIndex L = k) (hk0 : k ≠ 0) (FL FΛ : Set V) (hFL : MeasurableSet FL) (hFΛ : MeasurableSet FΛ)
    (hdL : ∀ v, ∃! l : L, (l : V) + v ∈ FL) (hdΛ : ∀ v, ∃! a : Λ, (a : V) + v ∈ FΛ) :
    μ FΛ = k * μ FL := by
  classical
  have hcard : Nat.card (L ⧸ Λ.addSubgroupOf L) = k := hk
  haveI : Finite (L ⧸ Λ.addSubgroupOf L) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hk0)
  haveI : Fintype (L ⧸ Λ.addSubgroupOf L) := Fintype.ofFinite _
  haveI : Countable Λ := Function.Injective.countable (AddSubgroup.inclusion_injective hle)
  haveI : MeasurableVAdd Λ V := by
    first
    | infer_instance
    | exact ⟨fun c => measurable_const_add (c : V), fun v => (measurable_add_const v).comp measurable_subtype_coe⟩
  haveI : VAddInvariantMeasure Λ V μ := by
    first
    | infer_instance
    | exact ⟨fun c s _ => measure_preimage_add μ (c : V) s⟩
  have hsurj : Function.Surjective (QuotientAddGroup.mk : L → L ⧸ Λ.addSubgroupOf L) :=
    QuotientAddGroup.mk_surjective
  obtain ⟨ρ, hρL, hρ⟩ : ∃ ρ : L ⧸ Λ.addSubgroupOf L → V,
      (∀ q, ρ q ∈ L) ∧ ∀ m ∈ L, ∃! q, ρ q + m ∈ Λ :=
    ⟨fun q => -((Function.surjInv hsurj q : L) : V), fun q => L.neg_mem (Function.surjInv hsurj q).2,
      fun m hm => existsUnique_neg_section_add_mem L Λ (Function.surjInv hsurj)
        (Function.surjInv_eq hsurj) m hm⟩
  have hmeas : ∀ q, MeasurableSet ((fun w => ρ q + w) ⁻¹' FL) := fun q =>
    measurable_const_add (ρ q) hFL
  have hU : IsAddFundamentalDomain Λ (⋃ q, (fun w => ρ q + w) ⁻¹' FL) μ :=
    isAddFundamentalDomain_of_existsUnique μ Λ _ (MeasurableSet.iUnion hmeas)
      (existsUnique_mem_iUnion_translate_preimage L Λ hle FL hdL ρ hρL hρ)
  have hΛ : IsAddFundamentalDomain Λ FΛ μ := isAddFundamentalDomain_of_existsUnique μ Λ FΛ hFΛ hdΛ
  rw [hΛ.measure_eq hU, measure_iUnion (pairwise_disjoint_translate_preimage L Λ FL hdL ρ hρL hρ) hmeas]
  simp only [measure_preimage_add]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    hcard]
end Formalism.L2.SG.NGCut.SplitEmbedding
