-- Prove2me | solution 1 for Formalism.GM.TM.adStep_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:47.757844+00:00
-- url     : https://prove2.me/submissions/4ca118c5-c632-498b-b451-79d4924b948d

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Theorems.Thm_Formalism_GM_TM_filL_sat
import Theorems.Thm_Formalism_GM_TM_filL_anti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.GM.TM
theorem _root_.solution (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (v : σ) (hFG : L.FG) (e : ℕ)
    (h : AdStep L v (e + 1)) : AdStep L v e := by
  obtain ⟨ι, _, f, ord, hli, hsp, hord, hfil⟩ := h
  have hle : filL L v (e + 1) ≤ filL L v e := filL_anti L v (Nat.le_succ e)
  have hfmem : ∀ i, f i ∈ filL L v (e + 1) := fun i => by
    rw [← hsp]; exact Submodule.subset_span ⟨i, rfl⟩
  let Fe := filL L v e
  let Fe1 := filL L v (e + 1)
  let Im : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p] ⧸ Fe1) := Fe.map Fe1.mkQ
  have hFeFG : Fe.FG := Submodule.FG.of_le hFG inf_le_left
  haveI : Module.Finite ℤ_[p] Im := Module.Finite.iff_fg.mpr (hFeFG.map _)
  haveI : Module.IsTorsionFree ℤ_[p] Im := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    rintro a ⟨y, hy⟩ h
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    by_cases ha : a = 0
    · left; exact ha
    · right
      have h' : a • Fe1.mkQ x = 0 := by
        have := congrArg Subtype.val h
        simpa using this
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h'
      have := filL_sat L v (e+1) a ha x (Submodule.mem_inf.mp hx).1 h'
      apply Subtype.ext
      change Fe1.mkQ x = 0
      rw [Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero _).mpr this
  obtain ⟨k, bQ⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ_[p]) (M := Im)
  have hlift : ∀ j, ∃ x, x ∈ Fe ∧ Fe1.mkQ x = (bQ j : MvPolynomial σ ℚ_[p] ⧸ Fe1) := fun j =>
    Submodule.mem_map.mp (bQ j).2
  choose g hgFe hgmk using hlift
  have hgnot : ∀ j, g j ∉ Fe1 := by
    intro j hj
    apply bQ.ne_zero j
    apply Subtype.ext
    rw [← hgmk j, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hj]
    rfl
  have hspanEq : Submodule.span ℤ_[p] (Set.range (Sum.elim f g)) = Fe := by
    rw [Set.Sum.elim_range, Submodule.span_union, hsp]
    apply le_antisymm
    · exact sup_le hle (Submodule.span_le.mpr (Set.range_subset_iff.mpr hgFe))
    · intro x hx
      have hxI : Fe1.mkQ x ∈ Im := Submodule.mem_map_of_mem hx
      have htop : (⟨Fe1.mkQ x, hxI⟩ : Im) ∈ Submodule.span ℤ_[p] (Set.range bQ) := by
        rw [bQ.span_eq]; exact Submodule.mem_top
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).mp htop
      have hc' : ∑ j, c j • Fe1.mkQ (g j) = Fe1.mkQ x := by
        have := congrArg Subtype.val hc
        simp only [Submodule.coe_sum, Submodule.coe_smul] at this
        rw [← this]
        apply Finset.sum_congr rfl
        intro j _
        rw [hgmk j]
      have hc2 : Fe1.mkQ (∑ j, c j • g j) = Fe1.mkQ x := by
        rw [map_sum]; simp only [map_smul]; exact hc'
      simp only [Submodule.mkQ_apply] at hc2
      have hdiff : x - ∑ j, c j • g j ∈ Fe1 := (Submodule.Quotient.eq Fe1).mp hc2.symm
      have : x = (x - ∑ j, c j • g j) + ∑ j, c j • g j := by abel
      rw [this]
      refine Submodule.add_mem _ (Submodule.mem_sup_left hdiff) (Submodule.mem_sup_right ?_)
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  refine ⟨ι ⊕ Fin k, inferInstance, Sum.elim f g, Sum.elim ord (fun _ => e), ?_, ?_, ?_, ?_⟩
  ·
    let f' : ι → Fe1 := fun i => ⟨f i, hfmem i⟩
    have hf' : LinearIndependent ℤ_[p] f' := LinearIndependent.of_comp Fe1.subtype hli
    have hg : LinearIndependent ℤ_[p] (Submodule.Quotient.mk (p := Fe1) ∘ g) := by
      have hb := bQ.linearIndependent.map' Im.subtype (Submodule.ker_subtype Im)
      have : Submodule.Quotient.mk (p := Fe1) ∘ g = Im.subtype ∘ bQ := by
        funext j; simp only [Function.comp_apply, Submodule.subtype_apply]; rw [← hgmk j]; rfl
      rw [this]; exact hb
    exact LinearIndependent.sumElim_of_quotient hf' g hg
  · exact hspanEq
  ·
    rintro (i | j)
    · exact ⟨(hord i).1, le_trans (Nat.le_succ e) (hord i).2⟩
    · refine ⟨⟨fun m hm => ?_, ?_⟩, le_rfl⟩
      · have h2 := (Submodule.mem_inf.mp (hgFe j)).2
        change g j ∈ MvPolynomial.restrictSupport ℚ_[p] _ at h2
        rw [mem_restrictSupport_iff] at h2
        exact h2 (Finset.mem_coe.mpr hm)
      · by_contra hc
        push Not at hc
        apply hgnot j
        refine Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp (hgFe j)).1, ?_⟩
        have h2 := (Submodule.mem_inf.mp (hgFe j)).2
        change g j ∈ MvPolynomial.restrictSupport ℚ_[p] _ at h2
        change g j ∈ MvPolynomial.restrictSupport ℚ_[p] _
        rw [mem_restrictSupport_iff] at h2 ⊢
        intro m hm
        have h3 : e ≤ m v := h2 hm
        have h4 : m v ≠ e := hc m hm
        simp only [Set.mem_setOf_eq]
        omega
  ·
    intro e' he'
    rcases Nat.eq_or_lt_of_le he' with rfl | hlt
    · have : {b : ι ⊕ Fin k | e ≤ Sum.elim ord (fun _ => e) b} = Set.univ := by
        ext b; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        rcases b with i | j
        · exact le_trans (Nat.le_succ e) (hord i).2
        · exact le_rfl
      rw [this, Set.image_univ]
      exact hspanEq
    · have : Sum.elim f g '' {b | e' ≤ Sum.elim ord (fun _ => e) b} = f '' {i | e' ≤ ord i} := by
        ext x
        constructor
        · rintro ⟨b, hb, rfl⟩
          rcases b with i | j
          · exact ⟨i, hb, rfl⟩
          · simp only [Set.mem_setOf_eq, Sum.elim_inr] at hb; omega
        · rintro ⟨i, hi, rfl⟩
          exact ⟨Sum.inl i, hi, rfl⟩
      rw [this]
      exact hfil e' hlt
end Formalism.GM.TM
