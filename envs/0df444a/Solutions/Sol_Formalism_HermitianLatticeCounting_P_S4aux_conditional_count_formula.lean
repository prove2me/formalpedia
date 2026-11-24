-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.conditional_count_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:04.516286+00:00
-- url     : https://prove2.me/submissions/06d8c0c2-d9ef-4380-8230-5cd6abaaf74e

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_index_span_pow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_card_of_surj
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : CondCount := by
  intro o T _ _ _ _ _ _ ϖ red cond q a hϖ hq hq2 hsurj hker hcond
  classical
  have hT : Fintype.card T = q ^ a := by
    rw [← Nat.card_eq_fintype_card]; exact card_of_surj ϖ hϖ q hq a red hsurj hker
  have h0 : ∀ ψ, cond ψ = 0 ↔ ψ = 0 := by
    intro ψ
    rw [← Nat.le_zero, hcond]
    constructor
    · intro h
      ext t
      obtain ⟨x, rfl⟩ := hsurj t
      simpa using h x
    · rintro rfl x; simp
  have ha : ∀ ψ, cond ψ ≤ a := by
    intro ψ
    rw [hcond]
    intro x
    have : red (ϖ ^ a * x) = 0 := (hker _).2 (dvd_mul_right _ _)
    rw [this, AddChar.map_zero_eq_one]
  have hle : ∀ i, (univ.filter fun ψ : AddChar T ℂ => cond ψ ≤ i).card ≤ q ^ i := by
    intro i
    set N : AddSubgroup o := (Ideal.span {ϖ ^ i}).toAddSubgroup with hN
    have hcardN : Nat.card (o ⧸ N) = q ^ i := index_span_pow ϖ hϖ q hq i
    have : Finite (o ⧸ N) := Nat.finite_of_card_ne_zero (by rw [hcardN]; positivity)
    have : Fintype (o ⧸ N) := Fintype.ofFinite _
    have hl : ∀ ψ : {ψ : AddChar T ℂ // cond ψ ≤ i}, ∀ x ∈ N,
        (ψ.1.compAddMonoidHom red).toAddMonoidHom x = 0 := by
      intro ψ x hx
      rw [hN, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton] at hx
      obtain ⟨y, rfl⟩ := hx
      have := (hcond ψ.1 i).1 ψ.2 y
      change Additive.ofMul (ψ.1 (red (ϖ ^ i * y))) = 0
      rw [this]; rfl
    let Φ : {ψ : AddChar T ℂ // cond ψ ≤ i} → AddChar (o ⧸ N) ℂ := fun ψ =>
      AddChar.toAddMonoidHomEquiv.symm (QuotientAddGroup.lift N _ (hl ψ))
    have hΦ : ∀ ψ x, Φ ψ (QuotientAddGroup.mk x) = ψ.1 (red x) := fun ψ x => rfl
    have hinj : Function.Injective Φ := by
      intro ψ ψ' h
      apply Subtype.ext
      ext t
      obtain ⟨x, rfl⟩ := hsurj t
      rw [← hΦ, ← hΦ, h]
    calc (univ.filter fun ψ : AddChar T ℂ => cond ψ ≤ i).card
        = Fintype.card {ψ : AddChar T ℂ // cond ψ ≤ i} := (Fintype.card_subtype _).symm
      _ ≤ Fintype.card (AddChar (o ⧸ N) ℂ) := Fintype.card_le_of_injective Φ hinj
      _ = Fintype.card (o ⧸ N) := AddChar.card_eq
      _ = q ^ i := by rw [← Nat.card_eq_fintype_card, hcardN]
  refine ⟨hT, h0, ha, fun i => ?_, fun i hi => ?_⟩
  · have h1 : (univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card ≤ q ^ i :=
      (Finset.card_le_card (fun ψ hψ => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ ⊢; omega)).trans (hle i)
    exact_mod_cast h1
  · have h1 : (univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card < q ^ i := by
      refine lt_of_lt_of_le (Finset.card_lt_card ?_) (hle i)
      rw [Finset.ssubset_iff_of_subset (fun ψ hψ => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ ⊢; omega)]
      refine ⟨0, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [(h0 0).2 rfl]; omega
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [(h0 0).2 rfl]; omega
    exact_mod_cast h1
end Formalism.HermitianLatticeCounting.P.S4aux
