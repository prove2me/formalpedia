-- Prove2me | solution 1 for DensInertW.isoPeel_of_valCount
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:37.938531+00:00
-- url     : https://prove2.me/submissions/c8417c51-78f0-43e3-8c0b-e3c9eeb569b2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ValMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_IsoPeel
import Theorems.Thm_DensInertW_iso_cntT_zero_eq
import Theorems.Thm_DensInertW_iso_fiber
import Theorems.Thm_DensInertW_Sub_hf_add_right
import Theorems.Thm_DensInertW_Sub_hf_smul_right
import Theorems.Thm_DensInertW_Sub_hf_sub_left
import Theorems.Thm_DensInertW_Sub_hf_symm
import Theorems.Thm_DensInertW_Sub_hf_zero_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
open DensInertW
open DensInertW.Sub
namespace DensInertW
theorem _root_.solution (hv : ValCount) : IsoPeel := by
  intro K L _ _ _ _ _ hKL n M W hM hW c k hk
  classical
  set q := Fintype.card K with hq_def
  have hcardL : Fintype.card L = q ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := K), hKL]
  have hinv : ∀ a : L, (a ^ q) ^ q = a := fun a => by
    rw [← pow_mul, ← sq, ← hcardL, FiniteField.pow_card]
  have hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q := by
    obtain ⟨nn, hp, hpn⟩ := FiniteField.card K (ringChar K)
    haveI : Fact (ringChar K).Prime := ⟨hp⟩
    haveI : CharP L (ringChar K) :=
      charP_of_injective_algebraMap (algebraMap K L).injective (ringChar K)
    intro a b
    rw [hq_def, hpn]
    exact add_pow_char_pow a b (ringChar K) nn
  have hq0 : q ≠ 0 := Fintype.card_ne_zero
  have hsymm : ∀ a b, hf q M b a = (hf q M a b) ^ q := hf_symm hadd hinv hM
  rw [iso_cntT_zero_eq]
  set S : Finset (Fin n → L) := Finset.univ.filter (fun v => v ∈ W ∧ v ≠ 0 ∧ hf q M v v = 0) with hS
  have hmaps : ∀ X ∈ Finset.univ.filter (isoP (m := c + 1) q M W), X 0 ∈ S := by
    intro X hX
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, isoP] at hX
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hX.1 0, hX.2.1.ne_zero 0, hX.2.2 0 0⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]

  have hfib : ∀ x ∈ S, (((Finset.univ.filter (isoP (m := c + 1) q M W)).filter
      (fun X => X 0 = x)).card : ℤ) = (q : ℤ) ^ (2 * c) * k := by
    intro x hx
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hxW, hx0, hxx⟩ := hx
    have hex : ∃ v ∈ W, hf q M x v ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx0 (hW x hxW h)
    obtain ⟨v, hvW, hv⟩ := hex
    obtain ⟨y, hy⟩ : ∃ y : Fin n → L, y = ((hf q M x v)⁻¹ ^ q) • v := ⟨_, rfl⟩
    have hxy : hf q M x y = 1 := by
      rw [hy, hf_smul_right, hinv, inv_mul_cancel₀ hv]
    have hyW : y ∈ W := by
      rw [hy]
      exact W.smul_mem _ hvW
    have hyx : hf q M y x = 1 := by rw [hsymm, hxy, one_pow]
    set W' : Submodule L (Fin n → L) :=
      W ⊓ LinearMap.ker (hfL q M x) ⊓ LinearMap.ker (hfL q M y) with hW'
    have hmemW' : ∀ u, u ∈ W' ↔ u ∈ W ∧ hf q M u x = 0 ∧ hf q M u y = 0 := fun u => by
      simp only [hW', Submodule.mem_inf, LinearMap.mem_ker]
      exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

    have hdec : ∀ u ∈ W, ∃ u' ∈ W', ∃ α β : L, u = u' + α • x + β • y := by
      intro u hu
      refine ⟨u - (hf q M u y - hf q M u x * hf q M y y) • x - hf q M u x • y, ?_,
        hf q M u y - hf q M u x * hf q M y y, hf q M u x, by abel⟩
      rw [hmemW']
      refine ⟨W.sub_mem (W.sub_mem hu (W.smul_mem _ hxW)) (W.smul_mem _ hyW), ?_, ?_⟩
      · rw [hf_sub_left, hf_sub_left, hf_smul_left, hf_smul_left, hxx, hyx]
        ring
      · rw [hf_sub_left, hf_sub_left, hf_smul_left, hf_smul_left, hxy]
        ring
    have hnd : NonDeg q M W' := by
      intro w hw hwall
      rw [hmemW'] at hw
      obtain ⟨hwW, hwx, hwy⟩ := hw
      apply hW w hwW
      intro u hu
      obtain ⟨u', hu', α, β, rfl⟩ := hdec u hu
      rw [hf_add_right hadd, hf_add_right hadd, hf_smul_right, hf_smul_right, hwall u' hu', hwx, hwy]
      ring

    have hdim : Module.finrank L W' + 2 = Module.finrank L W := by
      let ψ : W →ₗ[L] L × L := LinearMap.prod ((hfL q M x).comp W.subtype) ((hfL q M y).comp W.subtype)
      have hψ : ∀ w : W, ψ w = (hf q M w x, hf q M w y) := fun w => rfl
      have hsurj : Function.Surjective ψ := by
        rintro ⟨s, t⟩
        refine ⟨(t - s * hf q M y y) • ⟨x, hxW⟩ + s • ⟨y, hyW⟩, ?_⟩
        rw [hψ]
        simp only [Submodule.coe_add, Submodule.coe_smul, hf_add_left, hf_smul_left, hxx, hyx, hxy]
        ext <;> simp <;> ring
      have hrange : LinearMap.range ψ = ⊤ := LinearMap.range_eq_top.2 hsurj
      have hrn := LinearMap.finrank_range_add_finrank_ker ψ
      rw [hrange, finrank_top, Module.finrank_prod, Module.finrank_self] at hrn
      have hmap : (LinearMap.ker ψ).map W.subtype = W' := by
        ext u
        rw [hmemW', Submodule.mem_map]
        constructor
        · rintro ⟨w, hw, rfl⟩
          rw [LinearMap.mem_ker, hψ, Prod.mk_eq_zero] at hw
          exact ⟨w.2, hw.1, hw.2⟩
        · rintro ⟨huW, hux, huy⟩
          refine ⟨⟨u, huW⟩, ?_, rfl⟩
          rw [LinearMap.mem_ker, hψ, Prod.mk_eq_zero]
          exact ⟨hux, huy⟩
      have hfr : Module.finrank L W' = Module.finrank L (LinearMap.ker ψ) := by
        rw [← hmap]
        exact (Submodule.equivMapOfInjective _ W.injective_subtype _).finrank_eq.symm
      omega
    have hkW' := hk W' hnd hdim
    rw [iso_cntT_zero_eq] at hkW'
    rw [Finset.filter_filter, iso_fiber hadd hinv hM W x y hxW hyW hxx hxy]
    push_cast
    rw [hkW', Fintype.card_fun, Fintype.card_fin, hcardL]
    push_cast
    ring

  have hval := hv K L hKL n M W hM hW 0 (by rw [zero_pow hq0])
  simp only [if_true] at hval
  have hT : ({v : Fin n → L | v ∈ W ∧ hf q M v v = 0}.ncard) =
      (Finset.univ.filter fun v => v ∈ W ∧ hf q M v v = 0).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext v
    simp
  have hS' : S = (Finset.univ.filter fun v => v ∈ W ∧ hf q M v v = 0).erase 0 := by
    ext v
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    tauto
  have h0mem : (0 : Fin n → L) ∈ Finset.univ.filter fun v => v ∈ W ∧ hf q M v v = 0 := by
    simp [hf_zero_left]
  have hcardS := Finset.card_erase_add_one h0mem
  rw [← hS'] at hcardS
  rw [hT] at hval
  push_cast
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
  have hScast : (S.card : ℤ) = valZ q (Module.finrank L W) - 1 := by
    have h1 : (S.card : ℤ) + 1 = ((Finset.univ.filter fun v => v ∈ W ∧ hf q M v v = 0).card : ℤ) := by
      exact_mod_cast hcardS
    rw [← hq_def] at hval
    linarith
  rw [hScast]
  ring
end DensInertW
