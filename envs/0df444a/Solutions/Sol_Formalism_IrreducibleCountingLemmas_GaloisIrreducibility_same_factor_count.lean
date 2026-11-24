-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.same_factor_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:19:35.6978+00:00
-- url     : https://prove2.me/submissions/85b737ad-63dc-4c8b-9a3e-9cbd86e79ba3

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRFrobOrbitIrred
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSamePartCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CoeffZeroNeZeroOfIrreducible
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_root_conj
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_root_pow_card_mul
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_coeff_zero_ne_zero_of_irreducible
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_root_pow_sub_one
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mul_card_le_of_roots_mem
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_nthRootsFinset_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_lpow_le_rpow_quarter
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_lpow_order_iff
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_monic
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_natDegree
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_prime_to_part_endomorphism
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_prime_to_part_spec
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : SameFactorCount := by
  classical
  intro K L _ _ _ _ _ δ l hl hδ hBB
  have : Fact l.Prime := ⟨hl⟩
  set g := Fintype.card K with hgdef
  have hg : 2 ≤ g := Fintype.one_lt_card
  set n := g ^ δ - 1 with hn
  set v := padicValNat l n with hv
  have hgd : 2 ≤ g ^ δ := hg.trans (Nat.le_self_pow (by omega) g)
  have hn0 : n ≠ 0 := by omega
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (by omega : 1 ≤ g)
  have hlv : ((l ^ v : ℕ) : ℝ) ≤ (g : ℝ) ^ ((δ : ℝ) / 4) := lpow_le_rpow_quarter hBB
  set B : ℝ := (g : ℝ) ^ ((δ : ℝ) / 2) * (g : ℝ) ^ ((δ : ℝ) / 4) with hB
  set I := (Finset.range δ).filter (fun e => e ∣ δ) with hI
  set T : ℕ → Finset L := fun e => nthRootsFinset ((g ^ e - 1) * l ^ v) (1 : L) with hT
  have hmpos : ∀ e ∈ I, 0 < (g ^ e - 1) * l ^ v := by
    intro e he
    simp only [hI, Finset.mem_filter, Finset.mem_range] at he
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · subst h0; have := Nat.eq_zero_of_zero_dvd he.2; omega
      · exact h0
    have hge : 2 ≤ g ^ e := hg.trans (Nat.le_self_pow (by omega) g)
    exact Nat.mul_pos (by omega) (pow_pos hl.pos _)
  have hTe : ∀ e ∈ I, ((T e).card : ℝ) ≤ B := by
    intro e he
    simp only [hI, Finset.mem_filter, Finset.mem_range] at he
    obtain ⟨hed, k, hk⟩ := he
    have h2e : 2 * e ≤ δ := by
      have hk2 : 2 ≤ k := by
        by_contra hlt
        have : k = 0 ∨ k = 1 := by omega
        rcases this with rfl | rfl <;> omega
      calc 2 * e = e * 2 := by ring
        _ ≤ e * k := Nat.mul_le_mul_left e hk2
        _ = δ := hk.symm
    have hc1 : (T e).card ≤ (g ^ e - 1) * l ^ v := card_nthRootsFinset_le _
    have hc2 : ((g ^ e - 1 : ℕ) : ℝ) ≤ (g : ℝ) ^ ((δ : ℝ) / 2) := by
      have h4 : ((g ^ e - 1 : ℕ) : ℝ) ≤ (g : ℝ) ^ e := by
        have : g ^ e - 1 ≤ g ^ e := Nat.sub_le _ _
        exact_mod_cast this
      refine h4.trans ?_
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le hg1
      have : ((2 * e : ℕ) : ℝ) ≤ (δ : ℝ) := by exact_mod_cast h2e
      push_cast at this
      linarith
    calc ((T e).card : ℝ) ≤ (((g ^ e - 1) * l ^ v : ℕ) : ℝ) := by exact_mod_cast hc1
      _ = ((g ^ e - 1 : ℕ) : ℝ) * ((l ^ v : ℕ) : ℝ) := by push_cast; ring
      _ ≤ B := mul_le_mul hc2 hlv (by positivity) (by positivity)
  set F := (Finset.univ : Finset (Fin δ → K)).filter (fun c => Irreducible (monicOf c) ∧
      ¬ Set.InjOn (primeToPart l) ((monicOf c).rootSet L)) with hF
  have hFirr : ∀ c ∈ F, Irreducible (monicOf c) := fun c hc => (Finset.mem_filter.mp hc).2.1
  have hroots : ∀ c ∈ F, ∀ x : L, aeval x (monicOf c) = 0 → x ∈ I.biUnion T := by
    intro c hc x' hx'
    obtain ⟨-, hirr, hninj⟩ := Finset.mem_filter.mp hc
    have hmon := monicOf_monic c
    have hdeg : (monicOf c).natDegree = δ := monicOf_natDegree c
    have hc0 : (monicOf c).coeff 0 ≠ 0 :=
      coeff_zero_ne_zero_of_irreducible hirr (by rw [hdeg]; exact hδ)
    simp only [Set.InjOn, not_forall] at hninj
    obtain ⟨x, hx, y, hy, hxy, hne⟩ := hninj
    have hx := (mem_rootSet.mp hx).2
    have hy := (mem_rootSet.mp hy).2
    obtain ⟨i, hi⟩ := root_conj hmon hirr hx hy
    obtain ⟨j, hj⟩ := root_conj hmon hirr hx hx'
    have hxn : x ^ n = 1 := by
      have := root_pow_sub_one hirr hc0 hx
      rwa [hdeg] at this
    have hxfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn0, hxn⟩
    set z := primeToPart l x with hz
    have hzi : z ^ g ^ i = z := by
      have := (prime_to_part_endomorphism L L l x x (powMonoidHom (g ^ i)) hl hxfin hxfin).2
      simp only [powMonoidHom_apply] at this
      rw [hz, this, ← hi, ← hxy]
    have hzn : z ^ n = 1 := by
      rw [hz, primeToPart, ← pow_mul, mul_comm, pow_mul, hxn, one_pow]
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, zero_pow hn0] at hzn
      exact zero_ne_one hzn
    have hzi1 : z ^ (g ^ i - 1) = 1 := by
      have hpos : 0 < g ^ i := pow_pos (by omega) _
      have : z ^ (g ^ i - 1) * z = 1 * z := by
        rw [← pow_succ, Nat.sub_add_cancel hpos, hzi, one_mul]
      exact mul_right_cancel₀ hz0 this
    set e := Nat.gcd i δ with he
    have hze : z ^ (g ^ e - 1) = 1 := by
      rw [he, ← Nat.pow_sub_one_gcd_pow_sub_one]
      exact pow_gcd_eq_one.mpr ⟨hzi1, hzn⟩
    have heδ : e ∣ δ := Nat.gcd_dvd_right i δ
    have helt : e < δ := by
      refine lt_of_le_of_ne (Nat.le_of_dvd (by omega) heδ) ?_
      intro h
      have hdi : δ ∣ i := h ▸ Nat.gcd_dvd_left i δ
      obtain ⟨k, hk⟩ := hdi
      apply hne
      have := root_pow_card_mul hirr hx k
      rw [hdeg, ← hk, ← hi] at this
      exact this.symm
    have heI : e ∈ I := by
      simp only [hI, Finset.mem_filter, Finset.mem_range]; exact ⟨helt, heδ⟩
    obtain ⟨_, a, ha⟩ := prime_to_part_spec L l x hl hxfin
    have h1 : (x ^ (g ^ e - 1)) ^ (l ^ a) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ha, ← pow_mul, mul_comm, pow_mul, hze, one_pow]
    have h2 : (x ^ (g ^ e - 1)) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hxn, one_pow]
    have h3 := (lpow_order_iff hl hn0 _ h2).mp ⟨a, h1⟩
    rw [Finset.mem_biUnion]
    refine ⟨e, heI, ?_⟩
    rw [hT]
    simp only
    rw [mem_nthRootsFinset (hmpos e heI), hj, ← pow_mul, mul_comm, pow_mul, pow_mul, h3, one_pow]
  have hcount := mul_card_le_of_roots_mem F hFirr (I.biUnion T) hroots
  have hB0 : 0 ≤ B := by positivity
  have hIcard : (I.card : ℝ) ≤ δ := by
    have : I.card ≤ δ := (Finset.card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  have hS : ((I.biUnion T).card : ℝ) ≤ δ * B := by
    calc ((I.biUnion T).card : ℝ) ≤ ((∑ e ∈ I, (T e).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ e ∈ I, ((T e).card : ℝ) := by push_cast; rfl
      _ ≤ ∑ _e ∈ I, B := Finset.sum_le_sum hTe
      _ = (I.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ δ * B := mul_le_mul_of_nonneg_right hIcard hB0
  have hδR : (0 : ℝ) < δ := by exact_mod_cast (by omega : 0 < δ)
  have hfin : (δ : ℝ) * (F.card : ℝ) ≤ δ * B := by
    refine le_trans ?_ hS
    exact_mod_cast hcount
  have hFB : (F.card : ℝ) ≤ B := le_of_mul_le_mul_left hfin hδR
  have hBeq : B = (g : ℝ) ^ (3 * (δ : ℝ) / 4) := by
    rw [hB, ← Real.rpow_add (by linarith)]
    congr 1
    ring
  rw [← hBeq]
  exact hFB
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
