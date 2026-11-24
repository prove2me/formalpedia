-- Prove2me | solution 1 for Formalism.CountingSumsFrames.partnerM_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:50.301007+00:00
-- url     : https://prove2.me/submissions/10d3f3a4-ed9b-4de2-82d0-4a7ec71bb192

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_keep
import Theorems.Thm_Formalism_CountingSumsFrames_peel
import Theorems.Thm_Formalism_CountingSumsFrames_finrank_lattice
import Theorems.Thm_Formalism_CountingSumsFrames_pol_finiteDimensional
import Theorems.Thm_Formalism_CountingSumsFrames_codim_inf_le
import Theorems.Thm_P2M_Formalism_CountingSumsFrames_fockN_smul_right__bfa97ee757de
import Theorems.Thm_Formalism_CountingSumsFrames_y_le_thrUpTo
import Theorems.Thm_Formalism_CountingSumsFrames_phi_keeps
import Theorems.Thm_Formalism_GM_TM_lg_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
namespace Formalism.CountingSumsFrames
theorem _root_.solution (hTie : TieOps) (hYP : YPartner) : PartnerM := by
  obtain ⟨C₂, hC₂, hT⟩ := hTie
  obtain ⟨C₃, hC₃, hY⟩ := hYP
  refine ⟨max 1 (max C₂ C₃), le_max_left _ _, ?_⟩
  intro C hC p _ N r _ _ LL T a E κ n ρ h2p hr hρ hadm hE hS hdeg hz hκ hHP hHW hL4 nb f U V dg fw h1 h2 h3
  have hops := hT p N r LL T a E κ n ρ h2p hr hρ hadm hE hS hdeg hz hκ hHP hHW hL4 nb f U V dg fw h1 h2 h3
  choose Tm πm Kf hK hTY hTint hadj hcomm hrank using hops
  have hadm' : T.Admissible (LL.setTies T n) := hadm
  set LL' := LL.setTies T n with hLL'
  set Ysp : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) := Y p (r := r) LL' T.J T.thr with hYsp
  set W : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
    Ysp ⊓ (Finset.univ : Finset (Fin T.t)).inf (fun i => LinearMap.ker (πm i - LinearMap.id)) with hW
  have hYpol : Ysp ≤ Pol p r LL' := inf_le_left
  have hWY : W ≤ Ysp := inf_le_left
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlg := lg_nonneg p a r hr
  have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ
  have hCC₂ : C₂ ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hCC₃ : C₃ ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have hsat : ∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), c ≠ 0 →
      x ∈ YZ p (r := r) LL' T.J T.thr → c • x ∈ W.restrictScalars ℤ_[p] ⊓ PolZ p r LL' →
      x ∈ W.restrictScalars ℤ_[p] ⊓ PolZ p r LL' := by
    intro c x hc hx hcx
    refine Submodule.mem_inf.mpr ⟨?_, (Submodule.mem_inf.mp hx).2⟩
    have hxY : x ∈ Ysp := (Submodule.mem_inf.mp hx).1
    have hcW : c • x ∈ W := (Submodule.mem_inf.mp hcx).1
    show x ∈ W
    refine Submodule.mem_inf.mpr ⟨hxY, ?_⟩
    rw [Submodule.mem_finsetInf]
    intro i _
    have hci := (Submodule.mem_finsetInf.mp (Submodule.mem_inf.mp hcW).2) i (Finset.mem_univ i)
    rw [LinearMap.mem_ker] at hci ⊢
    rw [← algebraMap_smul ℚ_[p] c x, map_smul, smul_eq_zero] at hci
    rcases hci with h | h
    · exact absurd (PadicInt.ext (h.trans PadicInt.coe_zero.symm)) hc
    · exact h
  have hL1Y : W.restrictScalars ℤ_[p] ⊓ PolZ p r LL' ≤ YZ p (r := r) LL' T.J T.thr :=
    inf_le_inf_right (PolZ p r LL') (show W.restrictScalars ℤ_[p] ≤ Ysp.restrictScalars ℤ_[p] from fun x hx => hWY hx)
  refine ⟨W.restrictScalars ℤ_[p] ⊓ PolZ p r LL', hL1Y, hsat, ?_, ?_⟩
  ·
    intro u hu hprim
    have huY : u ∈ YZ p (r := r) LL' T.J T.thr := hL1Y hu
    have hprimY : ∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), x ∈ YZ p (r := r) LL' T.J T.thr →
        u = c • x → IsUnit c := by
      intro c x hx hux
      by_cases hc : c = 0
      · exfalso
        have hu0 : u = 0 := by rw [hux, hc, zero_smul]
        have := hprim 0 0 (Submodule.zero_mem _) (by rw [hu0, smul_zero])
        exact not_isUnit_zero this
      · exact hprim c x (hsat c x hc hx (hux ▸ hu)) hux
    obtain ⟨z'', hz'', K₀, hK₀, hnorm⟩ := hY p N r LL' T.J T.thr ρ a κ hr hκ hHP u huY hprimY
    set e := ⌊E⌋₊ with he
    let Ts : Fin T.t → MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
      fun i => ((p : ℚ_[p]) ^ (Kf i)) • Tm i
    have hTsZ : ∀ i, ∀ y ∈ YZ p (r := r) LL' T.J T.thr, Ts i y ∈ YZ p (r := r) LL' T.J T.thr := by
      intro i y hy
      have hyY : y ∈ Ysp := (Submodule.mem_inf.mp hy).1
      have h1 : Ts i y ∈ Ysp := Ysp.smul_mem _ (hTY i y hyY)
      exact Submodule.mem_inf.mpr ⟨h1, Submodule.mem_inf.mpr ⟨hYpol h1, hTint i y hy⟩⟩
    have hTsY : ∀ i, ∀ y ∈ (Ysp : Set (MvPolynomial (Fin N × Fin r) ℚ_[p])), Ts i y ∈ Ysp :=
      fun i y hy => Ysp.smul_mem _ (hTY i y hy)
    set u' := lcomp Ts (List.finRange T.t) z'' with hu'
    have hu'Z : u' ∈ YZ p (r := r) LL' T.J T.thr :=
      lcomp_keep Ts (YZ p (r := r) LL' T.J T.thr : Set _) (List.finRange T.t) (fun j _ => hTsZ j) z'' hz''
    refine ⟨u', hu'Z, ?_⟩
    have hfix : ∀ i ∈ List.finRange T.t, πm i u = u := by
      intro i _
      have huW : u ∈ W := (Submodule.mem_inf.mp hu).1
      have := (Submodule.mem_finsetInf.mp (Submodule.mem_inf.mp huW).2) i (Finset.mem_univ i)
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
      exact this
    have hpeel := peel (fockN p LL') (T.phi p LL') Ts πm (fun i => (p : ℚ_[p]) ^ (Kf i + e))
      (fun i => (Y p (r := r) LL' T.J (T.thrUpTo i) : Set (MvPolynomial (Fin N × Fin r) ℚ_[p])))
      (Ysp : Set (MvPolynomial (Fin N × Fin r) ℚ_[p]))
      (fun i => fun x hx => y_le_thrUpTo LL' T i hx) hTsY
      (fun i j hij => phi_keeps LL' T hadm' i j hij)
      (fun i j hij => hcomm i j hij)
      (fun i u hu u' hu' => by
        show fockN p LL' (T.phi p LL' i u) (((p : ℚ_[p]) ^ (Kf i)) • Tm i u') = _
        rw [fockN_smul_right', hadj i u hu u' hu', pow_add]; ring)
      (List.finRange T.t) (List.pairwise_lt_finRange T.t) u (hWY (Submodule.mem_inf.mp hu).1) hfix z''
      (Submodule.mem_inf.mp hz'').1
    have hphis : T.phis p (r := r) LL' = lcomp (T.phi p (r := r) LL') (List.finRange T.t) := rfl
    rw [hphis, hpeel]
    have hS' : (∑ i, ((Kf i + e : ℕ) : ℝ)) ≤ (T.t : ℝ) * (E + C * κ) := by
      have hb : ∀ i, ((Kf i + e : ℕ) : ℝ) ≤ E + C * κ := by
        intro i; push_cast
        have h1 := hK i
        have h2 : (e : ℝ) ≤ E := Nat.floor_le (by linarith)
        have h3 : C₂ * κ ≤ C * κ := mul_le_mul_of_nonneg_right hCC₂ hκ0
        linarith
      calc (∑ i, ((Kf i + e : ℕ) : ℝ)) ≤ ∑ _i : Fin T.t, (E + C * κ) := Finset.sum_le_sum fun i _ => hb i
        _ = (T.t : ℝ) * (E + C * κ) := by simp; ring
    have hK0' : (K₀ : ℝ) ≤ C * κ := hK₀.trans (mul_le_mul_of_nonneg_right hCC₃ hκ0)
    have hD : (((∑ i, (Kf i + e)) + K₀ : ℕ) : ℤ) ≤ ⌊(T.t : ℝ) * (E + C * κ) + C * κ⌋ := by
      apply Int.le_floor.mpr
      have : (((∑ i, (Kf i + e)) + K₀ : ℕ) : ℝ) = (∑ i, ((Kf i + e : ℕ) : ℝ)) + K₀ := by push_cast; rfl
      rw [Int.cast_natCast, this]
      linarith
    have hprod : ((List.finRange T.t).map (fun i => (p : ℚ_[p]) ^ (Kf i + e))).prod =
        (p : ℚ_[p]) ^ (∑ i, (Kf i + e)) := by
      rw [← Fin.prod_univ_def, Finset.prod_pow_eq_pow_sum]
    rw [hprod, norm_mul, norm_pow, Padic.norm_p]
    calc (p : ℝ) ^ (-⌊(T.t : ℝ) * (E + C * κ) + C * κ⌋)
        ≤ (p : ℝ) ^ (-((((∑ i, (Kf i + e)) + K₀ : ℕ)) : ℤ)) := zpow_le_zpow_right₀ hp1.le (by omega)
      _ = (p : ℝ)⁻¹ ^ (∑ i, (Kf i + e)) * (p : ℝ) ^ (-(K₀ : ℤ)) := by
        rw [Nat.cast_add, neg_add, zpow_add₀ (ne_of_gt hp0), zpow_neg, zpow_natCast, inv_pow]
      _ ≤ (p : ℝ)⁻¹ ^ (∑ i, (Kf i + e)) * ‖fockN p LL' u z''‖ :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
  ·
    haveI := pol_finiteDimensional (p := p) (r := r) LL'
    haveI : FiniteDimensional ℚ_[p] Ysp := Submodule.finiteDimensional_of_le hYpol
    have e1 : Module.finrank ℤ_[p] (YZ p (r := r) LL' T.J T.thr) = Module.finrank ℚ_[p] Ysp :=
      finrank_lattice LL' Ysp hYpol
    have e2 : Module.finrank ℤ_[p] (W.restrictScalars ℤ_[p] ⊓ PolZ p r LL' : Submodule ℤ_[p] _) =
        Module.finrank ℚ_[p] W := finrank_lattice LL' W (hWY.trans hYpol)
    rw [e1, e2]
    have hc := codim_inf_le Ysp (fun i => LinearMap.ker (πm i - LinearMap.id)) univ
    refine (Nat.cast_le.mpr hc).trans ?_
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum fun i _ => hrank i
end Formalism.CountingSumsFrames
