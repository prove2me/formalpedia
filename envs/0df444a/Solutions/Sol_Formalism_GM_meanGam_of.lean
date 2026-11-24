-- Prove2me | solution 1 for Formalism.GM.meanGam_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:42:32.203066+00:00
-- url     : https://prove2.me/submissions/c65509e7-c2c3-4af6-b744-fb72697fe5a7

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_binMatK_map
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_nlog_le
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_per_row
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_split_det
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_splits_form
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_betaT_ne_zero
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_lead_part
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_lead_bound
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.GM
open Polynomial Finset Formalism.GM.M Formalism.GM.MeanGammaLemmas
namespace Formalism.GM
theorem _root_.solution (hDeg : GamDeg) (hLead : GamLead) (hInt : GamInt) (hW : Formalism.GM.WindowFullAP) :
    MeanGam := by
  obtain ⟨C, hC⟩ := hInt
  refine ⟨(C : ℝ) + 3, by positivity, ?_⟩
  intro p hp K r hr LLw q J M ρ z w n₀ f ord s d Yw a E κ U V dg hρ hr2 hv hli hspan hord hfil hE hYw hd
    hcop hSs hdeg hsY hz hκ hL4 hsmith
  classical
  have hr1 : 1 ≤ r := by omega
  have hmem : ∀ b, f b ∈ MMwZ p LLw J M ρ w := fun b => hspan ▸ Submodule.subset_span ⟨b, rfl⟩
  have hPol : ∀ b, f b ∈ Pol p r LLw := fun b =>
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp
      (Submodule.mem_inf.mp (hmem b)).1).1).1).1
  have hPolZ : ∀ b, f b ∈ PolZ p r LLw := fun b =>
    Submodule.mem_inf.mpr ⟨hPol b, (Submodule.mem_inf.mp (hmem b)).2⟩
  have hCI := fun x y => hC p K r LLw ρ z (f x) (f y) hr1 hv (hPolZ x) (hPolZ y)
  choose cc hcc using hCI
  set S := LLw.total with hSdef
  set o := LLw.deg (Fin.last K) with hodef
  set cI := C * (K + 3) * r ^ 2 * (Nat.log p (S + o + r) + 1) with hcIdef
  obtain ⟨hAeval, hnat, hlead, hord_le, hoS⟩ := lead_part hDeg hLead LLw J M ρ z w n₀ f ord κ ⌈κ⌉₊ cI cc
    hr1 hv hli hspan hord hfil hL4 (fun x y n hn => hcc x y n hn)
  set Aq := binMatK ℚ_[p] (2 * S) (coefT p (S + o) ⌈κ⌉₊ cc) with hAqdef

  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hlg0 : 0 ≤ Real.logb p (8 * a + r) := by
    apply Real.logb_nonneg hp1
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr2
    have : (0 : ℝ) ≤ a := by positivity
    linarith
  have hlgdef : lgV2 p a r = Real.logb p (8 * a + r) + 1 := rfl
  have h12 : (12 : ℝ) ≤ ((K : ℝ) + 3) * (r : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr2
    have : (0 : ℝ) ≤ K := by positivity
    nlinarith
  have hκ12 : 12 * (Real.logb p (8 * a + r) + 1) ≤ κ := by
    rw [hlgdef] at hκ
    nlinarith
  have hκ0 : 0 ≤ κ := by linarith
  have hS2a : S ≤ 2 * a := le_trans hSs (le_trans (Nat.le_add_right _ _) hsY)
  have ho2a : o ≤ 2 * a := hdeg _
  have hcI : (cI : ℝ) ≤ C * κ := by
    have hl := nlog_le p (S + o + r) (8 * a + r) (by omega)
    have hcast : (((8 * a + r : ℕ)) : ℝ) = 8 * (a : ℝ) + r := by push_cast; ring
    rw [hcast] at hl
    have hC0 : (0 : ℝ) ≤ C := by positivity
    have hK0 : (0 : ℝ) ≤ ((K : ℝ) + 3) * (r : ℝ) ^ 2 := by positivity
    calc (cI : ℝ) = (C : ℝ) * ((((K : ℝ) + 3) * (r : ℝ) ^ 2) * ((Nat.log p (S + o + r) : ℝ) + 1)) := by
          rw [hcIdef]; push_cast; ring
      _ ≤ (C : ℝ) * ((((K : ℝ) + 3) * (r : ℝ) ^ 2) * lgV2 p a r) := by
          rw [hlgdef]; gcongr
      _ ≤ C * κ := by gcongr
  have hLB := lead_bound p (fun b => ‖betaT p (⌈κ⌉₊ + cI) z o S (ord b)‖) (fun b => S + o - ord b) κ
    ((C + 3) * κ) ‖Aq.det.leadingCoeff‖ (fun b => norm_pos_iff.mpr (betaT_ne_zero p _ _ _ _ _)) hlead
    (fun b => per_row p a r S o z (ord b) cI κ C (hord_le b) ho2a hS2a hz hr1 hκ12 hcI)

  set alg := algebraMap ℚ_[p] (PadicAlgCl p) with halg
  set c' : Fin n₀ → Fin n₀ → ℕ → PadicAlgCl p := fun i j k => alg (coefT p (S + o) ⌈κ⌉₊ cc i j k) with hc'
  have hAK : binMatK (PadicAlgCl p) (2 * S) c' = Aq.map (Polynomial.map alg) :=
    binMatK_map ℚ_[p] (PadicAlgCl p) alg (2 * S) _
  have hDk : (binMatK (PadicAlgCl p) (2 * S) c').det = Aq.det.map alg := by
    rw [hAK]; exact split_det p Aq
  obtain ⟨hsplit, hcard⟩ := splits_form (binMatK (PadicAlgCl p) (2 * S) c').det
  have hlc : (binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff = alg Aq.det.leadingCoeff := by
    rw [hDk, leadingCoeff_map]
  have hnd : (binMatK (PadicAlgCl p) (2 * S) c').det.natDegree = Aq.det.natDegree := by
    rw [hDk, natDegree_map]
  have hlcnorm : ‖(binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff‖ = ‖Aq.det.leadingCoeff‖ := by
    rw [hlc, halg, norm_algebraMap']
  have hprod_pos : 0 < ∏ b, (‖betaT p (⌈κ⌉₊ + cI) z o S (ord b)‖ * (p : ℝ) ^ (-κ)) := by
    apply Finset.prod_pos
    intro b _
    exact mul_pos (norm_pos_iff.mpr (betaT_ne_zero p _ _ _ _ _)) (Real.rpow_pos_of_pos (by linarith) _)
  have hleadne : (binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff ≠ 0 := by
    rw [← norm_pos_iff, hlcnorm]; exact lt_of_lt_of_le hprod_pos hlead
  have hLB' : -Real.logb p ‖(binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff‖ +
      ((binMatK (PadicAlgCl p) (2 * S) c').det.roots.card : ℝ) / ((p : ℝ) - 1) ≤ (n₀ : ℝ) * ((C + 3) * κ) := by
    rw [hlcnorm, hcard, hnd, hnat]; exact hLB
  have hc'norm : ∀ i j k, ‖c' i j k‖ ≤ 1 := by
    intro i j k
    simp only [hc', halg, norm_algebraMap', coefT]
    split_ifs
    · rw [norm_mul, norm_pow, Padic.norm_p]
      have h1 : ‖((cc i j k : ℤ_[p]) : ℚ_[p])‖ ≤ 1 := by
        rw [← PadicInt.norm_def]; exact PadicInt.norm_le_one _
      have h2 : ((p : ℝ)⁻¹) ^ ⌈κ⌉₊ ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hp1.le)
      calc ((p : ℝ)⁻¹) ^ ⌈κ⌉₊ * ‖((cc i j k : ℤ_[p]) : ℚ_[p])‖ ≤ 1 * 1 :=
            mul_le_mul h2 h1 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · simp

  set h := Nat.clog p (8 * a + r) with hhdef
  have hph : 8 * a + r ≤ p ^ h := Nat.le_pow_clog hp.out.one_lt _
  have hhl : (h : ℝ) ≤ lgV2 p a r := by
    rw [hlgdef]
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · rw [h0]; push_cast; linarith
    · have h1 := Nat.pow_pred_clog_lt_self hp.out.one_lt (x := 8 * a + r) (by omega)
      rw [← hhdef, Nat.pred_eq_sub_one] at h1
      have h2 : h - 1 ≤ Nat.log p (8 * a + r) := Nat.le_log_of_pow_le hp.out.one_lt h1.le
      have h3 := nlog_le p (8 * a + r) (8 * a + r) le_rfl
      have hcast : (((8 * a + r : ℕ)) : ℝ) = 8 * (a : ℝ) + r := by push_cast; ring
      rw [hcast] at h3
      have h4 : ((h - 1 : ℕ) : ℝ) ≤ (Nat.log p (8 * a + r) : ℝ) := by exact_mod_cast h2
      have h5 : (h : ℝ) = ((h - 1 : ℕ) : ℝ) + 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      linarith
  have hYle : Yw ≤ 2 * a + 1 := by
    have h1 := Nat.le_mul_of_pos_left (Yw - 1) hd
    have h2 : d * (Yw - 1) ≤ 2 * a := le_trans (Nat.le_add_left _ _) hsY
    omega
  have hYh : Yw ≤ p ^ h := by omega
  have hdelh : 2 * S ≤ p ^ h := by omega

  set idx : ℤ → ℕ := fun t => ((t - (s : ℤ)) / (d : ℤ)).toNat with hidxdef
  have hidx : ∀ j : ℕ, idx (progr (s : ℤ) (d : ℤ) j) = j := by
    intro j
    simp only [hidxdef, progr, add_sub_cancel_left]
    rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hd.ne')]
    simp
  set U' : ℤ → Matrix (Fin n₀) (Fin n₀) (PadicAlgCl p) := fun t => (U (idx t)).map alg with hU'
  set V' : ℤ → Matrix (Fin n₀) (Fin n₀) (PadicAlgCl p) := fun t => (V (idx t)).map alg with hV'
  set dg' : ℤ → Fin n₀ → PadicAlgCl p := fun t b => alg ((p : ℚ_[p]) ^ cI * dg (idx t) b) with hdg'
  have hsm : ∀ j ∈ range Yw, (∀ x y, ‖U' (progr (s : ℤ) (d : ℤ) j) x y‖ ≤ 1) ∧
      (∀ x y, ‖V' (progr (s : ℤ) (d : ℤ) j) x y‖ ≤ 1) ∧
      ‖(U' (progr (s : ℤ) (d : ℤ) j)).det‖ = 1 ∧ ‖(V' (progr (s : ℤ) (d : ℤ) j)).det‖ = 1 ∧
      (binMatK (PadicAlgCl p) (2 * S) c').map (Polynomial.eval ((progr (s : ℤ) (d : ℤ) j : ℤ) : PadicAlgCl p)) =
        U' (progr (s : ℤ) (d : ℤ) j) * Matrix.diagonal (dg' (progr (s : ℤ) (d : ℤ) j)) *
          V' (progr (s : ℤ) (d : ℤ) j) := by
    intro j hj
    obtain ⟨hU1, hV1, hUd, hVd, hfac⟩ := hsmith j (Finset.mem_range.mp hj)
    simp only [hU', hV', hdg', hidx]
    refine ⟨fun x y => ?_, fun x y => ?_, ?_, ?_, ?_⟩
    · rw [Matrix.map_apply, halg, norm_algebraMap']; exact hU1 x y
    · rw [Matrix.map_apply, halg, norm_algebraMap']; exact hV1 x y
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, halg, norm_algebraMap']; exact hUd
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, halg, norm_algebraMap']; exact hVd
    · rw [hAK]
      ext x y
      have hpt : ((progr (s : ℤ) (d : ℤ) j : ℤ) : PadicAlgCl p) = ((s + d * j : ℕ) : PadicAlgCl p) := by
        simp [progr]
      have hfe := congrFun (congrFun hfac x) y
      simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.mul_diagonal] at hfe
      simp only [Matrix.map_apply, hpt, eval_natCast_map, Matrix.mul_apply, Matrix.mul_diagonal]
      rw [hAeval x y (s + d * j) (le_trans hSs (Nat.le_add_right _ _)), pow_add, mul_comm ((p : ℚ_[p]) ^ ⌈κ⌉₊),
        mul_assoc, hfe, Finset.mul_sum, map_sum]
      apply Finset.sum_congr rfl
      intro b _
      simp [Matrix.diagonal_apply, map_sum]
      ring
  have hcop' : IsCoprime (d : ℤ) (p : ℤ) := hcop
  have hE0 : (0 : ℝ) < E := by linarith
  have key := hW p (PadicAlgCl p) n₀ (2 * S) h E c' (binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff
    (binMatK (PadicAlgCl p) (2 * S) c').det.roots (s : ℤ) (d : ℤ) Yw ((C + 3) * κ) U' V' dg' hcop'
    (by omega) hYh hdelh hE0 hleadne hc'norm hsplit hsm hLB'

  have hcnt : ∀ j ∈ range Yw, ((univ.filter (fun b => ‖dg j b‖ < (p : ℝ) ^ (-E))).card : ℝ) ≤
      ((univ.filter (fun b => ‖dg' (progr (s : ℤ) (d : ℤ) j) b‖ ≤ (p : ℝ) ^ (-E))).card : ℝ) := by
    intro j _
    have hsub : univ.filter (fun b => ‖dg j b‖ < (p : ℝ) ^ (-E)) ⊆
        univ.filter (fun b => ‖dg' (progr (s : ℤ) (d : ℤ) j) b‖ ≤ (p : ℝ) ^ (-E)) := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      simp only [hdg', hidx, halg, norm_algebraMap', norm_mul, norm_pow, Padic.norm_p]
      have h2 : ((p : ℝ)⁻¹) ^ cI ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hp1.le)
      calc ((p : ℝ)⁻¹) ^ cI * ‖dg j b‖ ≤ 1 * ‖dg j b‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ ≤ (p : ℝ) ^ (-E) := by rw [one_mul]; exact hb.le
    exact_mod_cast Finset.card_le_card hsub
  have hYpos : (0 : ℝ) < Yw := by exact_mod_cast hYw
  calc (∑ j ∈ range Yw, ((univ.filter (fun b => ‖dg j b‖ < (p : ℝ) ^ (-E))).card : ℝ)) / Yw
      ≤ (∑ j ∈ range Yw, ((univ.filter (fun b => ‖dg' (progr (s : ℤ) (d : ℤ) j) b‖ ≤ (p : ℝ) ^ (-E))).card : ℝ)) /
          Yw := div_le_div_of_nonneg_right (Finset.sum_le_sum hcnt) hYpos.le
    _ ≤ (n₀ : ℝ) * (((2 * S : ℕ) : ℝ) / Yw + ((C + 3) * κ + ((2 * S : ℕ) : ℝ) * h / Yw) / E) := key
    _ ≤ n₀ * (2 * (LLw.total : ℝ) / Yw + (((C : ℝ) + 3) * κ + 2 * (LLw.total : ℝ) * lgV2 p a r / Yw) / E) := by
      rw [← hSdef]
      push_cast
      have h1 : 2 * (S : ℝ) * h / Yw ≤ 2 * (S : ℝ) * lgV2 p a r / Yw := by
        apply div_le_div_of_nonneg_right _ hYpos.le
        exact mul_le_mul_of_nonneg_left hhl (by positivity)
      have h2 : ((C : ℝ) + 3) * κ + 2 * (S : ℝ) * h / Yw ≤ ((C : ℝ) + 3) * κ + 2 * (S : ℝ) * lgV2 p a r / Yw := by
        linarith
      have h3 := div_le_div_of_nonneg_right h2 hE0.le
      have hn0 : (0 : ℝ) ≤ n₀ := by positivity
      nlinarith
end Formalism.GM
