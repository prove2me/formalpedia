-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.nonstationary_estimate_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:33.124227+00:00
-- url     : https://prove2.me/submissions/b82bff91-3629-4d66-b898-85f1a4366e86

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_K_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_one_le_tau
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_continuous_farCut
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_integrable_cut_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_abs_nonstationaryCutoff_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_inner_osc
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_muPi_closedBall
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_mem_rootSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_isOpen_Om
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_isClosed_Fs
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_Fs_subset_ball
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_Fs_subset_Om
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_differentiableOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_vpow
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_rpow_decay_arith
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_card_UT
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_phase_bounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_arith

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
noncomputable section
set_option maxHeartbeats 1000000
namespace Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
namespace _root_.Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.NonStatStepOfParts := by
  intro hNS hGL _hGD hRel _hCC hAF hOm hCut hIn
  obtain ⟨C₉, hAF⟩ := hAF
  refine ⟨2 * (C₉ + 1), 3, by positivity, ?_⟩
  intro m β hβ Kc hKc h0 δ ε hδ hε hεle
  have hs : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hC9 : (0 : ℝ) ≤ (C₉ : ℝ) := Nat.cast_nonneg _
  have hkey : ε * (((m : ℝ) + 2) * ((C₉ : ℝ) + 1)) ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity)] at hεle
    push_cast at hεle
    nlinarith
  have he0 : 0 ≤ ε * ((m : ℝ) + 2) := by positivity
  have hε2s : ε * ((m : ℝ) + 2) ≤ 1 / 2 := by nlinarith
  have hε2 : ε ≤ 1 / (2 * ((m : ℝ) + 2)) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = 4 * m + 12 := ⟨_, rfl⟩
  obtain ⟨Cst, t₁, c₀, ht₁, hc₀, hAmp⟩ := hAF m β Kc hKc h0 δ ε hδ hε hε2 q
  have hKc' : IsCompact ((fun D : ℂ => (-1) ^ (m + 3) * D) '' Kc) := hKc.image (by fun_prop)
  have h0' : (0 : ℂ) ∉ (fun D : ℂ => (-1) ^ (m + 3) * D) '' Kc := by
    rintro ⟨D, hD, hD0⟩
    rcases mul_eq_zero.mp hD0 with h | h
    · exact absurd h (pow_ne_zero _ (by norm_num))
    · exact h0 (h ▸ hD)
  obtain ⟨cg, hcg, hGrad⟩ := hGL m _ hKc' h0' (δ / 2) (half_pos hδ.1)
  obtain ⟨CN, hCN⟩ := hNS (m + 1) q β hβ
  obtain ⟨hRel1, hRel2⟩ := hRel m
  choose! Cj hCj using hRel2
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 1 + (∑ i ∈ Finset.range (q + 1), |Cj i|) * (1 + 1 / cg) := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by
    have h1 : 0 ≤ ∑ i ∈ Finset.range (q + 1), |Cj i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have : 0 ≤ (∑ i ∈ Finset.range (q + 1), |Cj i|) * (1 + 1 / cg) := by positivity
    linarith
  obtain ⟨Cp, hCp⟩ : ∃ Cp : ℝ, Cp = 2 * M / c₀ + 1 := ⟨_, rfl⟩
  have hCp1 : 1 ≤ Cp := by
    have : 0 ≤ 2 * M / c₀ := by positivity
    linarith
  obtain ⟨ny, hny⟩ : ∃ ny : ℕ, ny = Fintype.card (UT (m + 2)) := ⟨_, rfl⟩
  refine ⟨|CN| * |Cst| * (Cp / cg) ^ q * (‖β‖ / 2 * 4) ^ (m + 1) * (‖β‖ / 2 * 4) ^ ny, min t₁ 1,
    lt_min ht₁ one_pos, ?_⟩
  intro V _ _ _ Φ A K k hA hk hΦ t c ht htle hD
  have ht1 : ‖t‖ ≤ 1 := htle.trans (min_le_right _ _)
  have htt : ‖t‖ ≤ t₁ := htle.trans (min_le_left _ _)
  have hτ : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hK : 0 ≤ K := K_nonneg hD hΦ
  have hA0 : 0 ≤ A := by
    have : 0 ≤ ((m : ℝ) + 1) * ((m : ℝ) + 4) := by positivity
    linarith
  have hqk : q ≤ k := by
    have : 4 * m + 12 ≤ 3 * (m + 2) ^ 2 := by nlinarith
    omega
  obtain ⟨_, _, hint, _⟩ := inner_osc (β := β) hOm hCut hIn h0 (by linarith) hε.le hΦ ht ht1 hD
  obtain ⟨D, hDdef⟩ : ∃ D : ℂ, D = c * t ^ (m + 1) := ⟨_, rfl⟩
  rw [← hDdef] at hD hint ⊢
  have hAmp' := hAmp V Φ A K k hA0 hqk hΦ t D ht htt hD
  obtain ⟨D', hD'⟩ : ∃ D' : ℂ, D' = (-1) ^ (m + 3) * D := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ, v = ‖t‖ ^ (-ε) := ⟨_, rfl⟩
  have hv : 1 ≤ v := hvdef ▸ one_le_tau ht ht1 hε.le
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = v ^ (m + 2) := ⟨_, rfl⟩
  have hw : 1 ≤ w := hwdef ▸ one_le_pow₀ hv
  have hw0 : 0 < w := by linarith
  have hv0 : 0 < v := by linarith
  have hrw : ‖t‖ ^ (((m : ℝ) + 2) * ε) = w⁻¹ := by
    rw [hwdef, hvdef, ← Real.rpow_mul_natCast hτ.le, ← Real.rpow_neg hτ.le]
    congr 1; push_cast; ring
  have hintF := integrable_cut_smul hint (continuous_farCut m δ D) (abs_nonstationaryCutoff_le m δ D)
  have hFub : ∫ p : XY m, ((farCut m δ D p.1 : ℝ) : ℂ) • oscIn β m ε Φ D t p ∂(muXY β m) =
      ∫ y : UT (m + 2) → ℂ, ∫ x : Fin (m + 1) → ℂ, psi β (g0 D' x / t) •
        (((farCut m δ D x : ℝ) : ℂ) • ampIn β m ε Φ D t (x, y)) ∂(muPi β (Fin (m + 1)))
        ∂(muPi β (UT (m + 2))) := by
    unfold muXY at hintF ⊢
    rw [integral_prod_symm _ hintF]
    congr 1; funext y; congr 1; funext x
    simp only [oscIn]
    rw [smul_comm, hD']
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = |Cst| * K * w ^ C₉ := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = Cp * w ^ (C₉ + 1) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = c₀ * w⁻¹ := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hP0 : 0 < P := by rw [hP]; positivity
  have hr0 : 0 < r := by rw [hr]; positivity
  obtain ⟨Bd, hBd⟩ : ∃ Bd : ℝ,
    Bd = |CN| * S * (‖t‖ * P / cg) ^ q * (‖β‖ / 2 * (2 * v) ^ 2) ^ (m + 1) := ⟨_, rfl⟩
  have hdg : ∀ x ∈ ns_Om m D' (r / 2) (δ / 2), cg ≤ ‖dg0 D' x‖ := by
    intro x hx
    have hne : ∀ k, x k ≠ 0 := fun k => norm_pos_iff.mp ((half_pos hr0).trans (hx.1 k))
    obtain ⟨k, hk⟩ := hGrad D' ⟨D, hD, hD'.symm⟩ x hne
      (fun z hz => (hx.2 z ((ns_mem_rootSet (by omega) _ _).mpr hz)).le)
    exact hk.trans (norm_le_pi_norm _ k)
  have hgrad : ∀ x ∈ ns_Om m D' (r / 2) (δ / 2), cg ≤ ‖fderiv ℂ (g0 D') x‖ := by
    intro x hx
    have hne : ∀ k, x k ≠ 0 := fun k => norm_pos_iff.mp ((half_pos hr0).trans (hx.1 k))
    exact (hdg x hx).trans (hRel1 D' x hne).1
  have hMP : M / (r / 2) ≤ P := by
    have e1 : M / (r / 2) = 2 * M / c₀ * w := by rw [hr]; field_simp
    rw [e1, hP]
    apply mul_le_mul (by linarith) _ hw0.le (by linarith)
    calc w = w ^ 1 := (pow_one w).symm
      _ ≤ w ^ (C₉ + 1) := pow_le_pow_right₀ hw (by omega)
  have hrelP : ∀ x ∈ ns_Om m D' (r / 2) (δ / 2), ∀ j : ℕ, 1 ≤ j → j ≤ q →
      ‖iteratedFDeriv ℂ (j + 1) (g0 D') x‖ ≤ ‖fderiv ℂ (g0 D') x‖ * P ^ j := by
    intro x hx j hj1 hjq
    have h1 := ns_phase_bounds m q hRel1 Cj hCj hcg (half_pos hr0) (fun k => (hx.1 k).le) (hdg x hx) hj1 hjq
    rw [← hM] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact pow_le_pow_left₀ (by positivity) hMP j
  have hwP : w ^ C₉ ≤ P := by
    rw [hP]
    calc w ^ C₉ = 1 * w ^ C₉ := (one_mul _).symm
      _ ≤ Cp * w ^ (C₉ + 1) :=
        mul_le_mul hCp1 (pow_le_pow_right₀ hw (by omega)) (by positivity) (by linarith)
  have hslice : ∀ y : UT (m + 2) → ℂ, ‖∫ x : Fin (m + 1) → ℂ, psi β (g0 D' x / t) •
        (((farCut m δ D x : ℝ) : ℂ) • ampIn β m ε Φ D t (x, y)) ∂(muPi β (Fin (m + 1)))‖ ≤
      (Metric.closedBall (0 : UT (m + 2) → ℂ) (2 * v)).indicator (fun _ => Bd) y := by
    intro y
    obtain ⟨hcd, hsupp, hder⟩ := hAmp' y
    rw [← hvdef] at hsupp
    by_cases hy : ‖y‖ ≤ 2 * v
    · rw [Set.indicator_of_mem (mem_closedBall_zero_iff.mpr hy)]
      have hsub : Function.support (fun x : Fin (m + 1) → ℂ =>
          ((farCut m δ D x : ℝ) : ℂ) • ampIn β m ε Φ D t (x, y)) ⊆ ns_Fs m D' (2 * v) r δ := by
        intro x hx
        obtain ⟨_, h2, h3⟩ := hsupp x hx
        refine ⟨fun k => ⟨(h2 k).1, ?_⟩, fun z hz => h3 z ?_⟩
        · have h4 := (h2 k).2
          rwa [hrw, ← hr] at h4
        · rw [← hD']; exact (ns_mem_rootSet (by omega) _ _).mp hz
      have hts := closure_minimal hsub (ns_isClosed_Fs m D' (2 * v) r δ)
      have hball := hts.trans (ns_Fs_subset_ball m D' (2 * v) r δ (by positivity))
      have hcs : HasCompactSupport (fun x : Fin (m + 1) → ℂ =>
          ((farCut m δ D x : ℝ) : ℂ) • ampIn β m ε Φ D t (x, y)) :=
        (isCompact_closedBall 0 (2 * v)).of_isClosed_subset (isClosed_tsupport _) hball
      have hΩ := hts.trans (ns_Fs_subset_Om m D' (R := 2 * v) (half_lt_self hr0) (half_lt_self hδ.1))
      have hderP : ∀ j ≤ q, ∀ x : Fin (m + 1) → ℂ, ‖iteratedFDeriv ℝ j (fun x : Fin (m + 1) → ℂ =>
          ((farCut m δ D x : ℝ) : ℂ) • ampIn β m ε Φ D t (x, y)) x‖ ≤ S * P ^ j := by
        intro j hj x
        have h1 := hder j hj x
        rw [ns_vpow hτ.le ((m + 2) * (C₉ * (j + 1))) (by push_cast; ring), ← hvdef, pow_mul, ← hwdef] at h1
        calc _ ≤ Cst * K * w ^ (C₉ * (j + 1)) := h1
          _ ≤ |Cst| * K * w ^ (C₉ * (j + 1)) := by gcongr; exact le_abs_self _
          _ = S * (w ^ C₉) ^ j := by rw [hS]; ring
          _ ≤ S * P ^ j := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hwP j) hS0
      have hmain := hCN (ns_Om m D' (r / 2) (δ / 2)) (g0 D') cg P S (ns_isOpen_Om _ _ _ _)
        (ns_differentiableOn m D' (half_pos hr0).le) hcg hP0 hgrad hrelP V _ hcd hcs hΩ hderP t ht
      have hvol : (muPi β (Fin (m + 1)) (tsupport (fun x : Fin (m + 1) → ℂ =>
          ((farCut m δ D x : ℝ) : ℂ) • ampIn β m ε Φ D t (x, y)))).toReal ≤
          (‖β‖ / 2 * (2 * v) ^ 2) ^ (m + 1) := by
        have h1 := measure_mono (μ := muPi β (Fin (m + 1))) hball
        rw [ns_muPi_closedBall β _ _ (by positivity)] at h1
        have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
        rw [ENNReal.toReal_ofReal (by positivity), Fintype.card_fin] at h2
        exact h2
      refine hmain.trans ?_
      rw [hBd]
      have hX : 0 ≤ (‖t‖ * P / cg) ^ q := by positivity
      apply mul_le_mul _ hvol ENNReal.toReal_nonneg (by positivity)
      apply mul_le_mul_of_nonneg_right _ hX
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hS0
    · rw [Set.indicator_of_notMem (fun h => hy (mem_closedBall_zero_iff.mp h))]
      have hz : ∀ x : Fin (m + 1) → ℂ, ((farCut m δ D x : ℝ) : ℂ) • ampIn β m ε Φ D t (x, y) = 0 := by
        intro x
        by_contra hx
        exact hy (hsupp x hx).1
      simp [hz]
  have hfin : muPi β (UT (m + 2)) (Metric.closedBall 0 (2 * v)) ≠ ⊤ := by
    rw [ns_muPi_closedBall β _ _ (by positivity)]; exact ENNReal.ofReal_ne_top
  have hintInd : Integrable ((Metric.closedBall (0 : UT (m + 2) → ℂ) (2 * v)).indicator (fun _ => Bd))
      (muPi β (UT (m + 2))) :=
    (integrable_indicator_iff measurableSet_closedBall).mpr (integrableOn_const hfin)
  have hnyle : (ny : ℝ) ≤ ((m : ℝ) + 2) ^ 2 := by
    rw [hny]; exact_mod_cast ns_card_UT (m + 2)
  have harith := ns_arith m C₉ q ny hε hkey hε2s hq hnyle
  rw [hFub]
  calc _ ≤ ∫ y : UT (m + 2) → ℂ, (Metric.closedBall (0 : UT (m + 2) → ℂ) (2 * v)).indicator (fun _ => Bd) y
          ∂(muPi β (UT (m + 2))) := norm_integral_le_of_norm_le hintInd (Filter.Eventually.of_forall hslice)
    _ = Bd * (‖β‖ / 2 * (2 * v) ^ 2) ^ ny := by
        rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, Measure.real,
          ns_muPi_closedBall β _ _ (by positivity), ENNReal.toReal_ofReal (by positivity), ← hny]
        ring
    _ = |CN| * |Cst| * (Cp / cg) ^ q * (‖β‖ / 2 * 4) ^ (m + 1) * (‖β‖ / 2 * 4) ^ ny * K *
          (‖t‖ ^ q * v ^ ((m + 2) * C₉ + (m + 2) * (C₉ + 1) * q + 2 * (m + 1) + 2 * ny)) := by
        rw [hBd, hS, hP, hwdef]; ring
    _ ≤ |CN| * |Cst| * (Cp / cg) ^ q * (‖β‖ / 2 * 4) ^ (m + 1) * (‖β‖ / 2 * 4) ^ ny * K * ‖t‖ ^ (m + 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hvdef]
        exact rpow_decay_arith hτ ht1 q _ (m + 2) harith
end _root_.Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
