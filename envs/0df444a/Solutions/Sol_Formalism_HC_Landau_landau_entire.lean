-- Prove2me | solution 1 for Formalism.HC.Landau.landau_entire
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:51:21.268696+00:00
-- url     : https://prove2.me/submissions/b4db768b-417d-476d-91c0-92adb9bacf67

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Landau
import Theorems.Thm_P2M_Formalism_HC_Landau_logDerivResidue__a43bb3aa1b21
import Theorems.Thm_P2M_Formalism_HC_Landau_natOrder_ne_zero__cbc415af1e91
import Theorems.Thm_P2M_Formalism_HC_Landau_integral_real__9be9cb33e88c
import Theorems.Thm_Formalism_HC_Landau_differentiable_AP
import Theorems.Thm_Formalism_HC_Landau_PhiP_eq
import Theorems.Thm_Formalism_HC_Landau_PhiP_analyticAt
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_landauEq
import Theorems.Thm_Formalism_logDerivZeroFree
import Theorems.Thm_Formalism_mellinDeriv
import Theorems.Thm_Formalism_ne_ofReal_of_lt_re
import Theorems.Thm_Formalism_ne_one_of_one_lt_re
import Theorems.Thm_Formalism_ne_zero_of_lt_re
import Theorems.Thm_Formalism_ofReal_ne_ofReal_of_lt
import Theorems.Thm_Formalism_ofReal_ne_one_of_lt
import Theorems.Thm_Formalism_sub_ne_zero_of_lt_re
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism Formalism.HC Formalism.HC.Landau
open Formalism ArithmeticFunction
namespace Formalism.HC.Landau
theorem _root_.solution (P : ℂ → ℂ) (hP : Differentiable ℂ P) (hP1 : ∀ s : ℂ, 1 ≤ s.re → P s ≠ 0) (a b : ℂ)
    (hA : AP P a b 1 = 0) (H : ℝ → ℝ) (hm : Measurable H) (hH : ∀ x : ℝ, 1 ≤ x → 0 ≤ H x)
    (hI : ∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1))
    (C θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hM : ∀ s : ℂ, 1 < s.re → ∫ x in Ioi (1:ℝ), (H x : ℂ) * (x : ℂ) ^ (-s - 1) =
      (deriv P s / P s - (a + b * s)) / (s * (s - 1)) + C / (s - θ)) :
    ∀ s : ℂ, θ < s.re → P s ≠ 0 := by
  have hP10 : P 1 ≠ 0 := hP1 1 (by simp)
  have lan : ∀ α : ℝ, θ ≤ α → α < 1 → (∀ σ : ℝ, α < σ → σ < 1 → P σ ≠ 0) →
      ∀ σ : ℝ, α < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1) ∧
        PhiP P a b C θ σ = ∫ x in Ioi (1:ℝ), (H x : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 1) := by
    intro α ha ha1 hL
    refine landauEq H α 1 ha1 hm.aestronglyMeasurable (fun x hx => hH x hx.le) hI (PhiP P a b C θ) ?_ ?_ ?_
    · intro s hs
      exact PhiP_analyticAt hP a b C θ (ne_zero_of_lt_re zero_le_one hs) (hP1 s hs.le) (ne_ofReal_of_lt_re (by linarith))
    · intro σ h1' h2'
      have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast (show σ ≠ 0 by linarith)
      have hσθ : (σ : ℂ) ≠ θ := ofReal_ne_ofReal_of_lt (by linarith)
      refine PhiP_analyticAt hP a b C θ hσ0 ?_ hσθ
      rcases h2'.lt_or_eq with h2' | h2'
      · exact hL σ h1' h2'
      · subst h2'
        simpa using hP10
    · intro s hs
      rw [hM s hs, PhiP_eq hA (ne_one_of_one_lt_re hs) (ne_zero_of_lt_re zero_le_one hs) (hP1 s hs.le)]

  have hreal : ∀ σ : ℝ, θ < σ → σ < 1 → P σ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨β0, hβ0, hβ1, hz0⟩ := hcon
    set Pr : ℝ → ℂ := fun σ => P σ with hPr
    have hPc : Continuous Pr := hP.continuous.comp Complex.continuous_ofReal
    set Z : Set ℝ := Icc β0 1 ∩ Pr ⁻¹' {0} with hZ
    have hZc : IsCompact Z := isCompact_Icc.inter_right (isClosed_singleton.preimage hPc)
    have hZne : Z.Nonempty := ⟨β0, ⟨le_rfl, hβ1.le⟩, hz0⟩
    have hbdd : BddAbove Z := hZc.bddAbove
    have hβZ : sSup Z ∈ Z := hZc.sSup_mem hZne
    set β := sSup Z with hβdef
    obtain ⟨⟨hβ0le, hβle1⟩, hβP⟩ := hβZ
    have hβPz : P β = 0 := hβP
    have hβ1' : β < 1 := by
      rcases hβle1.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [h] at hβPz
        exact hP10 (by simpa using hβPz)
    have hnz : ∀ σ : ℝ, β < σ → σ < 1 → P σ ≠ 0 := by
      intro σ h1 h2 hz
      have := le_csSup hbdd (show σ ∈ Z from ⟨⟨by linarith, h2.le⟩, hz⟩)
      linarith
    have hβθ : θ < β := by linarith
    have hβ0' : 0 < β := by linarith
    have hLan := lan β hβθ.le hβ1' hnz
    set z : ℂ := (β : ℂ) with hb
    have hbθ : z - (θ : ℂ) ≠ 0 := sub_ne_zero.mpr (ofReal_ne_ofReal_of_lt hβθ)
    have hb0 : z ≠ 0 := by rw [hb]; exact_mod_cast hβ0'.ne'
    have hb1 : z - 1 ≠ 0 := sub_ne_zero.mpr (ofReal_ne_one_of_lt hβ1')
    set m : ℕ := analyticOrderNatAt P z with hmdef
    have hlL : Tendsto (fun s => (s - z) * (deriv P s / P s)) (𝓝[≠] z) (𝓝 (m : ℂ)) :=
      logDerivResidue' P z hP ⟨1, hP10⟩
    have hlin : Tendsto (fun s => (s - z) * (a + b * s)) (𝓝[≠] z) (𝓝 0) := by
      have hc : Continuous (fun s => (s - z) * (a + b * s)) := by fun_prop
      have := (hc.tendsto z).mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))
      simpa using this
    have hden : Tendsto (fun s : ℂ => s * (s - 1)) (𝓝[≠] z) (𝓝 (z * (z - 1))) :=
      ((continuous_id.mul (continuous_id.sub continuous_const)).tendsto z).mono_left
        (nhdsWithin_le_nhds (s := {z}ᶜ))
    have hCt : Tendsto (fun s : ℂ => (C : ℂ) * (s - z) / (s - θ)) (𝓝[≠] z) (𝓝 0) := by
      have hca : ContinuousAt (fun s : ℂ => (C : ℂ) * (s - z) / (s - θ)) z :=
        (continuousAt_const.mul (continuousAt_id.sub continuousAt_const)).div
          (continuousAt_id.sub continuousAt_const) hbθ
      have := hca.tendsto.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))
      simpa using this
    have hg := ((hlL.sub hlin).div hden (mul_ne_zero hb0 hb1)).add hCt
    have hpath : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] β) (𝓝[≠] z) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((Complex.continuous_ofReal.tendsto β).mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun σ hσ =>
          ofReal_ne_ofReal_of_lt (mem_Ioi.mp hσ))
    have hre := (Complex.continuous_re.tendsto _).comp (hg.comp hpath)
    have hev : ∀ᶠ σ in 𝓝[>] β, 0 ≤ (((fun s : ℂ => ((s - z) * (deriv P s / P s) - (s - z) * (a + b * s))
        / (s * (s - 1)) + (C : ℂ) * (s - z) / (s - θ)) ∘ (fun σ : ℝ => (σ : ℂ))) σ).re := by
      filter_upwards [Ioo_mem_nhdsGT hβ1'] with σ hσ
      obtain ⟨h1, h2⟩ := hσ
      have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast (show σ ≠ 0 by linarith)
      have hσ1 : (σ : ℂ) ≠ 1 := ofReal_ne_one_of_lt h2
      have hPe := PhiP_eq (C := C) (θ := θ) hA hσ1 hσ0 (hnz σ h1 h2)
      have hPi := (hLan σ h1).2
      rw [integral_real'] at hPi
      have hgσ : (((σ : ℂ) - z) * (deriv P σ / P σ) - ((σ : ℂ) - z) * (a + b * σ))
          / ((σ : ℂ) * ((σ : ℂ) - 1)) + (C : ℂ) * ((σ : ℂ) - z) / ((σ : ℂ) - θ)
          = (((σ - β : ℝ) : ℂ)) * PhiP P a b C θ σ := by
        rw [hPe, hb]
        push_cast
        ring
      simp only [Function.comp_apply]
      rw [hgσ, hPi, ← Complex.ofReal_mul, Complex.ofReal_re]
      refine mul_nonneg (by linarith) (setIntegral_nonneg measurableSet_Ioi fun x hx => ?_)
      exact mul_nonneg (hH x (le_of_lt (mem_Ioi.mp hx)))
        (Real.rpow_nonneg (by linarith [mem_Ioi.mp hx]) _)
    have hge := ge_of_tendsto hre hev
    have hval : ((m : ℂ) - 0) / (z * (z - 1)) + 0 = ((((m : ℝ)) / (β * (β - 1)) : ℝ) : ℂ) := by
      rw [hb]
      push_cast
      ring
    rw [hval, Complex.ofReal_re] at hge
    have hm1 : m ≠ 0 := natOrder_ne_zero' hP hP10 hβPz
    have hnum : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm1
    have hden' : β * (β - 1) < 0 := mul_neg_of_pos_of_neg hβ0' (by linarith)
    have := div_neg_of_pos_of_neg hnum hden'
    linarith
  have hInt := fun σ hσ => (lan θ le_rfl hθ1 hreal σ hσ).1
  set I : ℂ → ℂ := fun s => ∫ x in Ioi (1:ℝ), (H x : ℂ) * (x : ℂ) ^ (-s - 1) with hIdef
  set U : Set ℂ := {s | θ < s.re} with hU_def
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hId : DifferentiableOn ℂ I U := by
    intro s hs
    have hD := mellinDeriv (fun x => ((H x : ℝ) : ℂ)) θ
      (Complex.measurable_ofReal.comp hm).aestronglyMeasurable
      (fun σ hσ => (hInt σ hσ).congr_fun (fun x hx => by
        simp only [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hH x (le_of_lt (mem_Ioi.mp hx)))])
        measurableSet_Ioi) s hs
    exact hD.differentiableAt.differentiableWithinAt
  have hAd := differentiable_AP hP a b
  have hf1 : DifferentiableOn ℂ (fun s => s * (s - 1) * P s * (I s - C / (s - θ))) U := by
    intro s hs
    have hsθ : s - (θ : ℂ) ≠ 0 := sub_ne_zero_of_lt_re hs
    have hIs := (hId s hs).differentiableAt (hUopen.mem_nhds hs)
    have hEs := hP s
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := exact hsθ)
  have hEq : EqOn (fun s => s * (s - 1) * P s * (I s - C / (s - θ))) (AP P a b) U := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (hf1.analyticOnNhd hUopen) (hAd.differentiableOn.analyticOnNhd hUopen)
      (convex_halfSpace_re_gt θ).isPreconnected (z₀ := 2)
      (show θ < (2:ℂ).re by simp; linarith) ?_
    have h2mem : (2:ℂ) ∈ {s : ℂ | 1 < s.re} := by simp
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h2mem] with z hz
    have hz' : 1 < z.re := hz
    have hZ := hP1 z hz'.le
    have hs1' : z - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_one_lt_re hz')
    have hs0 : z ≠ 0 := ne_zero_of_lt_re zero_le_one hz'
    have hsθ : z - θ ≠ 0 := sub_ne_zero_of_lt_re (a := θ) (by linarith)
    have e : I z = _ := hM z hz'
    rw [e]
    unfold AP
    field_simp
    ring
  set q : ℂ → ℂ := fun s => (a + b * s) + s * (s - 1) * (I s - C / (s - θ)) with hq_def
  have hqd : DifferentiableOn ℂ q U := by
    intro s hs
    have hsθ : s - (θ : ℂ) ≠ 0 := sub_ne_zero_of_lt_re hs
    have hIs := (hId s hs).differentiableAt (hUopen.mem_nhds hs)
    apply DifferentiableAt.differentiableWithinAt
    simp only [hq_def]
    fun_prop (disch := exact hsθ)
  have hid : ∀ s ∈ U, deriv P s = q s * P s := by
    intro s hs
    have he := hEq hs
    simp only at he
    unfold AP at he
    simp only [hq_def]
    linear_combination -he
  intro s hs
  exact logDerivZeroFree P q U hUopen hP ⟨1, hP10⟩ hqd hid s hs
end Formalism.HC.Landau
