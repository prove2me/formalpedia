-- Prove2me | solution 1 for DRSOWass.Duality.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T08:19:17.250467+00:00
-- url     : https://prove2.me/submissions/960701bb-f958-4878-af0d-14eb189304f1

import Mathlib
import Definitions.Def_DRSOWass_Duality_Setting

open MeasureTheory Filter Topology

set_option linter.unusedSectionVars false

namespace DRSOWWeakAux

open DRSOWass.Duality ModelRiskOT.Duality

lemma ereal_alg (a1 a2 b1 b2 c : ENNReal) (hb1 : b1 ≠ ⊤) (hc : c ≠ ⊤)
    (h : a1 + b1 ≤ c + a2 + b2) :
    (a1 : EReal) - a2 ≤ (c : EReal) - ((b1 : EReal) - b2) := by
  by_cases ha2 : a2 = ⊤
  · subst ha2; simp
  by_cases hb2 : b2 = ⊤
  · subst hb2
    rw [EReal.coe_ennreal_top, EReal.sub_top, EReal.sub_bot (by simp)]; exact le_top
  have ha1 : a1 ≠ ⊤ := by
    intro h1; subst h1; simp_all [ENNReal.add_eq_top]
  lift a1 to NNReal using ha1
  lift a2 to NNReal using ha2
  lift b1 to NNReal using hb1
  lift b2 to NNReal using hb2
  lift c to NNReal using hc
  simp only [EReal.coe_nnreal_eq_coe_real]
  have h' : (a1:ℝ) + b1 ≤ c + a2 + b2 := by exact_mod_cast h
  rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
  linarith

lemma pw_alg (u : ℝ) (v : EReal) (L : ℝ) (hL : 0 ≤ L) (h : v ≤ ((L - u : ℝ) : EReal)) :
    ENNReal.ofReal u + v.toENNReal ≤ ENNReal.ofReal L + ENNReal.ofReal (-u) + (-v).toENNReal := by
  induction v using EReal.rec with
  | bot => simp
  | top => exact absurd h (EReal.coe_lt_top _).not_ge
  | coe v =>
    have h' : v ≤ L - u := by exact_mod_cast h
    simp only [EReal.real_coe_toENNReal, ← EReal.coe_neg]
    rcases le_total 0 u with hu | hu <;> rcases le_total 0 v with hv | hv
    · rw [← ENNReal.ofReal_add hu hv, add_assoc]
      exact le_add_right (ENNReal.ofReal_le_ofReal (by linarith))
    · rw [ENNReal.ofReal_of_nonpos hv, add_zero, add_right_comm,
        ← ENNReal.ofReal_add hL (by linarith)]
      exact le_add_right (ENNReal.ofReal_le_ofReal (by linarith))
    · rw [ENNReal.ofReal_of_nonpos hu, zero_add, ← ENNReal.ofReal_add hL (by linarith)]
      exact le_add_right (ENNReal.ofReal_le_ofReal (by linarith))
    · rw [ENNReal.ofReal_of_nonpos hu, ENNReal.ofReal_of_nonpos hv, zero_add]; exact bot_le

variable {Ξ : Type*} [MetricSpace Ξ] [SecondCountableTopology Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ]

lemma phi_le_of (Ψ : Ξ → ℝ) (p lam : ℝ) (ξ ζ : Ξ) :
    Phi Ψ p lam ζ ≤ ((lam * dist ξ ζ ^ p - Ψ ξ : ℝ) : EReal) :=
  iInf_le (fun ξ => ((lam * dist ξ ζ ^ p - Ψ ξ : ℝ) : EReal)) ξ

lemma phi_le_neg (Ψ : Ξ → ℝ) (p lam : ℝ) (hp : 0 < p) (ζ : Ξ) :
    Phi Ψ p lam ζ ≤ ((-Ψ ζ : ℝ) : EReal) := by
  have := phi_le_of Ψ p lam ζ ζ
  simpa [Real.zero_rpow hp.ne'] using this

lemma cont_term (Ψ : Ξ → ℝ) (p lam : ℝ) (hp : 0 < p) (ξ : Ξ) :
    Continuous fun ζ => lam * dist ξ ζ ^ p - Ψ ξ := by
  have : Continuous fun ζ => dist ξ ζ := continuous_const.dist continuous_id
  exact (continuous_const.mul (this.rpow_const (fun _ => Or.inr hp.le))).sub continuous_const

lemma phi_measurable (Ψ : Ξ → ℝ) (p lam : ℝ) (hp : 0 < p) : Measurable (Phi Ψ p lam) := by
  apply UpperSemicontinuous.measurable
  show UpperSemicontinuous fun ζ => ⨅ ξ : Ξ, ((lam * dist ξ ζ ^ p - Ψ ξ : ℝ) : EReal)
  exact upperSemicontinuous_iInf fun ξ =>
    (continuous_coe_real_ereal.comp (cont_term Ψ p lam hp ξ)).upperSemicontinuous

lemma extIntegral_real {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) :
    extIntegral μ (fun x => (f x : EReal)) =
      ((∫⁻ x, ENNReal.ofReal (f x) ∂μ : ENNReal) : EReal) -
        ((∫⁻ x, ENNReal.ofReal (-f x) ∂μ : ENNReal) : EReal) := by
  rfl

lemma phi_pos_ne_top (ν : Measure Ξ) (Ψ : Ξ → ℝ) (hΨ : Integrable Ψ ν) (p lam : ℝ) (hp : 0 < p) :
    ∫⁻ ζ, (Phi Ψ p lam ζ).toENNReal ∂ν ≠ ⊤ := by
  refine ne_top_of_le_ne_top hΨ.neg.lintegral_lt_top.ne (lintegral_mono fun ζ => ?_)
  exact EReal.toENNReal_le_toENNReal (phi_le_neg Ψ p lam hp ζ)

lemma extIntegral_phi_ne_top (ν : Measure Ξ) (Ψ : Ξ → ℝ) (hΨ : Integrable Ψ ν) (p lam : ℝ)
    (hp : 0 < p) : extIntegral ν (Phi Ψ p lam) ≠ ⊤ := by
  unfold extIntegral
  intro h
  have h1 := phi_pos_ne_top ν Ψ hΨ p lam hp
  have : ((∫⁻ ζ, (Phi Ψ p lam ζ).toENNReal ∂ν : ENNReal) : EReal) -
      ((∫⁻ ζ, (-Phi Ψ p lam ζ).toENNReal ∂ν : ENNReal) : EReal) ≤
      ((∫⁻ ζ, (Phi Ψ p lam ζ).toENNReal ∂ν : ENNReal) : EReal) - 0 :=
    EReal.sub_le_sub le_rfl (EReal.coe_ennreal_nonneg _)
  rw [h, sub_zero, top_le_iff, EReal.coe_ennreal_eq_top_iff] at this
  exact h1 this

lemma coupling_bound (ν : Measure Ξ) (Ψ : Ξ → ℝ) (hΨm : Measurable Ψ) (hΨ : Integrable Ψ ν)
    (p : ℝ) (hp : 0 < p) (lam : ℝ) (hlam : 0 ≤ lam)
    (μ : Measure Ξ) (γ : Measure (Ξ × Ξ)) (h1 : γ.map Prod.fst = μ) (h2 : γ.map Prod.snd = ν)
    (hC : ∫⁻ w, ENNReal.ofReal (dist w.1 w.2 ^ p) ∂γ ≠ ⊤) :
    extIntegral μ (fun ξ => (Ψ ξ : EReal)) ≤
      ((lam * (∫⁻ w, ENNReal.ofReal (dist w.1 w.2 ^ p) ∂γ).toReal : ℝ) : EReal) -
        extIntegral ν (Phi Ψ p lam) := by
  set C := ∫⁻ w, ENNReal.ofReal (dist w.1 w.2 ^ p) ∂γ with hCdef
  have hΦm := phi_measurable Ψ p lam hp
  have key : ∀ w : Ξ × Ξ, ENNReal.ofReal (Ψ w.1) + (Phi Ψ p lam w.2).toENNReal ≤
      ENNReal.ofReal lam * ENNReal.ofReal (dist w.1 w.2 ^ p) + ENNReal.ofReal (-Ψ w.1) +
        (-Phi Ψ p lam w.2).toENNReal := by
    intro w
    rw [← ENNReal.ofReal_mul hlam]
    exact pw_alg _ _ _ (mul_nonneg hlam (by positivity)) (phi_le_of Ψ p lam w.1 w.2)
  have hint := lintegral_mono (μ := γ) key
  have mΨp : Measurable fun ξ => ENNReal.ofReal (Ψ ξ) := ENNReal.measurable_ofReal.comp hΨm
  have mΨn : Measurable fun ξ => ENNReal.ofReal (-Ψ ξ) := ENNReal.measurable_ofReal.comp hΨm.neg
  have mΦp : Measurable fun ζ => (Phi Ψ p lam ζ).toENNReal := measurable_ereal_toENNReal.comp hΦm
  have mΦn : Measurable fun ζ => (-Phi Ψ p lam ζ).toENNReal :=
    measurable_ereal_toENNReal.comp hΦm.neg
  have e1 : ∫⁻ w, ENNReal.ofReal (Ψ w.1) ∂γ = ∫⁻ ξ, ENNReal.ofReal (Ψ ξ) ∂μ := by
    rw [← h1, lintegral_map mΨp measurable_fst]
  have e2 : ∫⁻ w, ENNReal.ofReal (-Ψ w.1) ∂γ = ∫⁻ ξ, ENNReal.ofReal (-Ψ ξ) ∂μ := by
    rw [← h1, lintegral_map mΨn measurable_fst]
  have e3 : ∫⁻ w, (Phi Ψ p lam w.2).toENNReal ∂γ = ∫⁻ ζ, (Phi Ψ p lam ζ).toENNReal ∂ν := by
    rw [← h2, lintegral_map mΦp measurable_snd]
  have e4 : ∫⁻ w, (-Phi Ψ p lam w.2).toENNReal ∂γ = ∫⁻ ζ, (-Phi Ψ p lam ζ).toENNReal ∂ν := by
    rw [← h2, lintegral_map mΦn measurable_snd]
  have mΨp' : Measurable fun w : Ξ × Ξ => ENNReal.ofReal (Ψ w.1) := mΨp.comp measurable_fst
  rw [lintegral_add_left mΨp', lintegral_add_left' ?_,
    lintegral_add_left' ?_, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, e1, e2, e3, e4]
    at hint
  rotate_left
  · exact (measurable_const.mul ((ENNReal.measurable_ofReal.comp
      ((measurable_fst.dist measurable_snd).pow_const p)))).aemeasurable
  · exact ((measurable_const.mul ((ENNReal.measurable_ofReal.comp
      ((measurable_fst.dist measurable_snd).pow_const p)))).add
      (mΨn.comp measurable_fst)).aemeasurable
  have := ereal_alg _ _ _ _ _ (phi_pos_ne_top ν Ψ hΨ p lam hp)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC) hint
  rw [extIntegral_real]
  unfold extIntegral
  convert this using 2
  rw [← ENNReal.ofReal_toReal hC, ← ENNReal.ofReal_mul hlam, EReal.coe_ennreal_ofReal,
    max_eq_left (mul_nonneg hlam ENNReal.toReal_nonneg), ENNReal.ofReal_toReal hC]

theorem weak {Ξ : Type*} [MetricSpace Ξ] [SecondCountableTopology Ξ]
    [MeasurableSpace Ξ] [BorelSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (Ψ : Ξ → ℝ) (p : ℝ) (θ : ℝ)
    (hp : 1 ≤ p) (hθ : 0 < θ) (hΨm : Measurable Ψ) (hΨ : Integrable Ψ ν) :
    vP Ψ ν p θ ≤ vD Ψ ν p θ := by
  have hp0 : 0 < p := by linarith
  have hθp : 0 < θ ^ p := Real.rpow_pos_of_pos hθ p
  unfold vP vD
  refine iSup₂_le fun μ hμ => le_iInf₂ fun lam hlam => ?_
  unfold dualObj
  obtain ⟨-, hW⟩ := hμ
  set X := extIntegral ν (Phi Ψ p lam) with hX
  rw [← EReal.le_of_forall_lt_iff_le]
  intro z hz
  by_cases hXb : X = ⊥
  · rw [hXb, EReal.sub_bot (EReal.coe_ne_bot _)] at hz
    exact absurd hz (not_lt.mpr le_top)
  have hXt : X ≠ ⊤ := extIntegral_phi_ne_top ν Ψ hΨ p lam hp0
  obtain ⟨x, hx⟩ : ∃ x : ℝ, X = x := ⟨X.toReal, (EReal.coe_toReal hXt hXb).symm⟩
  rw [hx, ← EReal.coe_sub, EReal.coe_lt_coe_iff] at hz
  set η := (z - (lam * θ ^ p - x)) / (lam + 1) with hη
  have hη0 : 0 < η := div_pos (by linarith) (by linarith)
  have hlη : lam * η ≤ z - (lam * θ ^ p - x) := by
    have hD : 0 < z - (lam * θ ^ p - x) := by linarith
    rw [hη, mul_div_assoc']
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hlt : wassPow p μ ν < ENNReal.ofReal (θ ^ p + η) := by
    refine lt_of_le_of_lt hW ?_
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  unfold wassPow RWPI.SqrtLasso.transportCost at hlt
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.mp hlt
  obtain ⟨⟨-, h1, h2⟩, hγ'⟩ := iInf_lt_iff.mp hγ
  have hCt : ∫⁻ w, ENNReal.ofReal (dist w.1 w.2 ^ p) ∂γ ≠ ⊤ :=
    ne_top_of_lt (lt_trans hγ' ENNReal.ofReal_lt_top)
  have hb := coupling_bound ν Ψ hΨm hΨ p hp0 lam hlam μ γ h1 h2 hCt
  rw [← hX, hx, ← EReal.coe_sub] at hb
  refine hb.trans (EReal.coe_le_coe_iff.mpr ?_)
  have hCr := ENNReal.toReal_lt_of_lt_ofReal hγ'
  nlinarith

end DRSOWWeakAux

theorem solution {Ξ : Type*} [MetricSpace Ξ] [CompleteSpace Ξ] [SecondCountableTopology Ξ]
    [MeasurableSpace Ξ] [BorelSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (Ψ : Ξ → ℝ) (p : ℝ) (θ : ℝ)
    (hp : 1 ≤ p) (hθ : 0 < θ) (hΨm : Measurable Ψ) (hΨ : Integrable Ψ ν) :
    DRSOWass.Duality.vP Ψ ν p θ ≤ DRSOWass.Duality.vD Ψ ν p θ :=
  DRSOWWeakAux.weak ν Ψ p θ hp hθ hΨm hΨ
