-- Prove2me | solution 1 for BertsekasShreve.ImperfectInfo.prop_10_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T05:24:53.799214+00:00
-- url     : https://prove2.me/submissions/197d5a68-30d0-481e-bf8b-54fae0985bde
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BertsekasShreve_ImperfectInfo_SufficientStatistic
import Theorems.Thm_BertsekasShreve_ImperfectInfo_prop_10_2
import Theorems.Thm_BertsekasShreve_ImperfectInfo_cor_10_2_1
import Theorems.Thm_BertsekasShreve_ImperfectInfo_lemma_10_2
import Theorems.Thm_BertsekasShreve_ImperfectInfo_optCostHat_gt_bot
import Theorems.Thm_BertsekasShreve_ImperfectInfo_optCostHat_univMeasurable
import Theorems.Thm_BertsekasShreve_ImperfectInfo_costHat_univMeasurable

open MeasureTheory ProbabilityTheory


namespace BertsekasShreve.ImperfectInfo.BS10Aux

lemma extIntegral_mono {α : Type} [MeasurableSpace α] (ν : Measure α) {f g : α → EReal}
    (h : ∀ a, f a ≤ g a) : extIntegral ν f ≤ extIntegral ν g := by
  have hp : ∫⁻ a, posPart (f a) ∂ν ≤ ∫⁻ a, posPart (g a) ∂ν :=
    lintegral_mono fun a => EReal.toENNReal_le_toENNReal (h a)
  have hn : ∫⁻ a, negPart (g a) ∂ν ≤ ∫⁻ a, negPart (f a) ∂ν :=
    lintegral_mono fun a => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (h a))
  unfold extIntegral
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (top_le_iff.1 (h1 ▸ hp)) h2
  · exact le_top
  · exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.2 hp)
      (EReal.coe_ennreal_le_coe_ennreal_iff.2 hn)

lemma extIntegral_congr_ae {α : Type} [MeasurableSpace α] (ν : Measure α) {f g : α → EReal}
    (h : f =ᵐ[ν] g) : extIntegral ν f = extIntegral ν g := by
  have hp : ∫⁻ a, posPart (f a) ∂ν = ∫⁻ a, posPart (g a) ∂ν :=
    lintegral_congr_ae (h.mono fun a ha => by simp [ha])
  have hn : ∫⁻ a, negPart (f a) ∂ν = ∫⁻ a, negPart (g a) ∂ν :=
    lintegral_congr_ae (h.mono fun a ha => by simp [ha])
  unfold extIntegral
  rw [hp, hn]

lemma univMeasurable_comp {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {f : β → γ} {g : α → β} (hf : UnivMeasurable f) (hg : Measurable g) :
    UnivMeasurable (f ∘ g) := by
  intro ν hν
  have : IsProbabilityMeasure (ν.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  exact (hf (ν.map g) this).comp_quasiMeasurePreserving
    (Measure.QuasiMeasurePreserving.mk hg Measure.AbsolutelyContinuous.rfl)

lemma measurable_posPart : Measurable (fun x : EReal => posPart x) := by
  unfold posPart; fun_prop

lemma measurable_negPart : Measurable (fun x : EReal => negPart x) := by
  unfold negPart; fun_prop

/-- pointwise identity `(x+ε)⁺ + x⁻ = x⁺ + (x+ε)⁻ + ε` for `x > -∞`. -/
lemma pos_neg_identity (x : EReal) (hx : x ≠ ⊥) (ε : ℝ) (hε : 0 < ε) :
    posPart (x + (ε : EReal)) + negPart x =
      posPart x + negPart (x + (ε : EReal)) + ENNReal.ofReal ε := by
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | top => simp [posPart, negPart]
  | coe r =>
    rw [← EReal.coe_add]
    simp only [posPart, negPart, ← EReal.coe_neg, EReal.real_coe_toENNReal]
    rcases le_total 0 r with hr | hr
    · rw [ENNReal.ofReal_of_nonpos (by linarith : -r ≤ 0),
        ENNReal.ofReal_of_nonpos (by linarith : -(r + ε) ≤ 0), ENNReal.ofReal_add hr hε.le]
      simp
    · rcases le_total 0 (r + ε) with hre | hre
      · rw [ENNReal.ofReal_of_nonpos hr, ENNReal.ofReal_of_nonpos (by linarith : -(r + ε) ≤ 0),
          ← ENNReal.ofReal_add hre (by linarith)]
        simp
      · rw [ENNReal.ofReal_of_nonpos hre, ENNReal.ofReal_of_nonpos hr, zero_add, zero_add,
          ← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ -(r + ε)) hε.le]
        ring_nf

lemma posPart_add_le (x : EReal) (ε : ℝ) :
    posPart (x + (ε : EReal)) ≤ posPart x + ENNReal.ofReal ε := by
  unfold posPart
  exact EReal.toENNReal_add_le.trans (by simp)

lemma negPart_le_add (x : EReal) (hx : x ≠ ⊥) (ε : ℝ) (hε : 0 < ε) :
    negPart x ≤ negPart (x + (ε : EReal)) + ENNReal.ofReal ε := by
  have := pos_neg_identity x hx ε hε
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | top => simp [negPart]
  | coe r =>
    rw [← EReal.coe_add]
    simp only [negPart, ← EReal.coe_neg, EReal.real_coe_toENNReal]
    calc ENNReal.ofReal (-r) = ENNReal.ofReal (-(r + ε) + ε) := by ring_nf
      _ ≤ _ := ENNReal.ofReal_add_le

/-- The integration step of the proof of Proposition 10.3 under `(F⁺, F̂⁺)`. -/
lemma eps_integrate {α : Type} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν] (f g : α → EReal)
    (hf : ∀ a, ⊥ < f a) (hfm : AEMeasurable f ν) (ε : ℝ) (hε : 0 < ε)
    (hg : ∀ a, g a ≤ f a + (ε : EReal)) :
    (⊥ < extIntegral ν f → extIntegral ν g ≤ extIntegral ν f + (ε : EReal)) ∧
    (extIntegral ν f = ⊥ → extIntegral ν g ≤ ((-1 / ε : ℝ) : EReal)) := by
  have hgF : extIntegral ν g ≤ extIntegral ν (fun a => f a + (ε : EReal)) := extIntegral_mono ν hg
  set P := ∫⁻ a, posPart (f a) ∂ν with hP
  set N := ∫⁻ a, negPart (f a) ∂ν with hN
  set P' := ∫⁻ a, posPart (f a + (ε : EReal)) ∂ν with hP'
  set N' := ∫⁻ a, negPart (f a + (ε : EReal)) ∂ν with hN'
  have hPP' : P' ≤ P + ENNReal.ofReal ε := by
    calc P' ≤ ∫⁻ a, (posPart (f a) + ENNReal.ofReal ε) ∂ν :=
          lintegral_mono fun a => posPart_add_le (f a) ε
      _ ≤ P + ENNReal.ofReal ε := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  have hNN' : N ≤ N' + ENNReal.ofReal ε := by
    calc N ≤ ∫⁻ a, (negPart (f a + (ε : EReal)) + ENNReal.ofReal ε) ∂ν :=
          lintegral_mono fun a => negPart_le_add (f a) (hf a).ne' ε hε
      _ = N' + ENNReal.ofReal ε := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  have hposm : AEMeasurable (fun a => posPart (f a)) ν := measurable_posPart.comp_aemeasurable hfm
  have hnegm : AEMeasurable (fun a => negPart (f a)) ν := measurable_negPart.comp_aemeasurable hfm
  have hid : P' + N = P + N' + ENNReal.ofReal ε := by
    have h1 : ∫⁻ a, (posPart (f a + (ε : EReal)) + negPart (f a)) ∂ν = P' + N :=
      lintegral_add_right' _ hnegm
    have h2 : ∫⁻ a, (posPart (f a) + negPart (f a + (ε : EReal)) + ENNReal.ofReal ε) ∂ν =
        P + N' + ENNReal.ofReal ε := by
      rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_add_left' hposm]
    rw [← h1, ← h2]
    exact lintegral_congr fun a => pos_neg_identity (f a) (hf a).ne' ε hε
  have hFdef : extIntegral ν (fun a => f a + (ε : EReal)) =
      if P' = ⊤ then ⊤ else (P' : EReal) - (N' : EReal) := rfl
  have hfdef : extIntegral ν f = if P = ⊤ then ⊤ else (P : EReal) - (N : EReal) := rfl
  constructor
  · intro hbot
    by_cases hPtop : P = ⊤
    · rw [hfdef, if_pos hPtop, EReal.top_add_coe]; exact le_top
    rw [hfdef, if_neg hPtop] at hbot ⊢
    have hNtop : N ≠ ⊤ := by
      intro h; rw [h, EReal.coe_ennreal_top, EReal.sub_top] at hbot; exact lt_irrefl _ hbot
    have hP'top : P' ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hPtop, ENNReal.ofReal_ne_top⟩) hPP'
    refine hgF.trans ?_
    rw [hFdef, if_neg hP'top]
    by_cases hN'top : N' = ⊤
    · rw [hN'top, EReal.coe_ennreal_top, EReal.sub_top]; exact bot_le
    have hr := congrArg ENNReal.toReal hid
    rw [ENNReal.toReal_add hP'top hNtop, ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hPtop, hN'top⟩)
      ENNReal.ofReal_ne_top, ENNReal.toReal_add hPtop hN'top, ENNReal.toReal_ofReal hε.le] at hr
    rw [← EReal.coe_ennreal_toReal hP'top, ← EReal.coe_ennreal_toReal hN'top,
      ← EReal.coe_ennreal_toReal hPtop, ← EReal.coe_ennreal_toReal hNtop,
      ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith
  · intro hbot
    by_cases hPtop : P = ⊤
    · rw [hfdef, if_pos hPtop] at hbot; exact absurd hbot (by simp)
    rw [hfdef, if_neg hPtop] at hbot
    have hNtop : N = ⊤ := by
      by_contra h
      rw [← EReal.coe_ennreal_toReal hPtop, ← EReal.coe_ennreal_toReal h, ← EReal.coe_sub] at hbot
      exact EReal.coe_ne_bot _ hbot
    have hN'top : N' = ⊤ := by
      by_contra h
      rw [hNtop] at hNN'
      exact absurd (top_le_iff.1 hNN') (ENNReal.add_ne_top.2 ⟨h, ENNReal.ofReal_ne_top⟩)
    have hP'top : P' ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hPtop, ENNReal.ofReal_ne_top⟩) hPP'
    refine hgF.trans ?_
    rw [hFdef, if_neg hP'top, hN'top, EReal.coe_ennreal_top, EReal.sub_top]
    exact bot_le

lemma ae_eq_of_measure_eq_one {α : Type} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (f g : α → EReal) (hf : AEMeasurable f ν) (hg : AEMeasurable g ν)
    (h : ν {a | g a = f a} = 1) : g =ᵐ[ν] f := by
  set T := {a | hg.mk g a ≤ hf.mk f a} ∩ {a | hf.mk f a ≤ hg.mk g a} with hTdef
  have hT : MeasurableSet T :=
    (measurableSet_le hg.measurable_mk hf.measurable_mk).inter
      (measurableSet_le hf.measurable_mk hg.measurable_mk)
  have hST : {a | g a = f a} =ᵐ[ν] T := by
    filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with a ha hb
    change (g a = f a) = (hg.mk g a ≤ hf.mk f a ∧ hf.mk f a ≤ hg.mk g a)
    rw [← ha, ← hb]
    exact propext le_antisymm_iff
  have hT1 : ν T = 1 := (measure_congr hST).symm.trans h
  have hTc : ν Tᶜ = 0 := (prob_compl_eq_zero_iff hT).2 hT1
  have hae : ∀ᵐ a ∂ν, a ∈ T := measure_eq_zero_iff_ae_notMem.1 hTc |>.mono fun a ha => by
    simpa using ha
  filter_upwards [hae, hf.ae_eq_mk, hg.ae_eq_mk] with a ha hfa hga
  rw [hfa, hga]
  exact le_antisymm ha.1 ha.2

end BertsekasShreve.ImperfectInfo.BS10Aux

open BertsekasShreve.ImperfectInfo in
theorem solution {S C Z : Type}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (M : ISIModel S C Z) {Y : ℕ → Type} [∀ k, TopologicalSpace (Y k)] [∀ k, MeasurableSpace (Y k)]
    (σ : SuffStat M Y)
    (hF : (M.Fplus ∧ σ.FhatPlus) ∨ (M.Fminus ∧ σ.FhatMinus)) :
    (∀ p : ProbabilityMeasure S, M.optCost p = extIntegral (σ.phi p) σ.optCostHat) ∧
    (∀ μ : (k : ℕ) → Y k → ProbabilityMeasure C, σ.IsMarkovPolicy μ →
      σ.IsOptimalHat (markovToPolicy μ) → M.IsOptimal (σ.toISI μ)) ∧
    (∀ μ : (k : ℕ) → Y k → ProbabilityMeasure C, σ.IsMarkovPolicy μ →
      ∀ p : ProbabilityMeasure S,
        σ.IsQOptimal (σ.phi p) (markovToPolicy μ) → M.IsOptimalAt (σ.toISI μ) p) ∧
    (∀ μ : (k : ℕ) → Y k → ProbabilityMeasure C, σ.IsMarkovPolicy μ →
      ∀ (p : ProbabilityMeasure S) (ε : ℝ), 0 < ε →
        σ.IsWeaklyEpsOptimal (σ.phi p) ε (markovToPolicy μ) →
          M.IsEpsOptimalAt (σ.toISI μ) p ε) ∧
    (M.Fplus ∧ σ.FhatPlus →
      ∀ μ : (k : ℕ) → Y k → ProbabilityMeasure C, σ.IsMarkovPolicy μ →
        ∀ ε : ℝ, 0 < ε → σ.IsEpsOptimalHat ε (markovToPolicy μ) →
          M.IsEpsOptimal (σ.toISI μ) ε) := by
  classical
  have hFhat : σ.FhatPlus ∨ σ.FhatMinus := hF.imp (fun h => h.2) (fun h => h.2)
  -- Markov (PSI) policies are (PSI) policies
  have hMP : ∀ μ : (k : ℕ) → Y k → ProbabilityMeasure C, σ.IsMarkovPolicy μ →
      σ.IsPolicy (markovToPolicy μ) := by
    intro μ hμ
    refine ⟨fun n => ?_, fun n hn o => hμ.2 n hn _⟩
    exact BS10Aux.univMeasurable_comp (hμ.1 n)
      ((measurable_pi_apply (Fin.last n)).comp measurable_fst)
  -- a Markov (PSI) policy, used through the statistic, is an (ISI) policy
  have hIP : ∀ μ : (k : ℕ) → Y k → ProbabilityMeasure C, σ.IsMarkovPolicy μ →
      M.IsPolicy (σ.toISI μ) := by
    intro μ hμ
    refine ⟨fun k => BS10Aux.univMeasurable_comp (hμ.1 k) (σ.η_measurable k), fun k hk p i => ?_⟩
    have hU : M.U k i = σ.Uhat k (σ.η k (p, i)) := by
      ext u
      have := congrArg (fun s => (i, u) ∈ s) (σ.Gamma_eq k hk p)
      simpa [GammaSet, SuffStat.Uhat] using this
    change (μ k (σ.η k (p, i)) : Measure C) (M.U k i) = 1
    rw [hU]; exact hμ.2 k hk _
  -- φ(p) is a probability measure
  have hphi : ∀ p : ProbabilityMeasure S, IsProbabilityMeasure (σ.phi p) := by
    intro p
    haveI := M.s0_markov
    unfold SuffStat.phi
    exact Measure.isProbabilityMeasure_map ((σ.η_measurable 0).comp
      (measurable_const.prodMk ((measurable_pi_lambda _ fun _ => measurable_snd).prodMk
        measurable_const))).aemeasurable
  -- eq. (41)
  have h1 : ∀ p : ProbabilityMeasure S, M.optCost p = extIntegral (σ.phi p) σ.optCostHat := by
    intro p
    refine le_antisymm (cor_10_2_1 M σ hF p) ?_
    unfold ISIModel.optCost
    refine le_iInf fun π => ?_
    obtain ⟨μ, hμ, hc⟩ := lemma_10_2 M σ hF p π.1 π.2
    rw [hc]
    refine BS10Aux.extIntegral_mono _ fun y => ?_
    unfold SuffStat.optCostHat
    exact iInf_le (fun ν : {μ // σ.IsPolicy μ} => σ.costHat ν.1 y) ⟨_, hMP μ hμ⟩
  have hcost : ∀ μ : (k : ℕ) → Y k → ProbabilityMeasure C, σ.IsMarkovPolicy μ →
      ∀ p, M.cost (σ.toISI μ) p = extIntegral (σ.phi p) (σ.costHat (markovToPolicy μ)) :=
    fun μ hμ p => prop_10_2 M σ hF p μ hμ
  refine ⟨h1, ?_, ?_, ?_, ?_⟩
  · intro μ hμ hopt p
    refine ⟨hIP μ hμ, ?_⟩
    rw [hcost μ hμ, h1]
    congr 1
    funext y
    exact hopt.2 y
  · intro μ hμ p hq
    refine ⟨hIP μ hμ, ?_⟩
    rw [hcost μ hμ, h1]
    haveI := hphi p
    have hJ := (costHat_univMeasurable M σ hFhat _ (hMP μ hμ) (σ.phi p) (hphi p)).aemeasurable
    have hJs := (optCostHat_univMeasurable M σ hFhat (σ.phi p) (hphi p)).aemeasurable
    exact BS10Aux.extIntegral_congr_ae _
      (BS10Aux.ae_eq_of_measure_eq_one _ _ _ hJs hJ hq.2)
  · intro μ hμ p ε hε hw
    refine ⟨hIP μ hμ, ?_, ?_⟩
    · rw [hcost μ hμ, h1]; exact hw.2.1
    · rw [hcost μ hμ, h1]; exact hw.2.2
  · intro hFp μ hμ ε hε he p
    haveI := hphi p
    have hgt : ∀ y, ⊥ < σ.optCostHat y := optCostHat_gt_bot M σ hFp.2
    have hJs := (optCostHat_univMeasurable M σ hFhat (σ.phi p) (hphi p)).aemeasurable
    have key := BS10Aux.eps_integrate (σ.phi p) σ.optCostHat (σ.costHat (markovToPolicy μ))
      hgt hJs ε hε (fun y => (he.2 y).1 (hgt y))
    refine ⟨hIP μ hμ, ?_, ?_⟩
    · rw [hcost μ hμ, h1]; exact key.1
    · rw [hcost μ hμ, h1]; exact key.2
