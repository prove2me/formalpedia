-- Prove2me | solution 1 for BanditAlgorithm.bayesian_ts_conditional_diagonal_representation
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T04:32:36.295285+00:00
-- url     : https://prove2.me/submissions/d9bb0de9-edde-4993-ae89-02b057979353

import Theorems.Thm_BanditAlgorithm_bayesian_ts_terminal_conditional_laws
import Theorems.Thm_BanditAlgorithm_posterior_diagonal_representation
import Definitions.Def_BayesianTSRoundConditionalGains
import Theorems.Thm_BanditAlgorithm_bayesianAdversarialMeasure_prefix_marginal
import Mathlib.Topology.Order.ProjIcc

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal BigOperators

namespace BanditAlgorithm

private theorem measurable_optimal_bridge {k n : ℕ} [NeZero k] :
    Measurable (bayesianOptimalAction : (Fin n → Fin k → ℝ) → Fin k) := by
  apply measurable_minArgmax.comp
  apply measurable_pi_lambda
  intro a
  exact Finset.measurable_sum Finset.univ fun t _ ↦
    (measurable_pi_apply a).comp (measurable_pi_apply t)

private theorem map_fst_bayesianMeasure_bridge {k n : ℕ}
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (pi : BanditPolicy k) (u : ℕ) (hu : u ≤ n) :
    Measure.map Prod.fst (bayesianAdversarialMeasure Q pi u hu) = Q := by
  have hp := bayesianAdversarialMeasure_prefix_marginal Q pi u hu 0 (Nat.zero_le u)
  have hprefix : Measurable
      (fun p : (Fin n → Fin k → ℝ) × BanditHistory k u ↦
        (p.1, fun s : Fin 0 ↦ p.2 (Fin.castLE (Nat.zero_le u) s))) := by
    apply measurable_fst.prodMk
    apply measurable_pi_lambda
    intro s
    exact s.elim0
  have hm := congrArg (Measure.map (@Prod.fst
    (Fin n → Fin k → ℝ) (BanditHistory k 0))) hp
  rw [Measure.map_map measurable_fst hprefix] at hm
  calc
    Measure.map Prod.fst (bayesianAdversarialMeasure Q pi u hu) =
        Measure.map Prod.fst
          (bayesianAdversarialMeasure Q pi 0 (Nat.zero_le n)) := by
      simpa [Function.comp_def] using hm
    _ = Q := by
      rw [bayesianAdversarialMeasure, Measure.map_map]
      · simp [Function.comp_def]
      · exact measurable_fst
      · exact measurable_id.prodMk measurable_const

private theorem condOptimal_eq_policy_bridge
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    {pi : BanditPolicy k} (hpi : IsBayesianTSPolicy Q pi)
    (t : Fin n) :
    let mu := bayesianAdversarialMeasure Q pi n le_rfl
    let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
    let optimal := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      bayesianOptimalAction p.1
    condDistrib optimal history mu =ᵐ[mu.map history] pi.select t.1 := by
  dsimp only
  apply condDistrib_ae_eq_of_measure_eq_compProd
  · exact (measurable_optimal_bridge.comp measurable_fst).aemeasurable
  · exact hpi t.1 (Nat.le_of_lt t.2)

theorem _root_.solution
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (s : Fin n) (a : Fin k), X s a ∈ Set.Icc (0 : ℝ) 1)
    {pi : BanditPolicy k} (hpi : IsBayesianTSPolicy Q pi) (t : Fin n) :
    let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
    let nu := Measure.map history (bayesianAdversarialMeasure Q pi n le_rfl)
    ∀ᵐ h ∂nu, ∃ (p : Fin k → ℝ)
      (P M : Fin k → Measure (Set.Icc (0 : ℝ) 1)),
      (∀ a, IsProbabilityMeasure (P a)) ∧
      (∀ a, IsProbabilityMeasure (M a)) ∧
      (∀ a, klDiv (P a) (M a) ≠ ∞) ∧
      bayesianTSRoundConditionalRegretGain Q pi t h =
        ∑ a, p a * ((∫ z, z.1 ∂P a) - ∫ z, z.1 ∂M a) ∧
      (∑ a, p a ^ 2 * (klDiv (P a) (M a)).toReal) ≤
        bayesianTSRoundConditionalInformationGain Q pi t h := by
  dsimp only
  let mu := bayesianAdversarialMeasure Q pi n le_rfl
  let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
  let nu := Measure.map history mu
  let base := bayesianAdversarialMeasure Q pi t.1 (Nat.le_of_lt t.2)
  let nuBase := Measure.map Prod.snd base
  let Rker := condDistrib Prod.fst Prod.snd base
  let optimalX := bayesianOptimalAction (k := k) (n := n)
  let B : Set (Fin n → Fin k → ℝ) :=
    {X | ∀ (s : Fin n) (a : Fin k), X s a ∈ Set.Icc (0 : ℝ) 1}
  have hhistory : Measurable history := by
    apply measurable_pi_lambda
    intro s
    exact (measurable_pi_apply (Fin.castLE (Nat.le_of_lt t.2) s)).comp measurable_snd
  have hB : MeasurableSet B := by
    rw [show B = ⋂ s : Fin n, ⋂ a : Fin k,
        {X | X s a ∈ Set.Icc (0 : ℝ) 1} by
      ext X
      simp [B]]
    exact MeasurableSet.iInter fun s ↦ MeasurableSet.iInter fun a ↦
      measurableSet_Icc.preimage
        ((measurable_pi_apply a).comp (measurable_pi_apply s))
  have hbaseBound : ∀ᵐ z ∂base, z.1 ∈ B := by
    apply (ae_map_iff measurable_fst.aemeasurable hB).mp
    rw [map_fst_bayesianMeasure_bridge Q pi t.1 (Nat.le_of_lt t.2)]
    exact hQ
  have hdisBase : nuBase ⊗ₘ Rker = Measure.map Prod.swap base := by
    dsimp [nuBase, Rker]
    exact compProd_map_condDistrib measurable_fst.aemeasurable
  have hpostBoundBase : ∀ᵐ h ∂nuBase, ∀ᵐ X ∂Rker h, X ∈ B := by
    have hswap : ∀ᵐ z ∂Measure.map Prod.swap base, z.2 ∈ B := by
      apply (ae_map_iff measurable_swap.aemeasurable
        (hB.preimage measurable_snd)).mpr
      simpa using hbaseBound
    rw [← hdisBase] at hswap
    exact Measure.ae_ae_of_ae_compProd hswap
  have hnu : nu = nuBase := by
    have hp := bayesianAdversarialMeasure_prefix_marginal Q pi n le_rfl
      t.1 (Nat.le_of_lt t.2)
    have hprefix : Measurable
        (fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
          (p.1, history p)) := measurable_fst.prodMk hhistory
    have hm := congrArg (Measure.map (@Prod.snd
      (Fin n → Fin k → ℝ) (BanditHistory k t.1))) hp
    rw [Measure.map_map measurable_snd hprefix] at hm
    simpa [nu, nuBase, Function.comp_def] using hm
  have hpostBound : ∀ᵐ h ∂nu, ∀ᵐ X ∂Rker h, X ∈ B := by
    rw [hnu]
    exact hpostBoundBase
  have hlaws := bayesian_ts_terminal_conditional_laws Q pi t
  dsimp only at hlaws
  rcases hlaws with ⟨hmat, haction, hrecorded⟩
  have hcondOpt := condOptimal_eq_policy_bridge Q hpi t
  have hoptComp :
      condDistrib (fun z : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
          optimalX z.1) history mu =ᵐ[nu]
        (condDistrib Prod.fst history mu).map optimalX := by
    simpa [nu, Function.comp_def] using
      (condDistrib_comp history measurable_fst.aemeasurable
        (measurable_optimal_bridge (k := k) (n := n)))
  have hqPolicy : ∀ᵐ h ∂nu,
      Measure.map optimalX (Rker h) = pi.select t.1 h := by
    filter_upwards [hmat, hcondOpt, hoptComp] with h hm ho hc
    rw [← hm]
    rw [Kernel.map_apply _ (measurable_optimal_bridge (k := k) (n := n)) h] at hc
    exact hc.symm.trans ho
  let xa := fun z : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    (z.1, (z.2 t).1)
  have hxa : Measurable xa := measurable_fst.prodMk
    (measurable_fst.comp ((measurable_pi_apply t).comp measurable_snd))
  have hxaComp : condDistrib xa history mu =ᵐ[nu]
      (condDistrib id history mu).map xa := by
    simpa [nu, Function.comp_def] using
      (condDistrib_comp history aemeasurable_id hxa)
  let obsReal := fun z : (Fin n → Fin k → ℝ) × Fin k ↦
    (z.2, z.1 t z.2)
  let optXA := fun z : (Fin n → Fin k → ℝ) × Fin k ↦ optimalX z.1
  have hobsReal : Measurable obsReal := by
    apply measurable_from_prod_countable_left
    intro a
    exact measurable_const.prodMk
      ((measurable_pi_apply a).comp (measurable_pi_apply t))
  have hoptXA : Measurable optXA := measurable_optimal_bridge.comp measurable_fst
  have hjointRealComp :
      condDistrib (fun z ↦ (optXA (xa z), obsReal (xa z))) history mu =ᵐ[nu]
        (condDistrib xa history mu).map (fun z ↦ (optXA z, obsReal z)) := by
    simpa [nu, Function.comp_def] using
      (condDistrib_comp history hxa.aemeasurable (hoptXA.prodMk hobsReal))
  have hobsRealComp : condDistrib (fun z ↦ obsReal (xa z)) history mu =ᵐ[nu]
      (condDistrib xa history mu).map obsReal := by
    simpa [nu, Function.comp_def] using
      (condDistrib_comp history hxa.aemeasurable hobsReal)
  have hoptXAComp : condDistrib (fun z ↦ optXA (xa z)) history mu =ᵐ[nu]
      (condDistrib xa history mu).map optXA := by
    simpa [nu, Function.comp_def] using
      (condDistrib_comp history hxa.aemeasurable hoptXA)
  have hobsRecorded :
      (fun z ↦ obsReal (xa z)) =ᵐ[mu]
        (fun z : (Fin n → Fin k → ℝ) × BanditHistory k n ↦ z.2 t) := by
    filter_upwards [hrecorded] with z hz
    simpa [obsReal, xa] using hz.symm
  have hjointRecorded :
      (fun z ↦ (optXA (xa z), obsReal (xa z))) =ᵐ[mu]
        (fun z : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
          (bayesianOptimalAction z.1, z.2 t)) := by
    filter_upwards [hrecorded] with z hz
    change (optimalX z.1, ((z.2 t).1, z.1 t (z.2 t).1)) =
      (optimalX z.1, z.2 t)
    exact congrArg (fun o ↦ (optimalX z.1, o)) hz.symm
  have hcondObsRecorded :
      condDistrib (fun z ↦ obsReal (xa z)) history mu =
        condDistrib (fun z : (Fin n → Fin k → ℝ) × BanditHistory k n ↦ z.2 t)
          history mu :=
    condDistrib_congr_left hobsRecorded
  have hcondJointRecorded :
      condDistrib (fun z ↦ (optXA (xa z), obsReal (xa z))) history mu =
        condDistrib (fun z : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
          (bayesianOptimalAction z.1, z.2 t)) history mu :=
    condDistrib_congr_left hjointRecorded
  filter_upwards [hpostBound, hqPolicy, haction, hxaComp, hjointRealComp,
    hobsRealComp, hoptXAComp] with h hbound hq hact hxc hjc hoc hpc
  let clip : ℝ → Set.Icc (0 : ℝ) 1 := Set.projIcc 0 1 zero_le_one
  let reward : Fin k → (Fin n → Fin k → ℝ) → Set.Icc (0 : ℝ) 1 :=
    fun a X ↦ clip (X t a)
  have hreward : ∀ a, Measurable (reward a) := by
    intro a
    exact continuous_projIcc.measurable.comp
      ((measurable_pi_apply a).comp (measurable_pi_apply t))
  letI : IsProbabilityMeasure (Rker h) := by infer_instance
  have hd := posterior_diagonal_representation (Rker h) optimalX
    (measurable_optimal_bridge (k := k) (n := n)) reward hreward
  rcases hd with ⟨p, P, M, hP, hM, hfinite, hregret, hinfo⟩
  refine ⟨p, P, M, hP, hM, hfinite, ?_, ?_⟩
  · let q := Measure.map optimalX (Rker h)
    letI : IsProbabilityMeasure q := by
      dsimp [q]
      exact Measure.isProbabilityMeasure_map
        (measurable_optimal_bridge (k := k) (n := n)).aemeasurable
    let rho := (Rker h).prod q
    let g : (Fin n → Fin k → ℝ) × Fin k → ℝ := fun z ↦
      z.1 t (optimalX z.1) - z.1 t z.2
    let gclip : (Fin n → Fin k → ℝ) × Fin k → ℝ := fun z ↦
      (reward (optimalX z.1) z.1).1 - (reward z.2 z.1).1
    have hg : Measurable g := by
      have heval : Measurable
          (fun z : (Fin n → Fin k → ℝ) × Fin k ↦ z.1 t z.2) :=
        measurable_from_prod_countable_left fun a ↦
          (measurable_pi_apply a).comp (measurable_pi_apply t)
      exact (heval.comp (measurable_fst.prodMk
        (measurable_optimal_bridge.comp measurable_fst))).sub heval
    have hbprod : ∀ᵐ z ∂rho, z.1 ∈ B := by
      apply (ae_map_iff measurable_fst.aemeasurable hB).mp
      rw [show Measure.map Prod.fst rho = Rker h by simp [rho]]
      exact hbound
    have hclipEq : g =ᵐ[rho] gclip := by
      filter_upwards [hbprod] with z hz
      have ho := hz t (optimalX z.1)
      have ha := hz t z.2
      simp [g, gclip, reward, clip, Set.projIcc_of_mem, ho, ha]
    rw [Kernel.map_apply _ hxa h] at hxc
    simp_rw [Kernel.prod_apply] at hact
    change (∫ z, g (xa z) ∂condDistrib id history mu h) = _
    calc
      (∫ z, g (xa z) ∂condDistrib id history mu h) =
          ∫ z, g z ∂Measure.map xa (condDistrib id history mu h) := by
        exact (MeasureTheory.integral_map hxa.aemeasurable hg.aestronglyMeasurable).symm
      _ = ∫ z, g z ∂condDistrib xa history mu h := by rw [hxc]
      _ = ∫ z, g z ∂(Rker h).prod (pi.select t.1 h) := by rw [hact]
      _ = ∫ z, g z ∂rho := by rw [← hq]
      _ = ∫ z, gclip z ∂rho := MeasureTheory.integral_congr_ae hclipEq
      _ = ∑ a, p a * ((∫ z, z.1 ∂P a) - ∫ z, z.1 ∂M a) := by
        exact hregret
  · let q := Measure.map optimalX (Rker h)
    letI : IsProbabilityMeasure q := by
      dsimp [q]
      exact Measure.isProbabilityMeasure_map
        (measurable_optimal_bridge (k := k) (n := n)).aemeasurable
    let rho := (Rker h).prod q
    let obsClip := fun z : (Fin n → Fin k → ℝ) × Fin k ↦
      (z.2, reward z.2 z.1)
    let jointClip := fun z : (Fin n → Fin k → ℝ) × Fin k ↦
      (optimalX z.1, obsClip z)
    have hobsClip : Measurable obsClip := by
      apply measurable_from_prod_countable_left
      intro a
      exact measurable_const.prodMk (hreward a)
    have hjointClip : Measurable jointClip :=
      (measurable_optimal_bridge.comp measurable_fst).prodMk hobsClip
    rw [Kernel.map_apply _ (hoptXA.prodMk hobsReal) h] at hjc
    rw [Kernel.map_apply _ hobsReal h] at hoc
    rw [Kernel.map_apply _ hoptXA h] at hpc
    simp_rw [Kernel.prod_apply] at hact
    have hcondXA : condDistrib xa history mu h =
        (Rker h).prod (pi.select t.1 h) := by
      simpa [xa, history, mu, Rker, base] using hact
    have hjReal :
        condDistrib (fun z ↦ (optXA (xa z), obsReal (xa z))) history mu h =
          Measure.map (fun z ↦ (optXA z, obsReal z)) rho := by
      rw [hjc, hcondXA, ← hq]
    have hoReal : condDistrib (fun z ↦ obsReal (xa z)) history mu h =
        Measure.map obsReal rho := by rw [hoc, hcondXA, ← hq]
    have hpReal : condDistrib (fun z ↦ optXA (xa z)) history mu h =
        Measure.map optXA rho := by rw [hpc, hcondXA, ← hq]
    have hmapOpt : Measure.map optXA rho = q := by
      rw [show optXA = optimalX ∘ Prod.fst by rfl,
        ← Measure.map_map (measurable_optimal_bridge (k := k) (n := n)) measurable_fst]
      simp [rho, q]
      exact Measure.map_congr (Filter.Eventually.of_forall fun X ↦ rfl)
    have hbprod : ∀ᵐ z ∂rho, z.1 ∈ B := by
      apply (ae_map_iff measurable_fst.aemeasurable hB).mp
      rw [show Measure.map Prod.fst rho = Rker h by simp [rho]]
      exact hbound
    let embedObs : (Fin k × Set.Icc (0 : ℝ) 1) → (Fin k × ℝ) :=
      Prod.map id Subtype.val
    let embedJoint : (Fin k × (Fin k × Set.Icc (0 : ℝ) 1)) →
        (Fin k × (Fin k × ℝ)) := Prod.map id embedObs
    have heSub : MeasurableEmbedding
        ((↑) : Set.Icc (0 : ℝ) 1 → ℝ) :=
      MeasurableEmbedding.subtype_coe measurableSet_Icc
    have heObs : MeasurableEmbedding embedObs := by
      exact MeasurableEmbedding.id.prodMap heSub
    have heJoint : MeasurableEmbedding embedJoint := by
      exact MeasurableEmbedding.id.prodMap heObs
    have hmapObs : Measure.map embedObs (Measure.map obsClip rho) =
        Measure.map obsReal rho := by
      rw [Measure.map_map heObs.measurable hobsClip]
      apply Measure.map_congr
      filter_upwards [hbprod] with z hz
      have ha := hz t z.2
      simp [embedObs, obsClip, obsReal, reward, clip, Set.projIcc_of_mem, ha]
    have hmapJoint : Measure.map embedJoint (Measure.map jointClip rho) =
        Measure.map (fun z ↦ (optXA z, obsReal z)) rho := by
      rw [Measure.map_map heJoint.measurable hjointClip]
      apply Measure.map_congr
      filter_upwards [hbprod] with z hz
      have ha := hz t z.2
      simp [embedJoint, embedObs, jointClip, obsClip, optXA, obsReal,
        reward, clip, Set.projIcc_of_mem, ha]
    have hmapRef : Measure.map embedJoint (q.prod (Measure.map obsClip rho)) =
        q.prod (Measure.map obsReal rho) := by
      rw [show embedJoint = Prod.map id embedObs by rfl, ←
        Measure.map_prod_map q (Measure.map obsClip rho) measurable_id heObs.measurable,
        Measure.map_id, hmapObs]
    have hKL := InformationTheory.klDiv_map_measurableEmbedding heJoint
      (Measure.map jointClip rho) (q.prod (Measure.map obsClip rho))
    rw [hmapJoint, hmapRef] at hKL
    have hres : (∑ a, p a ^ 2 * (klDiv (P a) (M a)).toReal) ≤
        (klDiv
        (condDistrib (fun z ↦ (optXA (xa z), obsReal (xa z))) history mu h)
        ((condDistrib (fun z ↦ optXA (xa z)) history mu h).prod
          (condDistrib (fun z ↦ obsReal (xa z)) history mu h))).toReal := by
      rw [hjReal, hpReal, hoReal, hmapOpt, hKL]
      exact hinfo
    rw [hcondJointRecorded, hcondObsRecorded] at hres
    simpa [bayesianTSRoundConditionalInformationGain, optXA, xa, obsReal,
      history, mu, optimalX] using hres

end BanditAlgorithm
