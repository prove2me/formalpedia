-- Prove2me | solution 1 for CondPortOT.FiberDual.ball_repr
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T05:29:42.937458+00:00
-- url     : https://prove2.me/submissions/3ad1d297-6dd6-475f-9335-9baf44afcbb9

import Mathlib
import Definitions.Def_CondPortOT_FiberDual_Setting
open MeasureTheory RWPI.SqrtLasso ModelRiskOT.Duality
open scoped NNReal

namespace CondPortOTBallAux

/-- regrouping a sum over samples by distinct atoms. -/
lemma regroup {Ω : Type*} [DecidableEq Ω] {N : ℕ} (z : Fin N → Ω) (F : Ω → ENNReal) :
    ∑ a ∈ Finset.univ.image z, F a =
      ∑ i, ((Finset.univ.filter fun j => z j = z i).card : ENNReal)⁻¹ * F (z i) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image z) (g := z)
    (fun i _ => Finset.mem_image_of_mem z (Finset.mem_univ i))]
  refine Finset.sum_congr rfl fun a ha => ?_
  obtain ⟨i0, -, rfl⟩ := Finset.mem_image.1 ha
  have hcard : ∀ i ∈ Finset.univ.filter (fun i => z i = z i0),
      ((Finset.univ.filter fun j => z j = z i).card : ENNReal)⁻¹ * F (z i) =
      ((Finset.univ.filter fun j => z j = z i0).card : ENNReal)⁻¹ * F (z i0) := by
    intro i hi
    rw [(Finset.mem_filter.1 hi).2]
  rw [Finset.sum_congr rfl hcard, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel, one_mul]
  · have : i0 ∈ Finset.univ.filter (fun j => z j = z i0) := by simp
    exact_mod_cast (Finset.card_pos.2 ⟨i0, this⟩).ne'
  · exact ENNReal.natCast_ne_top _

/-- Decomposition of a coupling whose second marginal is an empirical measure. -/
theorem decomp {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {N : ℕ}
    (z : Fin N → Ω) (π : Measure (Ω × Ω))
    (hπ : π.map Prod.snd = (N : ENNReal)⁻¹ • ∑ i, Measure.dirac (z i)) :
    ∃ πi : Fin N → Measure Ω, (∀ i, πi i Set.univ = (N : ENNReal)⁻¹) ∧
      (∀ g : Ω × Ω → ENNReal, Measurable g →
        ∫⁻ w, g w ∂π = ∑ i, ∫⁻ x, g (x, z i) ∂(πi i)) := by
  classical
  set m : Fin N → ENNReal := fun i => ((Finset.univ.filter fun j => z j = z i).card : ENNReal)
    with hm
  have hm0 : ∀ i, m i ≠ 0 := by
    intro i
    have : i ∈ Finset.univ.filter (fun j => z j = z i) := by simp
    rw [hm]
    exact Nat.cast_ne_zero.2 (Finset.card_pos.2 ⟨i, this⟩).ne'
  have hmt : ∀ i, m i ≠ ⊤ := fun i => ENNReal.natCast_ne_top _
  set π' : Ω → Measure Ω := fun a => (π.restrict (Set.univ ×ˢ {a})).map Prod.fst with hπ'
  refine ⟨fun i => (m i)⁻¹ • π' (z i), ?_, ?_⟩
  · intro i
    have h1 : π (Set.univ ×ˢ {z i}) = (N : ENNReal)⁻¹ * m i := by
      have := congrArg (fun μ : Measure Ω => μ {z i}) hπ
      rw [Measure.map_apply measurable_snd (measurableSet_singleton _)] at this
      have hpre : Prod.snd ⁻¹' ({z i} : Set Ω) = (Set.univ ×ˢ {z i} : Set (Ω × Ω)) := by
        ext w; simp
      rw [hpre] at this
      rw [this, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
      congr 1
      simp only [Measure.dirac_apply' _ (measurableSet_singleton _), Set.indicator_apply,
        Set.mem_singleton_iff, Pi.one_apply]
      rw [Finset.sum_boole]
    simp only [Measure.smul_apply, smul_eq_mul, hπ']
    rw [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, h1, ← mul_assoc,
      mul_comm (m i)⁻¹, mul_assoc, ENNReal.inv_mul_cancel (hm0 i) (hmt i), mul_one]
  · intro g hg
    set S : Finset Ω := Finset.univ.image z with hS
    -- π is concentrated on `univ ×ˢ S`
    have hconc : π (Set.univ ×ˢ (↑S : Set Ω) : Set (Ω × Ω))ᶜ = 0 := by
      have hmeasS : MeasurableSet (↑S : Set Ω) := S.finite_toSet.measurableSet
      have hpre : (Set.univ ×ˢ (↑S : Set Ω) : Set (Ω × Ω))ᶜ = Prod.snd ⁻¹' ((↑S : Set Ω)ᶜ) := by
        ext w; simp
      rw [hpre, ← Measure.map_apply measurable_snd hmeasS.compl, hπ, Measure.smul_apply,
        Measure.coe_finsetSum, Finset.sum_apply]
      rw [Finset.sum_eq_zero fun i _ => ?_, smul_zero]
      rw [Measure.dirac_apply' _ hmeasS.compl, Set.indicator_of_notMem]
      simp [hS]
    have h1 : ∫⁻ w, g w ∂π = ∫⁻ w in Set.univ ×ˢ (↑S : Set Ω), g w ∂π := by
      rw [← lintegral_add_compl _ (MeasurableSet.univ.prod S.finite_toSet.measurableSet),
        setLIntegral_measure_zero _ _ hconc, add_zero]
    have hunion : (Set.univ ×ˢ (↑S : Set Ω) : Set (Ω × Ω)) =
        ⋃ a ∈ S, (Set.univ ×ˢ ({a} : Set Ω) : Set (Ω × Ω)) := by
      ext w; simp
    rw [h1, hunion, lintegral_biUnion_finset]
    rotate_left
    · intro a _ b _ hab
      simp only [Function.onFun]
      rw [Set.disjoint_prod]
      right
      simpa using hab
    · intro a _
      exact MeasurableSet.univ.prod (measurableSet_singleton a)
    have h2 : ∀ a, ∫⁻ w in Set.univ ×ˢ ({a} : Set Ω), g w ∂π = ∫⁻ x, g (x, a) ∂(π' a) := by
      intro a
      have hgm : Measurable fun x : Ω => g (x, a) := hg.comp (measurable_id.prodMk measurable_const)
      show _ = ∫⁻ x, g (x, a) ∂((π.restrict (Set.univ ×ˢ {a})).map Prod.fst)
      rw [lintegral_map hgm measurable_fst]
      refine setLIntegral_congr_fun (MeasurableSet.univ.prod (measurableSet_singleton a)) ?_
      intro w hw
      have : w.2 = a := by simpa using hw.2
      simp [← this]
    simp_rw [h2]
    rw [regroup z (fun a => ∫⁻ x, g (x, a) ∂(π' a))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_smul_measure, smul_eq_mul]



lemma iSup_min_nat (a : ℝ≥0) : (⨆ n : ℕ, ((min a (n : ℝ≥0) : ℝ≥0) : ENNReal)) = (a : ENNReal) := by
  apply le_antisymm
  · exact iSup_le fun n => ENNReal.coe_le_coe.2 (min_le_left _ _)
  · obtain ⟨n, hn⟩ := exists_nat_ge (a : ℝ)
    refine le_iSup_of_le n (ENNReal.coe_le_coe.2 (le_of_eq ?_))
    rw [min_eq_left]
    exact_mod_cast hn

/-- Existence of an optimal coupling for a continuous real cost on a Polish space. -/
lemma optcoup {Z : Type*} [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (g : Z × Z → ℝ) (hg : Continuous g) (Q P : Measure Z) [IsProbabilityMeasure Q]
    [IsProbabilityMeasure P] :
    ∃ π : Measure (Z × Z), IsProbabilityMeasure π ∧ π.map Prod.fst = Q ∧ π.map Prod.snd = P ∧
      ∫⁻ w, ENNReal.ofReal (g w) ∂π ≤
        ⨅ (π' : Measure (Z × Z)) (_ : IsProbabilityMeasure π' ∧ π'.map Prod.fst = Q ∧
          π'.map Prod.snd = P), ∫⁻ w, ENNReal.ofReal (g w) ∂π' := by
  classical
  set Qp : ProbabilityMeasure Z := ⟨Q, inferInstance⟩ with hQp
  set Pp : ProbabilityMeasure Z := ⟨P, inferInstance⟩ with hPp
  set S : Set (ProbabilityMeasure (Z × Z)) :=
    {π | π.map measurable_fst.aemeasurable = Qp ∧ π.map measurable_snd.aemeasurable = Pp} with hS
  have hSc : IsClosed S :=
    (isClosed_eq (ProbabilityMeasure.continuous_map continuous_fst) continuous_const).inter
      (isClosed_eq (ProbabilityMeasure.continuous_map continuous_snd) continuous_const)
  have hfstS : ∀ μ ∈ S, (μ : Measure (Z × Z)).map Prod.fst = Q := by
    intro μ hμ
    have := congrArg ProbabilityMeasure.toMeasure hμ.1
    rwa [ProbabilityMeasure.toMeasure_map] at this
  have hsndS : ∀ μ ∈ S, (μ : Measure (Z × Z)).map Prod.snd = P := by
    intro μ hμ
    have := congrArg ProbabilityMeasure.toMeasure hμ.2
    rwa [ProbabilityMeasure.toMeasure_map] at this
  have hT : IsTightMeasureSet {x | ∃ μ ∈ S, (μ : Measure (Z × Z)) = x} := by
    apply IsTightMeasureSet.prodMk
    · refine (isTightMeasureSet_singleton (μ := Q)).subset ?_
      rintro _ ⟨_, ⟨μ, hμ, rfl⟩, rfl⟩
      exact hfstS μ hμ
    · refine (isTightMeasureSet_singleton (μ := P)).subset ?_
      rintro _ ⟨_, ⟨μ, hμ, rfl⟩, rfl⟩
      exact hsndS μ hμ
  have hK : IsCompact S :=
    (isCompact_closure_of_isTightMeasureSet hT).of_isClosed_subset hSc subset_closure
  have hne : S.Nonempty := by
    refine ⟨Qp.prod Pp, ?_, ?_⟩
    · apply ProbabilityMeasure.toMeasure_injective
      rw [ProbabilityMeasure.toMeasure_map]
      show ((Q.prod P).map Prod.fst) = Q
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    · apply ProbabilityMeasure.toMeasure_injective
      rw [ProbabilityMeasure.toMeasure_map]
      show ((Q.prod P).map Prod.snd) = P
      rw [Measure.map_snd_prod, measure_univ, one_smul]
  -- truncated costs
  let cn : ℕ → BoundedContinuousFunction (Z × Z) ℝ≥0 := fun n =>
    BoundedContinuousFunction.mkOfBound
      ⟨fun w => min (Real.toNNReal (g w)) (n : ℝ≥0), by fun_prop⟩ n (fun x y => by
        rw [NNReal.dist_eq]
        simp only [ContinuousMap.coe_mk, NNReal.coe_min, NNReal.coe_natCast]
        have h1 := min_le_right ((Real.toNNReal (g x) : ℝ)) (n : ℝ)
        have h2 := min_le_right ((Real.toNNReal (g y) : ℝ)) (n : ℝ)
        have h3 : (0 : ℝ) ≤ min ((Real.toNNReal (g x) : ℝ)) (n : ℝ) :=
          le_min (NNReal.coe_nonneg _) (Nat.cast_nonneg n)
        have h4 : (0 : ℝ) ≤ min ((Real.toNNReal (g y) : ℝ)) (n : ℝ) :=
          le_min (NNReal.coe_nonneg _) (Nat.cast_nonneg n)
        rw [abs_sub_le_iff]
        constructor <;> linarith)
  have hcn : ∀ n w, (cn n w : ℝ≥0) = min (Real.toNNReal (g w)) (n : ℝ≥0) := fun n w => rfl
  set F : ProbabilityMeasure (Z × Z) → ENNReal := fun π => ∫⁻ w, ENNReal.ofReal (g w) ∂π with hF
  have hFsup : F = fun π : ProbabilityMeasure (Z × Z) =>
      ⨆ n, ∫⁻ w, ((cn n w : ℝ≥0) : ENNReal) ∂(π : Measure (Z × Z)) := by
    funext π
    simp only [hF]
    rw [← lintegral_iSup]
    · congr 1
      funext w
      simp only [hcn]
      rw [iSup_min_nat]
      rfl
    · intro n
      exact (ENNReal.continuous_coe.comp (cn n).continuous).measurable
    · intro m n hmn w
      simp only [hcn]
      exact ENNReal.coe_le_coe.2 (min_le_min_left _ (by exact_mod_cast hmn))
  have hlsc : LowerSemicontinuous F := by
    rw [hFsup]
    exact lowerSemicontinuous_iSup fun n =>
      (ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction (cn n)).lowerSemicontinuous
  obtain ⟨πs, hπS, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne hK (hlsc.lowerSemicontinuousOn S)
  refine ⟨πs, inferInstance, hfstS πs hπS, hsndS πs hπS, ?_⟩
  refine le_iInf₂ fun π' hπ' => ?_
  obtain ⟨q, hq⟩ : ∃ q : ProbabilityMeasure (Z × Z), (q : Measure (Z × Z)) = π' :=
    ⟨⟨π', hπ'.1⟩, rfl⟩
  have hmem : q ∈ S := by
    refine ⟨?_, ?_⟩
    · apply ProbabilityMeasure.toMeasure_injective
      rw [ProbabilityMeasure.toMeasure_map, hq]
      exact hπ'.2.1
    · apply ProbabilityMeasure.toMeasure_injective
      rw [ProbabilityMeasure.toMeasure_map, hq]
      exact hπ'.2.2
  have := isMinOn_iff.1 hmin q hmem
  simp only [hF] at this
  rw [hq] at this
  exact this

end CondPortOTBallAux

open CondPortOTBallAux in
theorem solution {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ) (hγ : 0 < γ) (hA : CondPortOT.BigRadius.Assumption24 DX DY x0 γ xh)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (Q : Measure (X × Y)) [IsProbabilityMeasure Q] :
    CondPortOT.SingUninf.InBall DX DY xh yh ρ Q ↔
      ∃ π : Fin N → Measure (X × Y), (∀ i, IsProbabilityMeasure (π i)) ∧
        Q = (N : ENNReal)⁻¹ • ∑ i, π i ∧
        (N : ENNReal)⁻¹ * ∑ i, ∫⁻ z, CondPortOT.SingUninf.groundCost DX DY z (xh i, yh i) ∂(π i) ≤ ENNReal.ofReal ρ := by
  classical
  have hNe : (N : ENNReal) ≠ 0 := by exact_mod_cast hN.ne'
  have hNt : (N : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top N
  set z : Fin N → X × Y := fun i => (xh i, yh i) with hz
  have hemp : IsProbabilityMeasure (CondPortOT.SingUninf.empirical xh yh) := by
    constructor
    simp only [CondPortOT.SingUninf.empirical, Measure.smul_apply, Measure.coe_finsetSum,
      Finset.sum_apply, measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hNe hNt
  have hg : Continuous fun w : (X × Y) × (X × Y) => DX w.1.1 w.2.1 + DY w.1.2 w.2.2 :=
    (hA.contX.comp (continuous_fst.fst.prodMk continuous_snd.fst)).add
      (hA.contY.comp (continuous_fst.snd.prodMk continuous_snd.snd))
  have hcm : Measurable fun w : (X × Y) × (X × Y) =>
      CondPortOT.SingUninf.groundCost DX DY w.1 w.2 :=
    ENNReal.measurable_ofReal.comp hg.measurable
  constructor
  · rintro ⟨hQp, hTC⟩
    obtain ⟨πs, hπp, h1, h2, hcost⟩ :=
      optcoup (fun w : (X × Y) × (X × Y) => DX w.1.1 w.2.1 + DY w.1.2 w.2.2) hg Q
        (CondPortOT.SingUninf.empirical xh yh)
    have hcost' : ∫⁻ w, CondPortOT.SingUninf.groundCost DX DY w.1 w.2 ∂πs ≤
        ENNReal.ofReal ρ := le_trans hcost hTC
    obtain ⟨πi, hmass, hint⟩ := decomp z πs (by rw [h2]; rfl)
    have hQB : ∀ B, MeasurableSet B → Q B = ∑ i, πi i B := by
      intro B hB
      rw [← h1, Measure.map_apply measurable_fst hB]
      have h := hint (fun w => B.indicator 1 w.1)
        ((measurable_one.indicator hB).comp measurable_fst)
      have e : (fun w : (X × Y) × (X × Y) => B.indicator (1 : X × Y → ENNReal) w.1) =
          (Prod.fst ⁻¹' B).indicator 1 := by
        ext w; simp [Set.indicator_apply]
      rw [e, lintegral_indicator_one (hB.preimage measurable_fst)] at h
      rw [h]
      exact Finset.sum_congr rfl fun i _ => lintegral_indicator_one hB
    refine ⟨fun i => (N : ENNReal) • πi i, fun i => ⟨?_⟩, ?_, ?_⟩
    · rw [Measure.smul_apply, hmass i, smul_eq_mul, ENNReal.mul_inv_cancel hNe hNt]
    · ext B hB
      rw [hQB B hB, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Measure.smul_apply, smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hNe hNt, one_mul]
    · have h := hint (fun w => CondPortOT.SingUninf.groundCost DX DY w.1 w.2) hcm
      rw [Finset.mul_sum]
      simp only [lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
        ENNReal.inv_mul_cancel hNe hNt, one_mul]
      rw [← h]
      exact hcost'
  · rintro ⟨π, hπp, hQ, hcost⟩
    refine ⟨inferInstance, ?_⟩
    have hmeas : ∀ i, Measurable fun x : X × Y => (x, z i) := fun i =>
      measurable_id.prodMk measurable_const
    let Pc : Measure ((X × Y) × (X × Y)) :=
      (N : ENNReal)⁻¹ • ∑ i, (π i).map (fun x => (x, z i))
    have hPg : ∀ g : (X × Y) × (X × Y) → ENNReal, Measurable g →
        ∫⁻ w, g w ∂Pc = (N : ENNReal)⁻¹ * ∑ i, ∫⁻ x, g (x, z i) ∂(π i) := by
      intro g hgm
      simp only [Pc, lintegral_smul_measure, lintegral_finsetSum_measure, smul_eq_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [lintegral_map hgm (hmeas i)]
    have hPp : IsProbabilityMeasure Pc := by
      constructor
      have h := hPg (fun _ => 1) measurable_const
      simp only [lintegral_const, mul_one, Measure.restrict_univ, one_mul, measure_univ,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
      rw [h]
      exact ENNReal.inv_mul_cancel hNe hNt
    have hP1 : Pc.map Prod.fst = Q := by
      ext B hB
      rw [Measure.map_apply measurable_fst hB, hQ]
      have h := hPg ((Prod.fst ⁻¹' B).indicator 1)
        (measurable_one.indicator (hB.preimage measurable_fst))
      rw [lintegral_indicator_one (hB.preimage measurable_fst)] at h
      rw [h, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have e : (fun x : X × Y => (Prod.fst ⁻¹' B).indicator
          (1 : (X × Y) × (X × Y) → ENNReal) (x, z i)) = B.indicator 1 := by
        ext x; simp [Set.indicator_apply]
      rw [e, lintegral_indicator_one hB]
    have hP2 : Pc.map Prod.snd = CondPortOT.SingUninf.empirical xh yh := by
      ext B hB
      rw [Measure.map_apply measurable_snd hB]
      have h := hPg ((Prod.snd ⁻¹' B).indicator 1)
        (measurable_one.indicator (hB.preimage measurable_snd))
      rw [lintegral_indicator_one (hB.preimage measurable_snd)] at h
      rw [h]
      simp only [CondPortOT.SingUninf.empirical, Measure.smul_apply, Measure.coe_finsetSum,
        Finset.sum_apply, smul_eq_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Measure.dirac_apply' _ hB]
      by_cases hzB : z i ∈ B
      · have e : (fun x : X × Y => (Prod.snd ⁻¹' B).indicator
            (1 : (X × Y) × (X × Y) → ENNReal) (x, z i)) = fun _ => 1 := by
          ext x; simp [Set.indicator_apply, hzB]
        rw [e, lintegral_const, measure_univ, mul_one, Set.indicator_of_mem hzB, Pi.one_apply]
      · have e : (fun x : X × Y => (Prod.snd ⁻¹' B).indicator
            (1 : (X × Y) × (X × Y) → ENNReal) (x, z i)) = fun _ => 0 := by
          ext x; simp [Set.indicator_apply, hzB]
        rw [e, lintegral_zero, Set.indicator_of_notMem hzB]
    unfold RWPI.SqrtLasso.transportCost
    refine le_trans (iInf₂_le Pc ⟨hPp, hP1, hP2⟩) ?_
    rw [hPg _ hcm]
    exact hcost
