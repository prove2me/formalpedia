-- Prove2me | solution 1 for CondPortOT.FiberDual.proposition_2_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T05:09:24.896794+00:00
-- url     : https://prove2.me/submissions/a7154d23-c963-4087-9083-91edc50cb451

import Mathlib
import Definitions.Def_CondPortOT_FiberDual_Setting
open MeasureTheory RWPI.SqrtLasso ModelRiskOT.Duality

namespace CondPortOTP25Aux

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



section Geo

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

lemma fiber_meas (DX : X → X → ℝ) (x0 : X) (γ : ℝ)
    (hDXc : Continuous fun p : X × X => DX p.1 p.2) :
    MeasurableSet (CondPortOT.SingUninf.fiber (Y := Y) DX x0 γ) := by
  have hc : Continuous fun x : X => DX x x0 := hDXc.comp (continuous_id.prodMk continuous_const)
  have : IsClosed (CondPortOT.SingUninf.nbhd DX x0 γ) := isClosed_le hc continuous_const
  exact this.measurableSet.prod MeasurableSet.univ

lemma mem_fiber (DX : X → X → ℝ) (x0 : X) (γ : ℝ) (w : X × Y) :
    w ∈ CondPortOT.SingUninf.fiber DX x0 γ ↔ w.1 ∈ CondPortOT.SingUninf.nbhd DX x0 γ := by
  simp [CondPortOT.SingUninf.fiber]

lemma groundCost_meas (DX : X → X → ℝ) (DY : Y → Y → ℝ)
    (hDXc : Continuous fun p : X × X => DX p.1 p.2) (hDYc : Continuous fun p : Y × Y => DY p.1 p.2) :
    Measurable fun w : (X × Y) × (X × Y) => CondPortOT.SingUninf.groundCost DX DY w.1 w.2 := by
  unfold CondPortOT.SingUninf.groundCost
  refine ENNReal.measurable_ofReal.comp (Measurable.add ?_ ?_)
  · exact hDXc.measurable.comp (measurable_fst.fst.prodMk measurable_snd.fst)
  · exact hDYc.measurable.comp (measurable_fst.snd.prodMk measurable_snd.snd)


/-- Lower bound: every coupling of a measure with fiber mass `≥ ε` costs at least the LP value. -/
lemma lower (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X)
    (yh : Fin N → Y) (x0 : X) (γ : ℝ) (hA : CondPortOT.BigRadius.Assumption24 DX DY x0 γ xh)
    (ε : ℝ) (Q : Measure (X × Y)) (π : Measure ((X × Y) × (X × Y)))
    (hπ1 : π.map Prod.fst = Q) (hπ2 : π.map Prod.snd = CondPortOT.SingUninf.empirical xh yh)
    (hQε : ENNReal.ofReal ε ≤ Q (CondPortOT.SingUninf.fiber DX x0 γ)) :
    ∃ υ : Fin N → ℝ, (∀ i, υ i ∈ Set.Icc (0 : ℝ) 1) ∧ (N : ℝ) * ε ≤ ∑ i, υ i ∧
      ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ i, CondPortOT.SingUninf.kappa DX x0 γ xh i * υ i) ≤
        ∫⁻ w, CondPortOT.SingUninf.groundCost DX DY w.1 w.2 ∂π := by
  classical
  set F := CondPortOT.SingUninf.fiber (Y := Y) DX x0 γ with hF
  set κ := CondPortOT.SingUninf.kappa DX x0 γ xh with hκ
  have hFm : MeasurableSet F := fiber_meas DX x0 γ hA.contX
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hκnn : ∀ i, 0 ≤ κ i := fun i =>
    Real.sInf_nonneg (by rintro _ ⟨x, _, rfl⟩; exact hA.nonnegX _ _)
  obtain ⟨πi, hmass, hint⟩ := decomp (fun i => (xh i, yh i)) π (by rw [hπ2]; rfl)
  have hQB : ∀ B, MeasurableSet B → Q B = ∑ i, πi i B := by
    intro B hB
    rw [← hπ1, Measure.map_apply measurable_fst hB]
    have h := hint (fun w => B.indicator 1 w.1) ((measurable_one.indicator hB).comp measurable_fst)
    have e : (fun w : (X × Y) × (X × Y) => B.indicator (1 : X × Y → ENNReal) w.1) =
        (Prod.fst ⁻¹' B).indicator 1 := by
      ext w; simp [Set.indicator_apply]
    rw [e, lintegral_indicator_one (hB.preimage measurable_fst)] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => lintegral_indicator_one hB
  have hNinv : (N : ENNReal)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (by exact_mod_cast hN.ne')
  have hπfin : ∀ i, πi i F ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (by rw [hmass i]; exact hNinv) (measure_mono (Set.subset_univ _))
  have hle : ∀ i, (πi i F).toReal ≤ (N : ℝ)⁻¹ := by
    intro i
    have := ENNReal.toReal_mono (by rw [hmass i]; exact hNinv) (measure_mono (μ := πi i)
      (Set.subset_univ F))
    rwa [hmass i, ENNReal.toReal_inv, ENNReal.toReal_natCast] at this
  refine ⟨fun i => (N : ℝ) * (πi i F).toReal, fun i => ⟨by positivity, ?_⟩, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left (hle i) hNpos.le
    rwa [mul_inv_cancel₀ hNpos.ne'] at this
  · have hQF := hQB F hFm
    have hQtop : Q F ≠ ⊤ := by rw [hQF]; exact ENNReal.sum_ne_top.2 fun i _ => hπfin i
    have hQR : (Q F).toReal = ∑ i, (πi i F).toReal := by
      rw [hQF, ENNReal.toReal_sum fun i _ => hπfin i]
    have hε' : ε ≤ (Q F).toReal := by
      rcases le_or_gt ε 0 with h | h
      · exact le_trans h ENNReal.toReal_nonneg
      · exact (ENNReal.ofReal_le_iff_le_toReal hQtop).1 hQε
    rw [← Finset.mul_sum, ← hQR]
    exact mul_le_mul_of_nonneg_left hε' hNpos.le
  · rw [hint _ (groundCost_meas DX DY hA.contX hA.contY)]
    have hpt : ∀ i, ENNReal.ofReal (κ i) * πi i F ≤
        ∫⁻ x, CondPortOT.SingUninf.groundCost DX DY x (xh i, yh i) ∂(πi i) := by
      intro i
      rw [← setLIntegral_const, ← lintegral_indicator hFm]
      refine lintegral_mono fun x => ?_
      by_cases hx : x ∈ F
      · rw [Set.indicator_of_mem hx]
        unfold CondPortOT.SingUninf.groundCost
        apply ENNReal.ofReal_le_ofReal
        have hx1 := (mem_fiber DX x0 γ x).1 hx
        have : κ i ≤ DX x.1 (xh i) :=
          csInf_le ⟨0, by rintro _ ⟨x, _, rfl⟩; exact hA.nonnegX _ _⟩ ⟨x.1, hx1, rfl⟩
        linarith [hA.nonnegY x.2 (yh i)]
      · rw [Set.indicator_of_notMem hx]; exact zero_le
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun i _ => hpt i)
    have e : (N : ℝ)⁻¹ * ∑ i, κ i * ((N : ℝ) * (πi i F).toReal) = ∑ i, κ i * (πi i F).toReal := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by field_simp
    simp only []
    rw [e, ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hκnn i) ENNReal.toReal_nonneg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_mul (hκnn i), ENNReal.ofReal_toReal (hπfin i)]


/-- Upper bound: moving a share `υᵢ` of each sample to its projection. -/
lemma qstar (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X)
    (yh : Fin N → Y) (x0 : X) (γ : ℝ) (hA : CondPortOT.BigRadius.Assumption24 DX DY x0 γ xh)
    (ε : ℝ) (υ : Fin N → ℝ) (hυ : ∀ i, υ i ∈ Set.Icc (0 : ℝ) 1) (hυs : (N : ℝ) * ε ≤ ∑ i, υ i) :
    ∃ Q : Measure (X × Y), IsProbabilityMeasure Q ∧
      RWPI.SqrtLasso.transportCost (CondPortOT.SingUninf.groundCost DX DY) Q
        (CondPortOT.SingUninf.empirical xh yh) ≤
        ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ i, CondPortOT.SingUninf.kappa DX x0 γ xh i * υ i) ∧
      ENNReal.ofReal ε ≤ Q (CondPortOT.SingUninf.fiber DX x0 γ) := by
  classical
  set F := CondPortOT.SingUninf.fiber (Y := Y) DX x0 γ with hF
  set nb := CondPortOT.SingUninf.nbhd DX x0 γ with hnb
  set κ := CondPortOT.SingUninf.kappa DX x0 γ xh with hκ
  have hFm : MeasurableSet F := fiber_meas DX x0 γ hA.contX
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hDYself : ∀ i, DY (yh i) (yh i) = 0 := fun i => by
    have h := (hA.eq_zero_iff (xh i) (xh i) (yh i) (yh i)).2 rfl
    linarith [hA.nonnegX (xh i) (xh i), hA.nonnegY (yh i) (yh i)]
  have hDXself : ∀ i, DX (xh i) (xh i) = 0 := fun i => by
    have h := (hA.eq_zero_iff (xh i) (xh i) (yh i) (yh i)).2 rfl
    linarith [hA.nonnegX (xh i) (xh i), hA.nonnegY (yh i) (yh i)]
  have hκnn : ∀ i, 0 ≤ κ i := fun i =>
    Real.sInf_nonneg (by rintro _ ⟨x, _, rfl⟩; exact hA.nonnegX _ _)
  have hproj : ∀ i, ∃ xp, xp ∈ nb ∧ ∀ x ∈ nb, DX xp (xh i) ≤ DX x (xh i) :=
    fun i => (hA.proj i).exists
  choose xp hxp_mem hxp_min using hproj
  have hxp_κ : ∀ i, DX (xp i) (xh i) = κ i := by
    intro i
    rw [hκ]
    symm
    exact IsLeast.csInf_eq ⟨⟨xp i, hxp_mem i, rfl⟩, by
      rintro _ ⟨x, hx, rfl⟩; exact hxp_min i x hx⟩
  set z : Fin N → X × Y := fun i => (xh i, yh i) with hz
  let π : Measure ((X × Y) × (X × Y)) := (N : ENNReal)⁻¹ • ∑ i,
    (ENNReal.ofReal (υ i) • Measure.dirac ((xp i, yh i), z i) +
      ENNReal.ofReal (1 - υ i) • Measure.dirac (z i, z i))
  have hπg : ∀ g : (X × Y) × (X × Y) → ENNReal, ∫⁻ u, g u ∂π = (N : ENNReal)⁻¹ * ∑ i,
      (ENNReal.ofReal (υ i) * g ((xp i, yh i), z i) + ENNReal.ofReal (1 - υ i) * g (z i, z i)) := by
    intro g
    simp only [π, lintegral_smul_measure, lintegral_finsetSum_measure, lintegral_add_measure,
      lintegral_dirac, smul_eq_mul]
  have hsum1 : ∀ i, ENNReal.ofReal (υ i) + ENNReal.ofReal (1 - υ i) = 1 := by
    intro i
    rw [← ENNReal.ofReal_add (hυ i).1 (by linarith [(hυ i).2])]
    simp
  have hNinv : (N : ENNReal)⁻¹ * N = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top _)
  have hπprob : IsProbabilityMeasure π := by
    constructor
    have := hπg (fun _ => 1)
    simp only [lintegral_const, mul_one, Measure.restrict_univ, one_mul] at this
    rw [this, Finset.sum_congr rfl fun i _ => hsum1 i]
    simp [hNinv]
  have hπ2 : π.map Prod.snd = CondPortOT.SingUninf.empirical xh yh := by
    ext B hB
    rw [Measure.map_apply measurable_snd hB]
    have h := hπg ((Prod.snd ⁻¹' B).indicator 1)
    rw [lintegral_indicator_one (hB.preimage measurable_snd)] at h
    rw [h]
    simp only [CondPortOT.SingUninf.empirical, Measure.smul_apply, Measure.coe_finsetSum,
      Finset.sum_apply, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply, mul_ite, mul_one, mul_zero]
    rw [Measure.dirac_apply' _ hB]
    by_cases hzB : (xh i, yh i) ∈ B
    · simp only [hz, hzB, if_true]
      rw [Set.indicator_of_mem hzB, Pi.one_apply]
      exact hsum1 i
    · simp only [hz, hzB, if_false, add_zero]
      rw [Set.indicator_of_notMem hzB]
  refine ⟨π.map Prod.fst, Measure.isProbabilityMeasure_map measurable_fst.aemeasurable, ?_, ?_⟩
  · unfold RWPI.SqrtLasso.transportCost
    refine le_trans (iInf₂_le π ⟨hπprob, rfl, hπ2⟩) (le_of_eq ?_)
    rw [hπg]
    simp only [CondPortOT.SingUninf.groundCost, hz, hDXself, hDYself, add_zero, hxp_κ,
      ENNReal.ofReal_zero, mul_zero]
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hNpos.le), ENNReal.ofReal_inv_of_pos hNpos,
      ENNReal.ofReal_natCast, ENNReal.ofReal_sum_of_nonneg fun i _ =>
        mul_nonneg (hκnn i) (hυ i).1]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ENNReal.ofReal_mul (hυ i).1, mul_comm]
  · rw [Measure.map_apply measurable_fst hFm]
    have h := hπg ((Prod.fst ⁻¹' F).indicator 1)
    rw [lintegral_indicator_one (hFm.preimage measurable_fst)] at h
    rw [h]
    have hin : ∀ i, ((xp i, yh i), z i) ∈ Prod.fst ⁻¹' F := fun i =>
      (mem_fiber DX x0 γ (xp i, yh i)).2 (hxp_mem i)
    have hlow : ∀ i, ENNReal.ofReal (υ i) ≤ ENNReal.ofReal (υ i) *
        (Prod.fst ⁻¹' F).indicator 1 ((xp i, yh i), z i) +
        ENNReal.ofReal (1 - υ i) * (Prod.fst ⁻¹' F).indicator 1 (z i, z i) := by
      intro i
      rw [Set.indicator_of_mem (hin i), Pi.one_apply, mul_one]
      exact le_self_add
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hlow i) zero_le)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (hυ i).1),
      show (N : ENNReal)⁻¹ = ENNReal.ofReal ((N : ℝ)⁻¹) by
        rw [ENNReal.ofReal_inv_of_pos hNpos, ENNReal.ofReal_natCast],
      ← ENNReal.ofReal_mul (inv_nonneg.2 hNpos.le)]
    apply ENNReal.ofReal_le_ofReal
    rw [le_inv_mul_iff₀ hNpos]
    linarith

end Geo

end CondPortOTP25Aux

open CondPortOTP25Aux in
theorem solution {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ) (hγ : 0 ≤ γ) (hA : CondPortOT.BigRadius.Assumption24 DX DY x0 γ xh)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∃ v : ℝ,
      IsLeast {r : ℝ | ∃ υ : Fin N → ℝ, (∀ i, υ i ∈ Set.Icc (0 : ℝ) 1) ∧
        (N : ℝ) * ε ≤ ∑ i, υ i ∧ r = (N : ℝ)⁻¹ * ∑ i, CondPortOT.SingUninf.kappa DX x0 γ xh i * υ i} v ∧
      CondPortOT.SingDual.rhoMin DX DY xh yh x0 γ ε = ENNReal.ofReal v) ∧
    ∀ ρ : ℝ, 0 ≤ ρ →
      ((∃ Q : Measure (X × Y), CondPortOT.SingUninf.InBall DX DY xh yh ρ Q ∧ ENNReal.ofReal ε ≤ Q (CondPortOT.SingUninf.fiber DX x0 γ)) ↔
        CondPortOT.SingDual.rhoMin DX DY xh yh x0 γ ε ≤ ENNReal.ofReal ρ) := by
  classical
  set κ := CondPortOT.SingUninf.kappa DX x0 γ xh with hκ
  set f : (Fin N → ℝ) → ℝ := fun υ => (N : ℝ)⁻¹ * ∑ i, κ i * υ i with hf
  set K : Set (Fin N → ℝ) := Set.Icc 0 1 ∩ {υ | (N : ℝ) * ε ≤ ∑ i, υ i} with hK
  have hKc : IsCompact K := isCompact_Icc.inter_right
    (isClosed_le continuous_const (continuous_finsetSum _ fun i _ => continuous_apply i))
  have hKne : K.Nonempty := ⟨1, ⟨⟨fun _ => zero_le_one, le_rfl⟩, by
    show (N : ℝ) * ε ≤ ∑ i, (1 : Fin N → ℝ) i
    simp only [Pi.one_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    exact mul_le_of_le_one_right (by positivity) hε1⟩⟩
  have hfc : Continuous f := continuous_const.mul
    (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))
  obtain ⟨υs, hυsK, hmin⟩ := hKc.exists_isMinOn hKne hfc.continuousOn
  have hmemK : ∀ υ : Fin N → ℝ, (∀ i, υ i ∈ Set.Icc (0 : ℝ) 1) → (N : ℝ) * ε ≤ ∑ i, υ i →
      υ ∈ K := fun υ h1 h2 => ⟨⟨fun i => (h1 i).1, fun i => (h1 i).2⟩, h2⟩
  have hυs : ∀ i, υs i ∈ Set.Icc (0 : ℝ) 1 := fun i => ⟨hυsK.1.1 i, hυsK.1.2 i⟩
  have hυss : (N : ℝ) * ε ≤ ∑ i, υs i := hυsK.2
  set v := f υs with hv
  have hlow : ENNReal.ofReal v ≤ CondPortOT.SingDual.rhoMin DX DY xh yh x0 γ ε := by
    unfold CondPortOT.SingDual.rhoMin
    refine le_iInf₂ fun Q hQ => ?_
    unfold RWPI.SqrtLasso.transportCost
    refine le_iInf₂ fun π hπ => ?_
    obtain ⟨υ, h1, h2, h3⟩ := lower DX DY hN xh yh x0 γ hA ε Q π hπ.2.1 hπ.2.2 hQ.2
    exact le_trans (ENNReal.ofReal_le_ofReal (hmin (hmemK υ h1 h2))) h3
  obtain ⟨Qs, hQsp, hQsc, hQsF⟩ := qstar DX DY hN xh yh x0 γ hA ε υs hυs hυss
  have hup : CondPortOT.SingDual.rhoMin DX DY xh yh x0 γ ε ≤ ENNReal.ofReal v := by
    unfold CondPortOT.SingDual.rhoMin
    exact le_trans (iInf₂_le Qs ⟨hQsp, hQsF⟩) hQsc
  have heq : CondPortOT.SingDual.rhoMin DX DY xh yh x0 γ ε = ENNReal.ofReal v :=
    le_antisymm hup hlow
  refine ⟨⟨v, ⟨⟨υs, hυs, hυss, rfl⟩, ?_⟩, heq⟩, ?_⟩
  · rintro r ⟨υ, h1, h2, rfl⟩
    exact hmin (hmemK υ h1 h2)
  · intro ρ hρ
    constructor
    · rintro ⟨Q, ⟨hQp, hTC⟩, hQF⟩
      unfold CondPortOT.SingDual.rhoMin
      exact le_trans (iInf₂_le Q ⟨hQp, hQF⟩) hTC
    · intro h
      rw [heq] at h
      exact ⟨Qs, ⟨hQsp, le_trans hQsc h⟩, hQsF⟩
