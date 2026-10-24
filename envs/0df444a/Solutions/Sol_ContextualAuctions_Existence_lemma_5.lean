-- Prove2me | solution 1 for ContextualAuctions.Existence.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T06:43:42.252233+00:00
-- url     : https://prove2.me/submissions/d0e1d40d-9d6a-4ec8-a0a2-4819fa510dc5

import Mathlib
import Definitions.Def_ContextualAuctions_Existence_Setting
import Definitions.Def_ContextualAuctions_Existence_FixedPoint
import Theorems.Thm_ContextualAuctions_Existence_lemma_1
import Theorems.Thm_ContextualAuctions_Existence_lemma_3

open MeasureTheory ContextualAuctions.Existence

namespace L5Aux

lemma measurableSet_Theta (M : Model) : MeasurableSet (Theta M) := by
  simp only [Theta, Set.ofPred_and, Set.ofPred_forall]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => ?_) ?_
  · exact (measurableSet_lt measurable_const ((measurable_pi_apply i).comp measurable_fst)).inter
      (measurableSet_lt ((measurable_pi_apply i).comp measurable_fst) measurable_const)
  · exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const)

lemma qmp_toType (d : ℕ) :
    Measure.QuasiMeasurePreserving (toType : EuclideanSpace ℝ (Fin (d + 1)) → (Fin d → ℝ) × ℝ)
      volume volume := by
  have h1 := PiLp.volume_preserving_ofLp (ι := Fin (d + 1))
  have h2 := measurePreserving_piFinSuccAbove (fun _ : Fin (d + 1) => (volume : Measure ℝ))
    (Fin.last d)
  have h3 := Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := Measure.pi fun _ : Fin d => (volume : Measure ℝ))
  have h := (h3.comp h2).comp h1
  have heq : ((Prod.swap ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ)
      (Fin.last d))) ∘ (@WithLp.ofLp 2 (Fin (d + 1) → ℝ))) = toType := by
    funext x
    simp [toType, MeasurableEquiv.piFinSuccAbove_apply]
    rfl
  rw [heq] at h
  exact h.quasiMeasurePreserving

lemma measurable_toType (d : ℕ) :
    Measurable (toType : EuclideanSpace ℝ (Fin (d + 1)) → (Fin d → ℝ) × ℝ) :=
  (qmp_toType d).measurable

lemma Vtheta_congr (M : Model) {f g : (Fin M.d → ℝ) × ℝ → ℝ}
    (h : f =ᵐ[volume.restrict (Theta M)] g) : Vtheta M f = Vtheta M g := by
  unfold Vtheta totalVariation
  have h' : ∀ᵐ y ∂(volume : Measure ((Fin M.d → ℝ) × ℝ)), y ∈ Theta M → f y = g y :=
    (ae_restrict_iff' (measurableSet_Theta M)).mp h
  have h'' : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (M.d + 1)))),
      toType x ∈ Theta M → f (toType x) = g (toType x) := (qmp_toType M.d).ae h'
  have hr : ∀ᵐ x ∂(volume.restrict (toType ⁻¹' Theta M) :
      Measure (EuclideanSpace ℝ (Fin (M.d + 1)))), f (toType x) = g (toType x) :=
    (ae_restrict_iff' ((measurableSet_Theta M).preimage (measurable_toType M.d))).mpr h''
  congr 1
  funext φ
  congr 1
  funext _
  refine congrArg (fun r : ℝ => (r : EReal)) ?_
  apply integral_congr_ae
  filter_upwards [hr] with x hx
  simp only [hx]

lemma measurable_val (d : ℕ) :
    Measurable (fun q : ((Fin d → ℝ) × ℝ) × (Fin d → ℝ) => val q.1 q.2) := by
  unfold val
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).mul
    ((measurable_pi_apply i).comp measurable_snd)

lemma measurable_sigma (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : Measurable μ) : Measurable (fun p : (Fin M.d → ℝ) × ℝ => sigma M μ p.1 p.2) := by
  classical
  have := hM.probG
  have hpaced : Measurable
      (fun q : ((Fin M.d → ℝ) × ℝ) × (Fin M.d → ℝ) => paced μ q.1 q.2) := by
    unfold paced
    exact (measurable_val M.d).div (measurable_const.add (hμ.comp measurable_fst))
  have hS : MeasurableSet
      {p : ((Fin M.d → ℝ) × ℝ) × ((Fin M.d → ℝ) × ℝ) | paced μ p.2 p.1.1 ≤ p.1.2} := by
    apply measurableSet_le
    · exact hpaced.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
    · exact measurable_snd.comp measurable_fst
  have hH : Measurable (fun p : (Fin M.d → ℝ) × ℝ => H M μ p.1 p.2) := by
    unfold H
    have := measurable_measure_prodMk_left (ν := M.G) hS
    exact (this.ennreal_toReal).pow_const _
  have hint1 : ∀ (a b : ((Fin M.d → ℝ) × ℝ) → ℝ), Measurable a → Measurable b →
      StronglyMeasurable (fun p : (Fin M.d → ℝ) × ℝ =>
        ∫ s in Set.Ioc (a p) (b p), H M μ p.1 s) := by
    intro a b ha hb
    have hg : Measurable (fun q : ((Fin M.d → ℝ) × ℝ) × ℝ =>
        Set.indicator {q : ((Fin M.d → ℝ) × ℝ) × ℝ | a q.1 < q.2 ∧ q.2 ≤ b q.1}
          (fun q => H M μ q.1.1 q.2) q) := by
      apply Measurable.indicator
      · exact hH.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      · exact (measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
          (measurableSet_le measurable_snd (hb.comp measurable_fst))
    have := (hg.stronglyMeasurable).integral_prod_right' (ν := (volume : Measure ℝ))
    convert this using 2 with p
    rw [← integral_indicator measurableSet_Ioc]
    congr 1
  have hI : Measurable (fun p : (Fin M.d → ℝ) × ℝ => ∫ s in (M.r p.1)..p.2, H M μ p.1 s) := by
    have h1 := (hint1 (fun p => M.r p.1) (fun p => p.2)
      (hM.measurable_r.comp measurable_fst) measurable_snd).measurable
    have h2 := (hint1 (fun p => p.2) (fun p => M.r p.1) measurable_snd
      (hM.measurable_r.comp measurable_fst)).measurable
    have := h1.sub h2
    convert this using 1
    funext p
    simp [intervalIntegral]
  unfold sigma
  refine Measurable.ite (measurableSet_lt measurable_snd
    (hM.measurable_r.comp measurable_fst)) measurable_snd ?_
  refine Measurable.ite (measurableSet_eq_fun hH measurable_const) measurable_const ?_
  exact measurable_snd.sub (hI.div hH)

lemma measurable_beta (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : Measurable μ) : Measurable (Function.uncurry (beta M μ)) := by
  have hpaced : Measurable
      (fun q : ((Fin M.d → ℝ) × ℝ) × (Fin M.d → ℝ) => paced μ q.1 q.2) := by
    unfold paced
    exact (measurable_val M.d).div (measurable_const.add (hμ.comp measurable_fst))
  have : Function.uncurry (beta M μ) =
      (fun p : (Fin M.d → ℝ) × ℝ => sigma M μ p.1 p.2) ∘
        (fun q : ((Fin M.d → ℝ) × ℝ) × (Fin M.d → ℝ) => (q.2, paced μ q.1 q.2)) := by
    funext q; rfl
  rw [this]
  exact (measurable_sigma M hM μ hμ).comp (measurable_snd.prodMk hpaced)

/-- the paced bid of type `θ` with multiplier `t`. -/
noncomputable def bidT (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ) (t : ℝ) :
    (Fin M.d → ℝ) → ℝ :=
  fun α => sigma M μ α (val θ α / (1 + t))

lemma measurable_Lam (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : Measurable μ) :
    Measurable (fun p : ((Fin M.d → ℝ) × ℝ) × ℝ => lagr M μ p.1 p.2 (bidT M μ p.1 p.2)) := by
  classical
  have := hM.probG
  have := hM.probF
  have : IsProbabilityMeasure (P M) := by unfold P; infer_instance
  have hb : Measurable (fun q : (((Fin M.d → ℝ) × ℝ) × ℝ) ×
      ((Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ)) =>
        bidT M μ q.1.1 q.1.2 q.2.1) := by
    unfold bidT
    have hv : Measurable (fun q : (((Fin M.d → ℝ) × ℝ) × ℝ) ×
        ((Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ)) => val q.1.1 q.2.1) :=
      (measurable_val M.d).comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))
    exact (measurable_sigma M hM μ hμ).comp ((measurable_fst.comp measurable_snd).prodMk
      (hv.div (measurable_const.add (measurable_snd.comp measurable_fst))))
  have hW : MeasurableSet {q : (((Fin M.d → ℝ) × ℝ) × ℝ) ×
      ((Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ)) |
        wins M (beta M μ) (bidT M μ q.1.1 q.1.2) q.2} := by
    unfold wins
    simp only [Set.ofPred_and, Set.ofPred_forall]
    refine MeasurableSet.inter ?_ (MeasurableSet.iInter fun i => ?_)
    · exact measurableSet_le (hM.measurable_r.comp (measurable_fst.comp measurable_snd)) hb
    · refine measurableSet_le ?_ hb
      have hm : Measurable (fun q : (((Fin M.d → ℝ) × ℝ) × ℝ) ×
          ((Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ)) => (q.2.2 i, q.2.1)) := by
        fun_prop
      exact (measurable_beta M hM μ hμ).comp hm
  have hg : Measurable (fun q : (((Fin M.d → ℝ) × ℝ) × ℝ) ×
      ((Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ)) =>
        if wins M (beta M μ) (bidT M μ q.1.1 q.1.2) q.2 then
          val q.1.1 q.2.1 / (1 + q.1.2) - bidT M μ q.1.1 q.1.2 q.2.1 else 0) := by
    refine Measurable.ite hW ?_ measurable_const
    refine Measurable.sub ?_ hb
    exact ((measurable_val M.d).comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))).div
      (measurable_const.add (measurable_snd.comp measurable_fst))
  have := (hg.stronglyMeasurable).integral_prod_right' (ν := P M)
  exact this.measurable

lemma bddAbove_omega (M : Model) (hM : M.Standing) :
    BddAbove {v | ∃ θ ∈ Theta M, ∃ α ∈ M.A, v = val θ α} := by
  obtain ⟨R, hR⟩ := hM.A_bounded.subset_closedBall 0
  refine ⟨∑ _i : Fin M.d, M.U * R, ?_⟩
  rintro v ⟨θ, hθ, α, hα, rfl⟩
  unfold val
  apply Finset.sum_le_sum
  intro i _
  have hαi : |α i| ≤ R := by
    have := hR hα
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact (norm_le_pi_norm α i).trans this
  have hpos := hM.A_pos hα i
  have hw := hθ.1 i
  calc θ.1 i * α i ≤ M.U * α i := mul_le_mul_of_nonneg_right hw.2.le hpos.le
    _ ≤ M.U * R := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hαi) hM.U_pos.le

lemma val_le_omega (M : Model) (hM : M.Standing) {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M)
    {α : Fin M.d → ℝ} (hα : α ∈ M.A) : val θ α ≤ omega M :=
  le_csSup (bddAbove_omega M hM) ⟨θ, hθ, α, hα, rfl⟩

lemma theta_nonempty (M : Model) (hM : M.Standing) : (Theta M).Nonempty := by
  refine ⟨(fun _ => M.U / 2, (M.Bmin + M.U) / 2), fun i => ⟨?_, ?_⟩, ?_, ?_⟩
  · have := hM.U_pos; simp only; linarith
  · have := hM.U_pos; simp only; linarith
  · have := hM.Bmin_lt_U; simp only; linarith
  · have := hM.Bmin_lt_U; simp only; linarith

lemma omega_nonneg (M : Model) (hM : M.Standing) : 0 ≤ omega M := by
  obtain ⟨θ, hθ⟩ := theta_nonempty M hM
  obtain ⟨α, hα⟩ := hM.A_nonempty
  refine le_trans ?_ (val_le_omega M hM hθ hα)
  unfold val
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hθ.1 i).1.le (hM.A_pos hα i).le

lemma ae_A (M : Model) (hM : M.Standing) : ∀ᵐ ω ∂P M, ω.1 ∈ M.A := by
  have := hM.probG
  have := hM.probF
  have h1 : ∀ᵐ α ∂M.F, α ∈ M.A := ae_iff.mpr hM.F_A
  exact (Measure.quasiMeasurePreserving_fst (μ := M.F)
    (ν := Measure.pi fun _ : Fin (M.n - 1) => M.G)).ae h1

open Classical in
lemma elem_le (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M) {t : ℝ} (ht : 0 ≤ 1 + t)
    (b : (Fin M.d → ℝ) → ℝ) (hb : Admissible M (beta M μ) b) :
    ∫ ω, (if wins M (beta M μ) b ω then val θ ω.1 - (1 + t) * b ω.1 else 0) ∂P M ≤ omega M := by
  have := hM.probG
  have := hM.probF
  have : IsProbabilityMeasure (P M) := by unfold P; infer_instance
  have hω0 := omega_nonneg M hM
  have hle : ∀ᵐ ω ∂P M,
      (if wins M (beta M μ) b ω then val θ ω.1 - (1 + t) * b ω.1 else 0) ≤ omega M := by
    filter_upwards [ae_A M hM] with ω hω
    split_ifs
    · have := hb.2.1 ω.1 hω
      have := val_le_omega M hM hθ hω
      nlinarith
    · exact hω0
  by_cases hint : Integrable (fun ω =>
      if wins M (beta M μ) b ω then val θ ω.1 - (1 + t) * b ω.1 else 0) (P M)
  · calc _ ≤ ∫ _ω, omega M ∂P M := integral_mono_ae hint (integrable_const _) hle
      _ = omega M := by simp
  · rw [integral_undef hint]; exact hω0

open Classical in
lemma zero_admissible (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) :
    Admissible M (beta M μ) (fun _ => 0) := by
  refine ⟨measurable_const, fun _ _ => le_refl 0, ?_⟩
  simp only [ite_self]
  exact integrable_zero _ _ _

open Classical in
/-- the set whose supremum defines `qDual` -/
def Sset (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ) (t : ℝ) : Set ℝ :=
  {v | ∃ b, Admissible M (beta M μ) b ∧
    v = ∫ ω, (if wins M (beta M μ) b ω then val θ ω.1 - (1 + t) * b ω.1 else 0) ∂P M}

lemma qDual_eq (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ) (t : ℝ) :
    qDual M μ θ t = sSup (Sset M μ θ t) + t * θ.2 := rfl

lemma Sset_bdd (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M) {t : ℝ} (ht : 0 ≤ 1 + t) :
    BddAbove (Sset M μ θ t) ∧ (Sset M μ θ t).Nonempty ∧ sSup (Sset M μ θ t) ≤ omega M := by
  have hbdd : BddAbove (Sset M μ θ t) := by
    refine ⟨omega M, ?_⟩
    rintro v ⟨b, hb, rfl⟩
    exact elem_le M hM μ hθ ht b hb
  have hne : (Sset M μ θ t).Nonempty := ⟨_, ⟨fun _ => 0, zero_admissible M μ, rfl⟩⟩
  refine ⟨hbdd, hne, csSup_le hne ?_⟩
  rintro v ⟨b, hb, rfl⟩
  exact elem_le M hM μ hθ ht b hb

open Classical in
lemma Sset_zero_nonneg (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M) {t : ℝ} (ht : 0 ≤ 1 + t) :
    0 ≤ sSup (Sset M μ θ t) := by
  have hmem : (∫ ω, (if wins M (beta M μ) (fun _ => 0) ω then val θ ω.1 - (1 + t) * 0
      else 0) ∂P M) ∈ Sset M μ θ t := ⟨fun _ => 0, zero_admissible M μ, rfl⟩
  have hnn : 0 ≤ ∫ ω, (if wins M (beta M μ) (fun _ => 0) ω then val θ ω.1 - (1 + t) * 0
      else 0) ∂P M := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_A M hM] with ω hω
    split_ifs
    · simp only [mul_zero, sub_zero]
      unfold val
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (hθ.1 i).1.le (hM.A_pos hω i).le
    · exact le_refl 0
  exact hnn.trans (le_csSup (Sset_bdd M hM μ hθ ht).1 hmem)

open Classical in
lemma integral_scale (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ)
    {t : ℝ} (ht : 0 < 1 + t) (b : (Fin M.d → ℝ) → ℝ) :
    ∫ ω, (if wins M (beta M μ) b ω then val θ ω.1 - (1 + t) * b ω.1 else 0) ∂P M =
      (1 + t) * lagr M μ θ t b := by
  unfold lagr
  rw [← integral_const_mul]
  congr 1
  funext ω
  split_ifs
  · field_simp
  · simp

/-- Lemma 1 gives the closed form of the dual function. -/
lemma qDual_formula (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : IsPacing M μ) {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M) {t : ℝ} (ht : 0 ≤ t) :
    qDual M μ θ t = (1 + t) * lagr M μ θ t (bidT M μ θ t) + t * θ.2 := by
  obtain ⟨hadm, hmax⟩ := lemma_1 M hM μ hμ θ hθ t ht
  have ht1 : 0 < 1 + t := by linarith
  rw [qDual_eq]
  congr 1
  apply IsGreatest.csSup_eq
  refine ⟨⟨bidT M μ θ t, hadm, (integral_scale M μ θ ht1 _).symm⟩, ?_⟩
  rintro v ⟨b, hb, rfl⟩
  rw [integral_scale M μ θ ht1]
  exact mul_le_mul_of_nonneg_left (hmax b hb) ht1.le

lemma measurableSet_wins (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : Measurable μ) (b : (Fin M.d → ℝ) → ℝ) (hb : Measurable b) :
    MeasurableSet {ω : (Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ) |
      wins M (beta M μ) b ω} := by
  unfold wins
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine MeasurableSet.inter ?_ (MeasurableSet.iInter fun i => ?_)
  · exact measurableSet_le (hM.measurable_r.comp measurable_fst) (hb.comp measurable_fst)
  · refine measurableSet_le ?_ (hb.comp measurable_fst)
    have hm : Measurable (fun q : (Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ) =>
        (q.2 i, q.1)) := by fun_prop
    exact (measurable_beta M hM μ hμ).comp hm

open Classical in
lemma affine_elem (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : Measurable μ) {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M)
    (b : (Fin M.d → ℝ) → ℝ) (hb : Admissible M (beta M μ) b) :
    ∃ A Pb : ℝ, ∀ t : ℝ,
      ∫ ω, (if wins M (beta M μ) b ω then val θ ω.1 - (1 + t) * b ω.1 else 0) ∂P M =
        A - (1 + t) * Pb := by
  have := hM.probG
  have := hM.probF
  have : IsProbabilityMeasure (P M) := by unfold P; infer_instance
  have hW := measurableSet_wins M hM μ hμ b hb.1
  have hv : Measurable (fun ω : (Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ) =>
      val θ ω.1) :=
    (measurable_val M.d).comp (measurable_const.prodMk measurable_fst)
  have hint1 : Integrable (fun ω => if wins M (beta M μ) b ω then val θ ω.1 else 0) (P M) := by
    refine Integrable.mono' (integrable_const (omega M)) ?_ ?_
    · exact (Measurable.ite hW hv measurable_const).aestronglyMeasurable
    · filter_upwards [ae_A M hM] with ω hω
      split_ifs
      · have h0 : 0 ≤ val θ ω.1 := by
          unfold val
          exact Finset.sum_nonneg fun i _ => mul_nonneg (hθ.1 i).1.le (hM.A_pos hω i).le
        rw [Real.norm_eq_abs, abs_of_nonneg h0]
        exact val_le_omega M hM hθ hω
      · simpa using omega_nonneg M hM
  refine ⟨∫ ω, (if wins M (beta M μ) b ω then val θ ω.1 else 0) ∂P M,
    ∫ ω, (if wins M (beta M μ) b ω then b ω.1 else 0) ∂P M, fun t => ?_⟩
  rw [← integral_const_mul, ← integral_sub hint1 (hb.2.2.const_mul _)]
  congr 1
  funext ω
  split_ifs <;> ring

lemma convex_q (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : Measurable μ) {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M) :
    ConvexOn ℝ (Set.Ioi (-1)) (qDual M μ θ) := by
  refine ⟨convex_Ioi _, fun x hx y hy a c ha hc hac => ?_⟩
  have hx' : 0 ≤ 1 + x := by have : (-1 : ℝ) < x := hx; linarith
  have hy' : 0 ≤ 1 + y := by have : (-1 : ℝ) < y := hy; linarith
  have hz' : 0 ≤ 1 + (a • x + c • y) := by
    simp only [smul_eq_mul]; nlinarith
  simp only [qDual_eq, smul_eq_mul]
  have key : sSup (Sset M μ θ (a * x + c * y)) ≤
      a * sSup (Sset M μ θ x) + c * sSup (Sset M μ θ y) := by
    apply csSup_le (Sset_bdd M hM μ hθ (by simpa using hz')).2.1
    rintro v ⟨b, hb, rfl⟩
    obtain ⟨A, Pb, h⟩ := affine_elem M hM μ hμ hθ b hb
    have h1 : A - (1 + x) * Pb ≤ sSup (Sset M μ θ x) :=
      le_csSup (Sset_bdd M hM μ hθ hx').1 ⟨b, hb, (h x).symm⟩
    have h2 : A - (1 + y) * Pb ≤ sSup (Sset M μ θ y) :=
      le_csSup (Sset_bdd M hM μ hθ hy').1 ⟨b, hb, (h y).symm⟩
    rw [h]
    have : A - (1 + (a * x + c * y)) * Pb = a * (A - (1 + x) * Pb) + c * (A - (1 + y) * Pb) := by
      have hc' : c = 1 - a := by linarith
      subst hc'; ring
    rw [this]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hc)
  nlinarith

lemma ell_spec (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : Measurable μ) {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M) :
    ell M μ θ ∈ Set.Icc 0 (omega M / M.Bmin) ∧
      IsMinOn (qDual M μ θ) (Set.Icc 0 (omega M / M.Bmin)) (ell M μ θ) := by
  set c := omega M / M.Bmin with hc_def
  have hc : 0 ≤ c := div_nonneg (omega_nonneg M hM) hM.Bmin_pos.le
  have hcont : ContinuousOn (qDual M μ θ) (Set.Icc 0 c) :=
    ((convex_q M hM μ hμ hθ).continuousOn isOpen_Ioi).mono
      (fun s hs => show (-1 : ℝ) < s by linarith [hs.1])
  obtain ⟨s0, hs0, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hc) hcont
  set A := {s ∈ Set.Icc 0 c | IsMinOn (qDual M μ θ) (Set.Icc 0 c) s} with hA_def
  have hA : A = Set.Icc 0 c ∩ qDual M μ θ ⁻¹' Set.Iic (qDual M μ θ s0) := by
    ext s
    constructor
    · rintro ⟨hs, hm⟩
      exact ⟨hs, hm hs0⟩
    · rintro ⟨hs, hle⟩
      exact ⟨hs, fun x hx => show qDual M μ θ s ≤ qDual M μ θ x from le_trans hle (hmin hx)⟩
  have hclosed : IsClosed A := by
    rw [hA]
    exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hmem : sInf A ∈ A :=
    hclosed.csInf_mem ⟨s0, hs0, hmin⟩ ⟨0, fun s hs => hs.1.1⟩
  exact hmem

lemma G_ac_restrict (M : Model) (hM : M.Standing) : M.G ≪ volume.restrict (Theta M) := by
  intro s hs
  rw [Measure.restrict_apply_eq_zero' (measurableSet_Theta M)] at hs
  have h1 : M.G (s ∩ Theta M) = 0 := hM.G_ac hs
  apply measure_mono_null (t := (s ∩ Theta M) ∪ (Theta M)ᶜ)
  · intro x hx
    by_cases hxT : x ∈ Theta M
    · exact Or.inl ⟨hx, hxT⟩
    · exact Or.inr hxT
  · exact measure_union_null h1 hM.G_Theta

lemma integrable_q (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    (hμ : IsPacing M μ) (ν : (Fin M.d → ℝ) × ℝ → ℝ) (hν : Measurable ν)
    (hνr : ∀ θ ∈ Theta M, ν θ ∈ Set.Icc 0 (omega M / M.Bmin)) :
    Integrable (fun θ => qDual M μ θ (ν θ)) M.G := by
  have := hM.probG
  have hΘ : ∀ᵐ θ ∂M.G, θ ∈ Theta M := ae_iff.mpr hM.G_Theta
  set c := omega M / M.Bmin
  have hmeas : Measurable (fun θ : (Fin M.d → ℝ) × ℝ =>
      (1 + ν θ) * lagr M μ θ (ν θ) (bidT M μ θ (ν θ)) + ν θ * θ.2) := by
    have h1 := (measurable_Lam M hM μ hμ.1).comp (measurable_id.prodMk hν)
    exact ((measurable_const.add hν).mul h1).add (hν.mul measurable_snd)
  refine Integrable.mono' (integrable_const (omega M + c * M.U)) ?_ ?_
  · refine hmeas.aestronglyMeasurable.congr ?_
    filter_upwards [hΘ] with θ hθ
    exact (qDual_formula M hM μ hμ hθ (hνr θ hθ).1).symm
  · filter_upwards [hΘ] with θ hθ
    have ht := hνr θ hθ
    have ht1 : 0 ≤ 1 + ν θ := by linarith [ht.1]
    have h0 := Sset_zero_nonneg M hM μ hθ ht1
    have h1 := (Sset_bdd M hM μ hθ ht1).2.2
    have hB : 0 < θ.2 := lt_trans hM.Bmin_pos hθ.2.1
    have hBU : θ.2 ≤ M.U := hθ.2.2.le
    have hc : 0 ≤ c := div_nonneg (omega_nonneg M hM) hM.Bmin_pos.le
    have e1 : 0 ≤ ν θ * θ.2 := mul_nonneg ht.1 hB.le
    have e2 : ν θ * θ.2 ≤ c * M.U :=
      mul_le_mul ht.2 hBU hB.le hc
    rw [qDual_eq, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith

end L5Aux

open L5Aux in
theorem solution (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (hμ : μ ∈ X0 M)
    (hfix : μ ∈ C0star M μ) :
    ∀ᵐ θ ∂M.G, μ θ ∈ Set.Icc 0 (omega M / M.Bmin) ∧
      IsMinOn (qDual M μ θ) (Set.Icc 0 (omega M / M.Bmin)) (μ θ) := by
  have := hM.probG
  set c := omega M / M.Bmin with hc_def
  have hc : 0 ≤ c := div_nonneg (omega_nonneg M hM) hM.Bmin_pos.le
  have hpac : IsPacing M μ := hμ.1.1
  have hμr : ∀ θ ∈ Theta M, μ θ ∈ Set.Icc 0 c := hμ.1.2.2
  obtain ⟨hellint, hellV⟩ := lemma_3 M hM μ hpac hμr
  have hae := hellint.aestronglyMeasurable.aemeasurable
  set g := hae.mk (ell M μ)
  set ν : (Fin M.d → ℝ) × ℝ → ℝ := fun θ => max 0 (min c (g θ)) with hν_def
  have hνm : Measurable ν := measurable_const.max (measurable_const.min hae.measurable_mk)
  have hνell : ν =ᵐ[volume.restrict (Theta M)] ell M μ := by
    filter_upwards [hae.ae_eq_mk, ae_restrict_mem (measurableSet_Theta M)] with θ h hθ
    have hs := (ell_spec M hM μ hpac.1 hθ).1
    simp only [hν_def, g, ← h]
    rw [min_eq_right hs.2, max_eq_right hs.1]
  have hνr : ∀ θ ∈ Theta M, ν θ ∈ Set.Icc 0 c :=
    fun θ _ => ⟨le_max_left _ _, max_le hc (min_le_left _ _)⟩
  have hνX0 : ν ∈ X0 M := by
    refine ⟨⟨⟨hνm, fun θ _ => le_max_left _ _⟩, hellint.congr hνell.symm, hνr⟩, ?_⟩
    rw [Vtheta_congr M hνell]
    exact hellV
  have hle := hfix.2 ν hνX0
  unfold fObj at hle
  have hI1 := integrable_q M hM μ hpac μ hpac.1 hμr
  have hI2 := integrable_q M hM μ hpac ν hνm hνr
  have hG : ν =ᵐ[M.G] ell M μ := (G_ac_restrict M hM).ae_le hνell
  have hΘ : ∀ᵐ θ ∂M.G, θ ∈ Theta M := ae_iff.mpr hM.G_Theta
  have hdiff : 0 ≤ᵐ[M.G] (fun θ => qDual M μ θ (μ θ) - qDual M μ θ (ν θ)) := by
    filter_upwards [hG, hΘ] with θ h hθ
    have : qDual M μ θ (ell M μ θ) ≤ qDual M μ θ (μ θ) := (ell_spec M hM μ hpac.1 hθ).2 (hμr θ hθ)
    simp only [Pi.zero_apply, h]
    linarith
  have hint0 : ∫ θ, (qDual M μ θ (μ θ) - qDual M μ θ (ν θ)) ∂M.G = 0 := by
    apply le_antisymm
    · rw [integral_sub hI1 hI2]; linarith
    · exact integral_nonneg_of_ae hdiff
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hdiff (hI1.sub hI2)).mp hint0
  filter_upwards [hzero, hG, hΘ] with θ h0 hνe hθ
  refine ⟨hμr θ hθ, fun s hs => ?_⟩
  have h1 := (ell_spec M hM μ hpac.1 hθ).2 hs
  simp only [Pi.zero_apply, hνe] at h0
  show qDual M μ θ (μ θ) ≤ qDual M μ θ s
  have h1' : qDual M μ θ (ell M μ θ) ≤ qDual M μ θ s := h1
  linarith
