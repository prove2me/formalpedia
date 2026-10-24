-- Prove2me | solution 1 for ContextualAuctions.Existence.proposition_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T06:26:18.21204+00:00
-- url     : https://prove2.me/submissions/e2a90fdf-d3a1-413f-b745-e82b59aabb37
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ContextualAuctions_Existence_Setting
import Definitions.Def_ContextualAuctions_Existence_FixedPoint
import Theorems.Thm_ContextualAuctions_Existence_lemma_4
import Theorems.Thm_ContextualAuctions_Existence_lemma_5
import Theorems.Thm_FanGlicksberg_kakutani_fan_glicksberg

open MeasureTheory ContextualAuctions.Existence

namespace CAProp2Aux

/-- `H` only depends on the `G`-a.e. class of `μ`. -/
lemma H_congr (M : Model) {μ₁ μ₂ : (Fin M.d → ℝ) × ℝ → ℝ} (h : μ₁ =ᵐ[M.G] μ₂) :
    H M μ₁ = H M μ₂ := by
  funext α x
  unfold H
  congr 2
  apply measure_congr
  filter_upwards [h] with θ hθ
  change (paced μ₁ θ α ≤ x) = (paced μ₂ θ α ≤ x)
  simp only [paced, hθ]

lemma sigma_congr (M : Model) {μ₁ μ₂ : (Fin M.d → ℝ) × ℝ → ℝ} (h : μ₁ =ᵐ[M.G] μ₂) :
    sigma M μ₁ = sigma M μ₂ := by
  funext α x
  unfold sigma
  rw [H_congr M h]

lemma ae_comp (M : Model) (hM : M.Standing) {μ₁ μ₂ : (Fin M.d → ℝ) × ℝ → ℝ}
    (h : μ₁ =ᵐ[M.G] μ₂) : ∀ᵐ ω ∂P M, ∀ i, μ₁ (ω.2 i) = μ₂ (ω.2 i) := by
  have := hM.probG
  have := hM.probF
  rw [ae_all_iff]
  intro i
  have h1 : ∀ᵐ x ∂(Measure.pi fun _ : Fin (M.n - 1) => M.G), μ₁ (x i) = μ₂ (x i) :=
    (measurePreserving_eval (fun _ : Fin (M.n - 1) => M.G) i).quasiMeasurePreserving.ae h
  exact (Measure.quasiMeasurePreserving_snd (μ := M.F)
    (ν := Measure.pi fun _ : Fin (M.n - 1) => M.G)).ae h1

lemma wins_congr (M : Model) {μ₁ μ₂ : (Fin M.d → ℝ) × ℝ → ℝ} (h : μ₁ =ᵐ[M.G] μ₂)
    (b : (Fin M.d → ℝ) → ℝ) (ω : (Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ))
    (hω : ∀ i, μ₁ (ω.2 i) = μ₂ (ω.2 i)) :
    wins M (beta M μ₁) b ω ↔ wins M (beta M μ₂) b ω := by
  unfold wins beta paced
  rw [sigma_congr M h]
  simp only [hω]

lemma qDual_congr (M : Model) (hM : M.Standing) {μ₁ μ₂ : (Fin M.d → ℝ) × ℝ → ℝ}
    (h : μ₁ =ᵐ[M.G] μ₂) : qDual M μ₁ = qDual M μ₂ := by
  classical
  funext θ t
  have hP := ae_comp M hM h
  have hset : ∀ (f : (Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ) → ℝ)
      (b : (Fin M.d → ℝ) → ℝ),
      (fun ω => if wins M (beta M μ₁) b ω then f ω else 0) =ᵐ[P M]
        (fun ω => if wins M (beta M μ₂) b ω then f ω else 0) := by
    intro f b
    filter_upwards [hP] with ω hω
    simp only [wins_congr M h b ω hω]
  have hadm : ∀ b, Admissible M (beta M μ₁) b ↔ Admissible M (beta M μ₂) b := by
    intro b
    unfold Admissible
    rw [integrable_congr (hset (fun ω => b ω.1) b)]
  unfold qDual
  congr 2
  ext v
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, (hadm b).1 hb, integral_congr_ae (hset _ b)⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, (hadm b).2 hb, (integral_congr_ae (hset _ b)).symm⟩

lemma fObj_congr (M : Model) (hM : M.Standing) {μ₁ μ₂ ν₁ ν₂ : (Fin M.d → ℝ) × ℝ → ℝ}
    (h : μ₁ =ᵐ[M.G] μ₂) (h' : ν₁ =ᵐ[M.G] ν₂) : fObj M μ₁ ν₁ = fObj M μ₂ ν₂ := by
  unfold fObj
  rw [qDual_congr M hM h]
  apply integral_congr_ae
  filter_upwards [h'] with θ hθ
  rw [hθ]

lemma measurableSet_Theta (M : Model) : MeasurableSet (Theta M) := by
  simp only [Theta, Set.ofPred_and, Set.ofPred_forall]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => ?_) ?_
  · exact (measurableSet_lt measurable_const ((measurable_pi_apply i).comp measurable_fst)).inter
      (measurableSet_lt ((measurable_pi_apply i).comp measurable_fst) measurable_const)
  · exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const)

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

lemma ae_G_of_ae_vol (M : Model) (hM : M.Standing) {f₁ f₂ : (Fin M.d → ℝ) × ℝ → ℝ}
    (h : f₁ =ᵐ[volume.restrict (Theta M)] f₂) : f₁ =ᵐ[M.G] f₂ :=
  (G_ac_restrict M hM).ae_le h

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

lemma ae_A (M : Model) (hM : M.Standing) : ∀ᵐ ω ∂P M, ω.1 ∈ M.A := by
  have := hM.probG
  have := hM.probF
  have h1 : ∀ᵐ α ∂M.F, α ∈ M.A := ae_iff.mpr hM.F_A
  exact (Measure.quasiMeasurePreserving_fst (μ := M.F)
    (ν := Measure.pi fun _ : Fin (M.n - 1) => M.G)).ae h1

open Classical in
lemma elem_le (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M) (hω0 : 0 ≤ omega M) {t : ℝ} (ht : 0 ≤ t)
    (b : (Fin M.d → ℝ) → ℝ) (hb : Admissible M (beta M μ) b) :
    ∫ ω, (if wins M (beta M μ) b ω then val θ ω.1 - (1 + t) * b ω.1 else 0) ∂P M ≤ omega M := by
  have := hM.probG
  have := hM.probF
  have : IsProbabilityMeasure (P M) := by unfold P; infer_instance
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
lemma qDual_bounds (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M) (hω0 : 0 ≤ omega M) {t : ℝ} (ht : 0 ≤ t) :
    t * θ.2 ≤ qDual M μ θ t ∧ (t = 0 → qDual M μ θ t ≤ omega M) := by
  set S := {v | ∃ b, Admissible M (beta M μ) b ∧
    v = ∫ ω, (if wins M (beta M μ) b ω then val θ ω.1 - (1 + t) * b ω.1 else 0) ∂P M} with hS
  have hbdd : BddAbove S := by
    refine ⟨omega M, ?_⟩
    rintro v ⟨b, hb, rfl⟩
    exact elem_le M hM μ hθ hω0 ht b hb
  have hmem : (∫ ω, (if wins M (beta M μ) (fun _ => 0) ω then val θ ω.1 - (1 + t) * 0
      else 0) ∂P M) ∈ S := ⟨fun _ => 0, zero_admissible M μ, rfl⟩
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
  unfold qDual
  rw [← hS]
  constructor
  · have := le_csSup hbdd hmem
    linarith
  · intro ht0
    subst ht0
    have : sSup S ≤ omega M := csSup_le ⟨_, hmem⟩ (fun v hv => by
      obtain ⟨b, hb, rfl⟩ := hv
      exact elem_le M hM μ hθ hω0 ht b hb)
    linarith

lemma isMinOn_Ici (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ)
    {θ : (Fin M.d → ℝ) × ℝ} (hθ : θ ∈ Theta M) {s : ℝ}
    (hs : s ∈ Set.Icc 0 (omega M / M.Bmin))
    (hmin : IsMinOn (qDual M μ θ) (Set.Icc 0 (omega M / M.Bmin)) s) :
    IsMinOn (qDual M μ θ) (Set.Ici 0) s := by
  have hB := hM.Bmin_pos
  have hω0 : 0 ≤ omega M := by
    have h := le_trans hs.1 hs.2
    rwa [le_div_iff₀ hB, zero_mul] at h
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht
  by_cases htle : t ≤ omega M / M.Bmin
  · exact hmin ⟨ht0, htle⟩
  · rw [not_le] at htle
    have h0mem : (0 : ℝ) ∈ Set.Icc 0 (omega M / M.Bmin) := ⟨le_refl 0, div_nonneg hω0 hB.le⟩
    have hq0 := (qDual_bounds M hM μ hθ hω0 (le_refl 0)).2 rfl
    have hqt := (qDual_bounds M hM μ hθ hω0 ht0).1
    have hs0 : qDual M μ θ s ≤ qDual M μ θ 0 := hmin h0mem
    have htB : omega M < t * M.Bmin := by
      rwa [div_lt_iff₀ hB] at htle
    have hBθ : M.Bmin < θ.2 := hθ.2.1
    have htpos : 0 < t := lt_of_le_of_lt (div_nonneg hω0 hB.le) htle
    have : t * M.Bmin ≤ t * θ.2 := mul_le_mul_of_nonneg_left hBθ.le htpos.le
    show qDual M μ θ s ≤ qDual M μ θ t
    linarith

end CAProp2Aux

theorem solution (M : Model) (hM : M.Standing) :
    ∃ μ : (Fin M.d → ℝ) × ℝ → ℝ, IsPacing M μ ∧
      ∀ᵐ θ ∂M.G, 0 ≤ μ θ ∧ IsMinOn (qDual M μ θ) (Set.Ici 0) (μ θ) := by
  obtain ⟨⟨hne, hcpt, hconv⟩, -, huhc, hvals⟩ := lemma_4 M hM
  obtain ⟨g, hgK, hgfix⟩ := FanGlicksberg.kakutani_fan_glicksberg (X0L M) hne hcpt hconv
    (C0starL M) huhc (fun _ _ _ hh => hh.1) (fun x hx => (hvals x hx).1)
    (fun x hx => (hvals x hx).2.1) (fun x hx => (hvals x hx).2.2.isClosed)
  obtain ⟨μ, hμX0, hgμ⟩ := hgK
  have hgμG := CAProp2Aux.ae_G_of_ae_vol M hM hgμ
  have hfix : μ ∈ C0star M μ := by
    refine ⟨hμX0, fun ν hν => ?_⟩
    have hνint : IntegrableOn ν (Theta M) := hν.1.2.1
    let k : L1Theta M := hνint.toL1 ν
    have hk : (k : (Fin M.d → ℝ) × ℝ → ℝ) =ᵐ[volume.restrict (Theta M)] ν :=
      Integrable.coeFn_toL1 hνint
    have hkX : k ∈ X0L M := ⟨ν, hν, hk⟩
    have h := hgfix.2 k hkX
    unfold fL at h
    rwa [CAProp2Aux.fObj_congr M hM hgμG hgμG,
      CAProp2Aux.fObj_congr M hM hgμG (CAProp2Aux.ae_G_of_ae_vol M hM hk)] at h
  have h5 := lemma_5 M hM μ hμX0 hfix
  have hΘ : ∀ᵐ θ ∂M.G, θ ∈ Theta M := ae_iff.mpr hM.G_Theta
  refine ⟨μ, hμX0.1.1, ?_⟩
  filter_upwards [h5, hΘ] with θ h hθ
  exact ⟨h.1.1, CAProp2Aux.isMinOn_Ici M hM μ hθ h.1 h.2⟩
