-- Prove2me | solution 1 for GenCostSched.GFCS.dual_attainment
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:10:14.236074+00:00
-- url     : https://prove2.me/submissions/d78a2043-816f-4d9f-9e22-8ad37485d75c

import Mathlib
import Definitions.Def_GenCostSched_GFCS_Model

open MeasureTheory Set Filter
open scoped ENNReal Topology

open GenCostSched.GFCS

/-! ### Basic properties of cost functions on `[s, ∞)` -/

private lemma g_nonneg {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (hA : ∀ j ∈ A, I.r j ≤ s) {j : Fin m} (hj : j ∈ A) {t : ℝ}
    (ht : s ≤ t) : 0 ≤ I.g j t :=
  (hI j).2.2.1 t ((hA j hj).trans ht)

private lemma g_monoOn {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (hA : ∀ j ∈ A, I.r j ≤ s) {j : Fin m} (hj : j ∈ A) :
    MonotoneOn (I.g j) (Ici s) :=
  (hI j).2.2.2.1.mono (Ici_subset_Ici.mpr (hA j hj))

private lemma g_continuousOn {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (hA : ∀ j ∈ A, I.r j ≤ s) {j : Fin m} (hj : j ∈ A) :
    ContinuousOn (I.g j) (Ici s) := by
  have hcont : ContinuousOn (I.g j) (Ici (I.r j)) :=
    fun t ht => ((hI j).2.2.2.2.2 t ht).continuousWithinAt
  exact hcont.mono (Ici_subset_Ici.mpr (hA j hj))

private lemma measurable_indicator_of_continuousOn {S : Set ℝ} (hS : MeasurableSet S)
    {f : ℝ → ℝ} (hf : ContinuousOn f S) : Measurable (S.indicator f) := by
  refine measurable_of_isOpen fun U hU => ?_
  have h1 : MeasurableSet (Subtype.val '' (S.domRestrict f ⁻¹' U) : Set ℝ) :=
    (MeasurableEmbedding.subtype_coe hS).measurableSet_image.mpr
      (hf.domRestrict.measurable hU.measurableSet)
  by_cases h0 : (0 : ℝ) ∈ U
  · have heq : S.indicator f ⁻¹' U = (Subtype.val '' (S.domRestrict f ⁻¹' U)) ∪ Sᶜ := by
      ext t
      by_cases ht : t ∈ S
      · simp [ht]
      · simp [ht, h0]
    rw [heq]
    exact h1.union hS.compl
  · have heq : S.indicator f ⁻¹' U = Subtype.val '' (S.domRestrict f ⁻¹' U) := by
      ext t
      by_cases ht : t ∈ S
      · simp [ht]
      · simp [ht, h0]
    rw [heq]
    exact h1

/-! ### Back-to-back schedule helper -/

private noncomputable def btStart {m : ℕ} (u : ℝ) (A : Finset (Fin m)) (d : Fin m → ℝ)
    (j : Fin m) : ℝ :=
  u + ∑ i ∈ A.filter (· < j), d i

private noncomputable def btSched {m : ℕ} (u : ℝ) (A : Finset (Fin m)) (d : Fin m → ℝ)
    (j : Fin m) : ℝ → ℝ :=
  if j ∈ A then (Ico (btStart u A d j) (btStart u A d j + d j)).indicator (fun _ => 1) else 0

private lemma btStart_ge {m : ℕ} (u : ℝ) (A : Finset (Fin m)) (d : Fin m → ℝ)
    (hd : ∀ j ∈ A, 0 ≤ d j) (j : Fin m) : u ≤ btStart u A d j := by
  unfold btStart
  have h : 0 ≤ ∑ i ∈ A.filter (· < j), d i :=
    Finset.sum_nonneg (fun i hi => hd i (Finset.mem_filter.mp hi).1)
  linarith

private lemma btStart_add_le {m : ℕ} (u : ℝ) (A : Finset (Fin m)) (d : Fin m → ℝ)
    (hd : ∀ j ∈ A, 0 ≤ d j) {j : Fin m} (hj : j ∈ A) :
    btStart u A d j + d j ≤ u + ∑ i ∈ A, d i := by
  unfold btStart
  have hsub : insert j (A.filter (· < j)) ⊆ A := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact hj
    · exact (Finset.mem_filter.mp hi').1
  have hnotmem : j ∉ A.filter (· < j) := by simp
  have hsum : (∑ i ∈ A.filter (· < j), d i) + d j ≤ ∑ i ∈ A, d i := by
    rw [add_comm, ← Finset.sum_insert hnotmem]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hd i hi)
  linarith

private lemma btStart_add_le_btStart {m : ℕ} (u : ℝ) (A : Finset (Fin m)) (d : Fin m → ℝ)
    (hd : ∀ j ∈ A, 0 ≤ d j) {i j : Fin m} (hi : i ∈ A) (hij : i < j) :
    btStart u A d i + d i ≤ btStart u A d j := by
  unfold btStart
  have hsub : insert i (A.filter (· < i)) ⊆ A.filter (· < j) := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk'
    · exact Finset.mem_filter.mpr ⟨hi, hij⟩
    · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk').1,
        (Finset.mem_filter.mp hk').2.trans hij⟩
  have hnotmem : i ∉ A.filter (· < i) := by simp
  have hsum : (∑ k ∈ A.filter (· < i), d k) + d i ≤ ∑ k ∈ A.filter (· < j), d k := by
    rw [add_comm, ← Finset.sum_insert hnotmem]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k hk _ => hd k (Finset.mem_filter.mp hk).1)
  linarith

private lemma btSched_measurable {m : ℕ} (u : ℝ) (A : Finset (Fin m)) (d : Fin m → ℝ)
    (j : Fin m) : Measurable (btSched u A d j) := by
  unfold btSched
  split_ifs
  · exact measurable_const.indicator measurableSet_Ico
  · exact measurable_const

private lemma btSched_nonneg {m : ℕ} (u : ℝ) (A : Finset (Fin m)) (d : Fin m → ℝ)
    (j : Fin m) (t : ℝ) : 0 ≤ btSched u A d j t := by
  unfold btSched
  split_ifs
  · exact indicator_nonneg (fun _ _ => zero_le_one) t
  · rfl

private lemma btSched_le_one {m : ℕ} (u : ℝ) (A : Finset (Fin m)) (d : Fin m → ℝ)
    (j : Fin m) (t : ℝ) : btSched u A d j t ≤ 1 := by
  unfold btSched
  split_ifs
  · by_cases ht : t ∈ Ico (btStart u A d j) (btStart u A d j + d j)
    · simp [indicator_of_mem ht]
    · simp [indicator_of_notMem ht]
  · exact zero_le_one

private lemma btSched_eq_zero_of_notMem {m : ℕ} (u : ℝ) (A : Finset (Fin m)) (d : Fin m → ℝ)
    {j : Fin m} (hj : j ∉ A) (t : ℝ) : btSched u A d j t = 0 := by
  simp [btSched, hj]

private lemma btSched_eq_zero_of_lt {m : ℕ} (u : ℝ) (A : Finset (Fin m)) (d : Fin m → ℝ)
    (hd : ∀ j ∈ A, 0 ≤ d j) (j : Fin m) {t : ℝ} (ht : t < u) : btSched u A d j t = 0 := by
  unfold btSched
  split_ifs with hj
  · apply indicator_of_notMem
    intro hmem
    linarith [hmem.1, btStart_ge u A d hd j]
  · rfl

private lemma btSched_eq_zero_of_ge {m : ℕ} (u : ℝ) (A : Finset (Fin m)) (d : Fin m → ℝ)
    (hd : ∀ j ∈ A, 0 ≤ d j) (j : Fin m) {t : ℝ} (ht : u + ∑ i ∈ A, d i ≤ t) :
    btSched u A d j t = 0 := by
  unfold btSched
  split_ifs with hj
  · apply indicator_of_notMem
    intro hmem
    linarith [hmem.2, btStart_add_le u A d hd hj]
  · rfl

private lemma btSched_sum_le_one {m : ℕ} (u : ℝ) (A : Finset (Fin m)) (d : Fin m → ℝ)
    (hd : ∀ j ∈ A, 0 ≤ d j) (t : ℝ) : ∑ j, btSched u A d j t ≤ 1 := by
  by_cases hne : ∃ j, btSched u A d j t ≠ 0
  · obtain ⟨j, hjne⟩ := hne
    have huniq : ∀ i, i ≠ j → btSched u A d i t = 0 := by
      intro i hij
      by_contra hine
      have hiA : i ∈ A := by
        by_contra h; exact hine (btSched_eq_zero_of_notMem u A d h t)
      have hjA : j ∈ A := by
        by_contra h; exact hjne (btSched_eq_zero_of_notMem u A d h t)
      have hti : t ∈ Ico (btStart u A d i) (btStart u A d i + d i) := by
        by_contra h; exact hine (by simp [btSched, hiA, indicator_of_notMem h])
      have htj : t ∈ Ico (btStart u A d j) (btStart u A d j + d j) := by
        by_contra h; exact hjne (by simp [btSched, hjA, indicator_of_notMem h])
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · linarith [hti.2, htj.1, btStart_add_le_btStart u A d hd hiA hlt]
      · linarith [htj.2, hti.1, btStart_add_le_btStart u A d hd hjA hgt]
    rw [Finset.sum_eq_single j (fun i _ hij => huniq i hij) (by simp)]
    exact btSched_le_one u A d j t
  · push Not at hne
    simp [hne]

private lemma btSched_lintegral {m : ℕ} (u : ℝ) (A : Finset (Fin m)) (d : Fin m → ℝ)
    (_hd : ∀ j ∈ A, 0 ≤ d j) {j : Fin m} (hj : j ∈ A) :
    ∫⁻ t, ENNReal.ofReal (btSched u A d j t) = ENNReal.ofReal (d j) := by
  have heq : (fun t => ENNReal.ofReal (btSched u A d j t)) =
      (Ico (btStart u A d j) (btStart u A d j + d j)).indicator (fun _ => (1 : ℝ≥0∞)) := by
    ext t
    simp only [btSched, hj, ↓reduceIte]
    by_cases ht : t ∈ Ico (btStart u A d j) (btStart u A d j + d j)
    · simp [indicator_of_mem ht]
    · simp [indicator_of_notMem ht]
  rw [heq, lintegral_indicator measurableSet_Ico, setLIntegral_const, one_mul,
    Real.volume_Ico, add_sub_cancel_left]

private lemma btSched_setIntegral {m : ℕ} (u T : ℝ) (A : Finset (Fin m)) (d : Fin m → ℝ)
    (hd : ∀ j ∈ A, 0 ≤ d j) (hT : u + ∑ i ∈ A, d i ≤ T) {j : Fin m} (hj : j ∈ A) :
    ∫ t in Ico u T, btSched u A d j t = d j := by
  have hsub : Ico (btStart u A d j) (btStart u A d j + d j) ⊆ Ico u T := by
    intro t ht
    exact ⟨(btStart_ge u A d hd j).trans ht.1,
      ht.2.trans_le ((btStart_add_le u A d hd hj).trans hT)⟩
  simp only [btSched, hj, ↓reduceIte]
  rw [setIntegral_indicator measurableSet_Ico, inter_eq_right.mpr hsub, setIntegral_const,
    smul_eq_mul, mul_one, Measure.real, Real.volume_Ico, add_sub_cancel_left,
    ENNReal.toReal_ofReal (hd j hj)]

private lemma btSched_cost_le {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s u U : ℝ)
    (A : Finset (Fin m)) (hA : ∀ j ∈ A, I.r j ≤ s) (d : Fin m → ℝ) (hd : ∀ j ∈ A, 0 ≤ d j)
    (hsu : s ≤ u) (hU : u + ∑ i ∈ A, d i ≤ U) :
    offCost I.g (btSched u A d) ≤ ENNReal.ofReal (∑ j ∈ A, I.g j U * d j) := by
  have hsuU : s ≤ U :=
    hsu.trans (le_trans (by linarith [Finset.sum_nonneg (fun i hi => hd i hi)]) hU)
  unfold offCost
  rw [ENNReal.ofReal_sum_of_nonneg (fun j hj => mul_nonneg (g_nonneg I hI s A hA hj hsuU) (hd j hj))]
  calc
    ∑ j : Fin m, ∫⁻ t, ENNReal.ofReal (I.g j t * btSched u A d j t)
        = ∑ j ∈ A, ∫⁻ t, ENNReal.ofReal (I.g j t * btSched u A d j t) := by
          symm
          apply Finset.sum_subset (Finset.subset_univ A)
          intro j _ hj
          simp [btSched_eq_zero_of_notMem u A d hj]
    _ ≤ ∑ j ∈ A, ENNReal.ofReal (I.g j U * d j) := by
          refine Finset.sum_le_sum fun j hj => ?_
          calc
            ∫⁻ t, ENNReal.ofReal (I.g j t * btSched u A d j t)
                ≤ ∫⁻ t, ENNReal.ofReal (I.g j U * btSched u A d j t) := by
                  refine lintegral_mono fun t => ENNReal.ofReal_le_ofReal ?_
                  by_cases ht : t ∈ Ico (btStart u A d j) (btStart u A d j + d j)
                  · have hst : s ≤ t := hsu.trans ((btStart_ge u A d hd j).trans ht.1)
                    have htU : t ≤ U := ht.2.le.trans ((btStart_add_le u A d hd hj).trans hU)
                    have hg : I.g j t ≤ I.g j U := g_monoOn I hI s A hA hj hst hsuU htU
                    exact mul_le_mul_of_nonneg_right hg (btSched_nonneg u A d j t)
                  · simp [btSched, hj, indicator_of_notMem ht]
            _ = ∫⁻ t, ENNReal.ofReal (I.g j U) * ENNReal.ofReal (btSched u A d j t) := by
                  refine lintegral_congr fun t => ?_
                  exact ENNReal.ofReal_mul (g_nonneg I hI s A hA hj hsuU)
            _ = ENNReal.ofReal (I.g j U) * ∫⁻ t, ENNReal.ofReal (btSched u A d j t) :=
                  lintegral_const_mul _ ((btSched_measurable u A d j).ennreal_ofReal)
            _ = ENNReal.ofReal (I.g j U) * ENNReal.ofReal (d j) := by
                  rw [btSched_lintegral u A d hd hj]
            _ = ENNReal.ofReal (I.g j U * d j) :=
                  (ENNReal.ofReal_mul (g_nonneg I hI s A hA hj hsuU)).symm

private lemma rnf_ne_top {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (ρ : Fin m → ℝ) (hA : ∀ j ∈ A, I.r j ≤ s) (hρ : ∀ j ∈ A, 0 < ρ j) :
    rnf I.g s A ρ ≠ ⊤ := by
  have hρ0 : ∀ j ∈ A, 0 ≤ ρ j := fun j hj => (hρ j hj).le
  let x := btSched s A ρ
  have hx : IsOffFracSched s A ρ x :=
    ⟨btSched_measurable s A ρ, btSched_nonneg s A ρ,
      fun j t ht => btSched_eq_zero_of_lt s A ρ hρ0 j ht,
      fun j hj t => btSched_eq_zero_of_notMem s A ρ hj t,
      btSched_sum_le_one s A ρ hρ0,
      fun j hj => (btSched_lintegral s A ρ hρ0 hj).symm.le⟩
  have hle : rnf I.g s A ρ ≤ offCost I.g x := sInf_le ⟨x, hx, rfl⟩
  have hfin : offCost I.g x ≤ ENNReal.ofReal (∑ j ∈ A, I.g j (s + ∑ i ∈ A, ρ i) * ρ j) :=
    btSched_cost_le I hI s s (s + ∑ i ∈ A, ρ i) A hA ρ hρ0 le_rfl le_rfl
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle.trans hfin)

/-! ### Offline weak duality -/

private lemma off_weak_duality_aux {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (ρ : Fin m → ℝ) (hA : ∀ j ∈ A, I.r j ≤ s) (hρ : ∀ j ∈ A, 0 < ρ j)
    {a : Fin m → ℝ} {β : ℝ → ℝ} (hfeas : IsOffDualFeas I.g s A a β)
    {x : Fin m → ℝ → ℝ} (hx : IsOffFracSched s A ρ x) :
    ENNReal.ofReal (∑ j ∈ A, a j * ρ j) ≤ ENNReal.ofReal (∫ t in Ici s, β t) + offCost I.g x := by
  set μ : Measure ℝ := volume.restrict (Ici s)
  have hβ_int : Integrable β μ := hfeas.1
  have hβ_nn : ∀ᵐ t ∂μ, 0 ≤ β t := (ae_restrict_iff' measurableSet_Ici).mpr hfeas.2.2.1
  have h_each : ∀ j ∈ A,
      ENNReal.ofReal (a j * ρ j) ≤
        (∫⁻ t, ENNReal.ofReal (β t * x j t) ∂μ) +
          ∫⁻ t, ENNReal.ofReal (I.g j t * x j t) ∂μ := by
    intro j hj
    have haj : 0 ≤ a j := hfeas.2.1 j hj
    have hconstr : ∀ᵐ t ∂μ, a j ≤ β t + I.g j t :=
      (ae_restrict_iff' measurableSet_Ici).mpr (hfeas.2.2.2 j hj)
    have hmem : ∀ᵐ t ∂μ, s ≤ t := ae_restrict_mem measurableSet_Ici
    have hx_eq : ∫⁻ t, ENNReal.ofReal (x j t) = ∫⁻ t, ENNReal.ofReal (x j t) ∂μ := by
      have hind : (fun t => ENNReal.ofReal (x j t)) =
          (Ici s).indicator (fun t => ENNReal.ofReal (x j t)) := by
        ext t
        by_cases ht : t ∈ Ici s
        · rw [indicator_of_mem ht]
        · rw [indicator_of_notMem ht, hx.2.2.1 j t (not_le.mp ht), ENNReal.ofReal_zero]
      conv_lhs => rw [hind]
      exact lintegral_indicator measurableSet_Ici _
    have h1 : ENNReal.ofReal (a j * ρ j) ≤ ∫⁻ t, ENNReal.ofReal (a j * x j t) ∂μ := by
      calc
        ENNReal.ofReal (a j * ρ j)
            = ENNReal.ofReal (a j) * ENNReal.ofReal (ρ j) := ENNReal.ofReal_mul haj
        _ ≤ ENNReal.ofReal (a j) * ∫⁻ t, ENNReal.ofReal (x j t) ∂μ := by
              rw [← hx_eq]; gcongr; exact hx.2.2.2.2.2 j hj
        _ = ∫⁻ t, ENNReal.ofReal (a j) * ENNReal.ofReal (x j t) ∂μ :=
              (lintegral_const_mul _ (hx.1 j).ennreal_ofReal).symm
        _ = ∫⁻ t, ENNReal.ofReal (a j * x j t) ∂μ :=
              lintegral_congr fun t => (ENNReal.ofReal_mul haj).symm
    have h2 : ∀ᵐ t ∂μ, ENNReal.ofReal (a j * x j t) ≤
        ENNReal.ofReal (β t * x j t) + ENNReal.ofReal (I.g j t * x j t) := by
      filter_upwards [hβ_nn, hconstr, hmem] with t htβ htc hts
      have hxt : 0 ≤ x j t := hx.2.1 j t
      have hgt : 0 ≤ I.g j t := g_nonneg I hI s A hA hj hts
      rw [← ENNReal.ofReal_add (mul_nonneg htβ hxt) (mul_nonneg hgt hxt)]
      apply ENNReal.ofReal_le_ofReal
      nlinarith
    have hmeas_bx : AEMeasurable (fun t => ENNReal.ofReal (β t * x j t)) μ :=
      (hβ_int.aestronglyMeasurable.mul (hx.1 j).aestronglyMeasurable).aemeasurable.ennreal_ofReal
    calc
      ENNReal.ofReal (a j * ρ j)
          ≤ ∫⁻ t, ENNReal.ofReal (a j * x j t) ∂μ := h1
      _ ≤ ∫⁻ t, (ENNReal.ofReal (β t * x j t) + ENNReal.ofReal (I.g j t * x j t)) ∂μ :=
            lintegral_mono_ae h2
      _ = (∫⁻ t, ENNReal.ofReal (β t * x j t) ∂μ) +
            ∫⁻ t, ENNReal.ofReal (I.g j t * x j t) ∂μ :=
            lintegral_add_left' hmeas_bx _
  calc
    ENNReal.ofReal (∑ j ∈ A, a j * ρ j)
        = ∑ j ∈ A, ENNReal.ofReal (a j * ρ j) :=
          ENNReal.ofReal_sum_of_nonneg (fun j hj => mul_nonneg (hfeas.2.1 j hj) (hρ j hj).le)
    _ ≤ ∑ j ∈ A, ((∫⁻ t, ENNReal.ofReal (β t * x j t) ∂μ) +
          ∫⁻ t, ENNReal.ofReal (I.g j t * x j t) ∂μ) :=
          Finset.sum_le_sum h_each
    _ = (∑ j ∈ A, ∫⁻ t, ENNReal.ofReal (β t * x j t) ∂μ) +
          ∑ j ∈ A, ∫⁻ t, ENNReal.ofReal (I.g j t * x j t) ∂μ :=
          Finset.sum_add_distrib
    _ ≤ ENNReal.ofReal (∫ t in Ici s, β t) + offCost I.g x := by
          gcongr
          · have hsum_lint : ∫⁻ t, ∑ j ∈ A, ENNReal.ofReal (β t * x j t) ∂μ =
                ∑ j ∈ A, ∫⁻ t, ENNReal.ofReal (β t * x j t) ∂μ :=
              lintegral_finsetSum' A (fun j _ =>
                (hβ_int.aestronglyMeasurable.mul
                  (hx.1 j).aestronglyMeasurable).aemeasurable.ennreal_ofReal)
            rw [← hsum_lint, ofReal_integral_eq_lintegral_ofReal hβ_int hβ_nn]
            refine lintegral_mono_ae ?_
            filter_upwards [hβ_nn] with t htβ
            rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg htβ (hx.2.1 j t)),
              ← Finset.mul_sum]
            apply ENNReal.ofReal_le_ofReal
            have hsumA : ∑ j ∈ A, x j t ≤ 1 :=
              (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
                (fun j _ _ => hx.2.1 j t)).trans (hx.2.2.2.2.1 t)
            nlinarith
          · unfold offCost
            calc
              ∑ j ∈ A, ∫⁻ t, ENNReal.ofReal (I.g j t * x j t) ∂μ
                  ≤ ∑ j ∈ A, ∫⁻ t, ENNReal.ofReal (I.g j t * x j t) :=
                    Finset.sum_le_sum fun j _ => setLIntegral_le_lintegral _ _
              _ ≤ ∑ j : Fin m, ∫⁻ t, ENNReal.ofReal (I.g j t * x j t) :=
                    Finset.sum_le_sum_of_subset (Finset.subset_univ A)

private lemma off_weak_duality {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (ρ : Fin m → ℝ) (hA : ∀ j ∈ A, I.r j ≤ s) (hρ : ∀ j ∈ A, 0 < ρ j)
    {a : Fin m → ℝ} {β : ℝ → ℝ} (hfeas : IsOffDualFeas I.g s A a β) :
    offDualObj s A ρ a β ≤ (rnf I.g s A ρ).toReal := by
  have hle : ENNReal.ofReal (∑ j ∈ A, a j * ρ j) - ENNReal.ofReal (∫ t in Ici s, β t) ≤
      rnf I.g s A ρ := by
    apply le_sInf
    rintro _ ⟨x, hx, rfl⟩
    exact tsub_le_iff_left.mpr (off_weak_duality_aux I hI s A ρ hA hρ hfeas hx)
  have hle' : ENNReal.ofReal (∑ j ∈ A, a j * ρ j) ≤
      ENNReal.ofReal (∫ t in Ici s, β t) + rnf I.g s A ρ := tsub_le_iff_left.mp hle
  have hβ_int_nn : 0 ≤ ∫ t in Ici s, β t :=
    setIntegral_nonneg_ae measurableSet_Ici hfeas.2.2.1
  have hrnf_fin : rnf I.g s A ρ ≠ ⊤ := rnf_ne_top I hI s A ρ hA hρ
  rw [← ENNReal.ofReal_toReal hrnf_fin,
    ← ENNReal.ofReal_add hβ_int_nn ENNReal.toReal_nonneg] at hle'
  have hreal : ∑ j ∈ A, a j * ρ j ≤ (∫ t in Ici s, β t) + (rnf I.g s A ρ).toReal :=
    (ENNReal.ofReal_le_ofReal_iff (add_nonneg hβ_int_nn ENNReal.toReal_nonneg)).mp hle'
  unfold offDualObj
  linarith

/-! ### Integrability helpers on `[s, T)` -/

private lemma integrableOn_sched_Ico (s T : ℝ) {f : ℝ → ℝ} (hm : Measurable f)
    (h0 : ∀ t, 0 ≤ f t) (h1 : ∀ t, f t ≤ 1) : IntegrableOn f (Ico s T) := by
  refine Integrable.mono' (integrableOn_const (C := (1 : ℝ)) (hs := measure_Ico_lt_top.ne))
    hm.aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (h0 t)]
  exact h1 t

private lemma integrableOn_cost_Ico {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j)
    (s T : ℝ) (A : Finset (Fin m)) (hA : ∀ j ∈ A, I.r j ≤ s) (hsT : s ≤ T)
    {j : Fin m} (hj : j ∈ A) {f : ℝ → ℝ} (hm : Measurable f)
    (h0 : ∀ t, 0 ≤ f t) (h1 : ∀ t, f t ≤ 1) :
    IntegrableOn (fun t => I.g j t * f t) (Ico s T) := by
  have hgm : AEStronglyMeasurable (I.g j) (volume.restrict (Ico s T)) :=
    ((g_continuousOn I hI s A hA hj).mono Ico_subset_Ici_self).aestronglyMeasurable
      measurableSet_Ico
  refine Integrable.mono' (integrableOn_const (C := I.g j T) (hs := measure_Ico_lt_top.ne))
    (hgm.mul hm.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
  have hgt_nn : 0 ≤ I.g j t := g_nonneg I hI s A hA hj ht.1
  have hgt_le : I.g j t ≤ I.g j T := g_monoOn I hI s A hA hj ht.1 hsT ht.2.le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hgt_nn (h0 t))]
  nlinarith [h0 t, h1 t, hgt_nn]

/-! ### Strong duality (near-optimal duals via finite-dimensional Hahn–Banach) -/

private lemma continuousOn_max {S : Set ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f S) (hg : ContinuousOn g S) :
    ContinuousOn (fun t => max (f t) (g t)) S :=
  continuous_max.comp_continuousOn (hf.prodMk hg)

private lemma continuousOn_sup' {ι : Type*} (A : Finset ι) (hA : A.Nonempty)
    {S : Set ℝ} {f : ι → ℝ → ℝ} (hf : ∀ j ∈ A, ContinuousOn (f j) S) :
    ContinuousOn (fun t => A.sup' hA (fun j => f j t)) S := by
  induction hA using Finset.Nonempty.cons_induction with
  | singleton a =>
    simpa using hf a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
    have h1 : ContinuousOn (f a) S := hf a (Finset.mem_cons_self a s)
    have h2 : ContinuousOn (fun t => s.sup' hs (fun j => f j t)) S :=
      ih (fun j hj => hf j (Finset.mem_cons_of_mem hj))
    have heq : (fun t => (Finset.cons a s ha).sup' (Finset.cons_nonempty ha) (fun j => f j t)) =
        fun t => max (f a t) (s.sup' hs (fun j => f j t)) := by
      ext t; rw [Finset.sup'_cons]
    rw [heq]
    exact continuousOn_max h1 h2

private lemma measurable_sup' {ι : Type*} (A : Finset ι) (hA : A.Nonempty)
    {f : ι → ℝ → ℝ} (hf : ∀ j ∈ A, Measurable (f j)) :
    Measurable (fun t => A.sup' hA (fun j => f j t)) := by
  induction hA using Finset.Nonempty.cons_induction with
  | singleton a =>
    simpa using hf a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
    have h1 : Measurable (f a) := hf a (Finset.mem_cons_self a s)
    have h2 : Measurable (fun t => s.sup' hs (fun j => f j t)) :=
      ih (fun j hj => hf j (Finset.mem_cons_of_mem hj))
    have heq : (fun t => (Finset.cons a s ha).sup' (Finset.cons_nonempty ha) (fun j => f j t)) =
        fun t => max (f a t) (s.sup' hs (fun j => f j t)) := by
      ext t; rw [Finset.sup'_cons]
    rw [heq]
    exact h1.max h2

private lemma exists_near_opt_dual {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (hA_ne : A.Nonempty) (ρ : Fin m → ℝ) (hA : ∀ j ∈ A, I.r j ≤ s)
    (hρ : ∀ j ∈ A, 0 < ρ j) {ε : ℝ} (hε : 0 < ε) :
    ∃ (a : Fin m → ℝ) (β : ℝ → ℝ), IsOffDualFeas I.g s A a β ∧
      (rnf I.g s A ρ).toReal - ε ≤ offDualObj s A ρ a β := by
  set R : ℝ := ∑ j ∈ A, ρ j
  have hR : 0 < R := Finset.sum_pos hρ hA_ne
  set T : ℝ := s + R + 1
  have hsT : s ≤ T := by linarith
  set V : ℝ := (rnf I.g s A ρ).toReal
  have hrnf_fin : rnf I.g s A ρ ≠ ⊤ := rnf_ne_top I hI s A ρ hA hρ
  -- Finite-dimensional epigraph of feasible (volume, cost) pairs on [s, T)
  let E : Set (({j : Fin m // j ∈ A} → ℝ) × ℝ) :=
    { p | ∃ x : Fin m → ℝ → ℝ,
        (∀ j, Measurable (x j)) ∧
        (∀ j t, 0 ≤ x j t) ∧
        (∀ j, j ∉ A → ∀ t, x j t = 0) ∧
        (∀ j t, t ∉ Ico s T → x j t = 0) ∧
        (∀ t, ∑ j, x j t ≤ 1) ∧
        (∀ j : {j : Fin m // j ∈ A}, p.1 j ≤ ∫ t in Ico s T, x j.1 t) ∧
        (∑ j ∈ A, ∫ t in Ico s T, I.g j t * x j t) ≤ p.2 }
  have hx_le_one : ∀ (x : Fin m → ℝ → ℝ),
      (∀ j t, 0 ≤ x j t) → (∀ t, ∑ j, x j t ≤ 1) → ∀ j t, x j t ≤ 1 := by
    intro x hnn hsum j t
    exact (Finset.single_le_sum (fun i _ => hnn i t) (Finset.mem_univ j)).trans (hsum t)
  -- 1. E is convex
  have hE_conv : Convex ℝ E := by
    rintro p₁ ⟨x₁, hm₁, hnn₁, hout₁, hsupp₁, hsum₁, hw₁, hc₁⟩
      p₂ ⟨x₂, hm₂, hnn₂, hout₂, hsupp₂, hsum₂, hw₂, hc₂⟩ u v hu hv huv
    refine ⟨fun j t => u * x₁ j t + v * x₂ j t, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j; exact (hm₁ j).const_mul u |>.add ((hm₂ j).const_mul v)
    · intro j t; positivity [hnn₁ j t, hnn₂ j t]
    · intro j hj t; simp [hout₁ j hj t, hout₂ j hj t]
    · intro j t ht; simp [hsupp₁ j t ht, hsupp₂ j t ht]
    · intro t
      calc
        ∑ j, (u * x₁ j t + v * x₂ j t)
            = u * (∑ j, x₁ j t) + v * (∑ j, x₂ j t) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ u * 1 + v * 1 := by nlinarith [hsum₁ t, hsum₂ t]
        _ = 1 := by linarith
    · intro j
      have hi₁ := integrableOn_sched_Ico s T (hm₁ j.1) (hnn₁ j.1) (hx_le_one x₁ hnn₁ hsum₁ j.1)
      have hi₂ := integrableOn_sched_Ico s T (hm₂ j.1) (hnn₂ j.1) (hx_le_one x₂ hnn₂ hsum₂ j.1)
      rw [integral_add (hi₁.const_mul u) (hi₂.const_mul v),
        integral_const_mul, integral_const_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (hw₁ j) hu)
        (mul_le_mul_of_nonneg_left (hw₂ j) hv)
    · have hlin : ∀ j ∈ A,
          ∫ t in Ico s T, I.g j t * (u * x₁ j t + v * x₂ j t) =
            u * (∫ t in Ico s T, I.g j t * x₁ j t) +
            v * (∫ t in Ico s T, I.g j t * x₂ j t) := by
        intro j hj
        have h1 := integrableOn_cost_Ico I hI s T A hA hsT hj (hm₁ j) (hnn₁ j)
          (hx_le_one x₁ hnn₁ hsum₁ j)
        have h2 := integrableOn_cost_Ico I hI s T A hA hsT hj (hm₂ j) (hnn₂ j)
          (hx_le_one x₂ hnn₂ hsum₂ j)
        have heq : (fun t => I.g j t * (u * x₁ j t + v * x₂ j t)) =
            fun t => u * (I.g j t * x₁ j t) + v * (I.g j t * x₂ j t) := by
          ext t; ring
        rw [heq, integral_add (h1.const_mul u) (h2.const_mul v),
          integral_const_mul, integral_const_mul]
      rw [Finset.sum_congr rfl hlin, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      exact add_le_add (mul_le_mul_of_nonneg_left hc₁ hu) (mul_le_mul_of_nonneg_left hc₂ hv)
  -- 2. (ρ|_A, V - ε) ∉ closure E
  let p₀ : ({j : Fin m // j ∈ A} → ℝ) × ℝ := (fun j => ρ j.1, V - ε)
  have hp₀ : p₀ ∉ closure E := by
    intro hmem
    set M : ℝ := ∑ j ∈ A, I.g j (T + 1)
    have hM_nn : 0 ≤ M :=
      Finset.sum_nonneg fun j hj => g_nonneg I hI s A hA hj (by linarith)
    set δ : ℝ := min (1 / ((A.card : ℝ) + 1)) (ε / (2 * (M + 1)))
    have hδ_pos : 0 < δ := lt_min (by positivity) (by positivity)
    have hδ_card : (A.card : ℝ) * δ ≤ 1 := by
      have h1 : δ ≤ 1 / ((A.card : ℝ) + 1) := min_le_left _ _
      have h2 : (A.card : ℝ) ≤ (A.card : ℝ) + 1 := by linarith
      have h3 : 0 < (A.card : ℝ) + 1 := by positivity
      calc (A.card : ℝ) * δ ≤ (A.card : ℝ) * (1 / ((A.card : ℝ) + 1)) := by
            gcongr
        _ ≤ ((A.card : ℝ) + 1) * (1 / ((A.card : ℝ) + 1)) := by gcongr
        _ = 1 := by field_simp
    have hδ_eps : δ * (M + 1) < ε := by
      have h1 : δ ≤ ε / (2 * (M + 1)) := min_le_right _ _
      have hM1 : 0 < M + 1 := by linarith
      calc δ * (M + 1) ≤ (ε / (2 * (M + 1))) * (M + 1) := by gcongr
        _ = ε / 2 := by field_simp
        _ < ε := by linarith
    obtain ⟨p, hpE, hdist⟩ := Metric.mem_closure_iff.mp hmem δ hδ_pos
    obtain ⟨x, hm, hnn, hout, hsupp, hsum, hw, hc⟩ := hpE
    have hdist_fst : dist p₀.1 p.1 < δ := (max_lt_iff.mp hdist).1
    have hdist_snd : dist p₀.2 p.2 < δ := (max_lt_iff.mp hdist).2
    have hcoord : ∀ j : {j : Fin m // j ∈ A}, ρ j.1 - p.1 j < δ := by
      intro j
      have hj := (dist_pi_lt_iff hδ_pos).mp hdist_fst j
      rw [Real.dist_eq] at hj
      exact (le_abs_self _).trans_lt hj
    have hp2_lt : p.2 < V - ε + δ := by
      rw [Real.dist_eq] at hdist_snd
      have := (neg_le_abs ((V - ε) - p.2)).trans_lt hdist_snd
      linarith
    let d : Fin m → ℝ := fun j => if hj : j ∈ A then max (ρ j - p.1 ⟨j, hj⟩) 0 else 0
    have hd_nn : ∀ j ∈ A, 0 ≤ d j := fun j hj => by simp [d, hj]
    have hd_le : ∀ j ∈ A, d j ≤ δ := fun j hj => by
      simp only [d, hj, ↓reduceDIte, max_le_iff]
      exact ⟨(hcoord ⟨j, hj⟩).le, hδ_pos.le⟩
    have hd_sum : ∑ j ∈ A, d j ≤ 1 := by
      calc ∑ j ∈ A, d j ≤ ∑ _j ∈ A, δ := Finset.sum_le_sum hd_le
        _ = (A.card : ℝ) * δ := by simp
        _ ≤ 1 := hδ_card
    let z := btSched T A d
    let y : Fin m → ℝ → ℝ := fun j t => x j t + z j t
    have hy_feas : IsOffFracSched s A ρ y := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro j; exact (hm j).add (btSched_measurable T A d j)
      · intro j t; exact add_nonneg (hnn j t) (btSched_nonneg T A d j t)
      · intro j t ht
        have hxt : x j t = 0 := hsupp j t (fun h => not_le.mpr ht h.1)
        have hzt : z j t = 0 := btSched_eq_zero_of_lt T A d hd_nn j (ht.trans_le hsT)
        simp [y, hxt, hzt]
      · intro j hj t
        simp [y, z, hout j hj t, btSched_eq_zero_of_notMem T A d hj t]
      · intro t
        by_cases ht : t < T
        · have hz0 : ∀ j, z j t = 0 := fun j => btSched_eq_zero_of_lt T A d hd_nn j ht
          simp only [y, hz0, add_zero]
          exact hsum t
        · have hx0 : ∀ j, x j t = 0 := fun j => hsupp j t (fun h => ht h.2)
          simp only [y, hx0, zero_add]
          exact btSched_sum_le_one T A d hd_nn t
      · intro j hj
        have hadd : (fun t => ENNReal.ofReal (y j t)) =
            fun t => ENNReal.ofReal (x j t) + ENNReal.ofReal (z j t) := by
          ext t; exact ENNReal.ofReal_add (hnn j t) (btSched_nonneg T A d j t)
        rw [hadd, lintegral_add_left (hm j).ennreal_ofReal]
        have hx_lint : ∫⁻ t, ENNReal.ofReal (x j t) = ENNReal.ofReal (∫ t in Ico s T, x j t) := by
          have hind : (fun t => ENNReal.ofReal (x j t)) =
              (Ico s T).indicator (fun t => ENNReal.ofReal (x j t)) := by
            ext t
            by_cases ht : t ∈ Ico s T
            · rw [indicator_of_mem ht]
            · rw [indicator_of_notMem ht, hsupp j t ht, ENNReal.ofReal_zero]
          rw [hind, lintegral_indicator measurableSet_Ico,
            ofReal_integral_eq_lintegral_ofReal
              (integrableOn_sched_Ico s T (hm j) (hnn j) (hx_le_one x hnn hsum j))
              (Eventually.of_forall (hnn j))]
        rw [hx_lint, btSched_lintegral T A d hd_nn hj]
        have hx_int_nn : 0 ≤ ∫ t in Ico s T, x j t :=
          setIntegral_nonneg measurableSet_Ico (fun t _ => hnn j t)
        rw [← ENNReal.ofReal_add hx_int_nn (hd_nn j hj)]
        apply ENNReal.ofReal_le_ofReal
        have h1 : p.1 ⟨j, hj⟩ ≤ ∫ t in Ico s T, x j t := hw ⟨j, hj⟩
        have h2 : ρ j - p.1 ⟨j, hj⟩ ≤ d j := by simp [d, hj]
        linarith
    -- Cost of y
    have hy_cost : offCost I.g y ≤ ENNReal.ofReal (p.2 + M * δ) := by
      have hsplit : offCost I.g y = offCost I.g x + offCost I.g z := by
        unfold offCost
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j ∈ A
        · have hfun : (fun t => ENNReal.ofReal (I.g j t * y j t)) =
              fun t => ENNReal.ofReal (I.g j t * x j t) + ENNReal.ofReal (I.g j t * z j t) := by
            ext t
            by_cases hst : s ≤ t
            · have hgt := g_nonneg I hI s A hA hj hst
              rw [show I.g j t * y j t = I.g j t * x j t + I.g j t * z j t by ring]
              exact ENNReal.ofReal_add (mul_nonneg hgt (hnn j t))
                (mul_nonneg hgt (btSched_nonneg T A d j t))
            · have hlt : t < s := not_le.mp hst
              have hxt : x j t = 0 := hsupp j t (fun h => hst h.1)
              have hzt : z j t = 0 := btSched_eq_zero_of_lt T A d hd_nn j (hlt.trans_le hsT)
              simp [y, hxt, hzt]
          have hmeas_gx : AEMeasurable (fun t => ENNReal.ofReal (I.g j t * x j t)) volume := by
            have hind : (fun t => ENNReal.ofReal (I.g j t * x j t)) =
                (Ico s T).indicator (fun t => ENNReal.ofReal (I.g j t * x j t)) := by
              ext t
              by_cases ht : t ∈ Ico s T
              · rw [indicator_of_mem ht]
              · rw [indicator_of_notMem ht, hsupp j t ht, mul_zero, ENNReal.ofReal_zero]
            rw [hind]
            have hcont : ContinuousOn (I.g j) (Ico s T) :=
              (g_continuousOn I hI s A hA hj).mono Ico_subset_Ici_self
            exact ((measurable_indicator_of_continuousOn measurableSet_Ico hcont).mul
              (hm j)).ennreal_ofReal.aemeasurable.congr (Eventually.of_forall fun t => by
                by_cases ht : t ∈ Ico s T <;> simp [indicator, ht])
          rw [hfun, lintegral_add_left' hmeas_gx]
        · simp [y, hout j hj]
      have hx_cost : offCost I.g x ≤ ENNReal.ofReal p.2 := by
        unfold offCost
        have hsum_eq : ∑ j : Fin m, ∫⁻ t, ENNReal.ofReal (I.g j t * x j t) =
            ∑ j ∈ A, ENNReal.ofReal (∫ t in Ico s T, I.g j t * x j t) := by
          rw [← Finset.sum_subset (Finset.subset_univ A) (fun j _ hj => by simp [hout j hj])]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hind : (fun t => ENNReal.ofReal (I.g j t * x j t)) =
              (Ico s T).indicator (fun t => ENNReal.ofReal (I.g j t * x j t)) := by
            ext t
            by_cases ht : t ∈ Ico s T
            · rw [indicator_of_mem ht]
            · rw [indicator_of_notMem ht, hsupp j t ht, mul_zero, ENNReal.ofReal_zero]
          rw [hind, lintegral_indicator measurableSet_Ico,
            ← ofReal_integral_eq_lintegral_ofReal
              (integrableOn_cost_Ico I hI s T A hA hsT hj (hm j) (hnn j)
                (hx_le_one x hnn hsum j))
              ((ae_restrict_iff' measurableSet_Ico).mpr
                (Eventually.of_forall fun t ht =>
                  mul_nonneg (g_nonneg I hI s A hA hj ht.1) (hnn j t)))]
        rw [hsum_eq, ← ENNReal.ofReal_sum_of_nonneg (fun j hj =>
          setIntegral_nonneg measurableSet_Ico fun t ht =>
            mul_nonneg (g_nonneg I hI s A hA hj ht.1) (hnn j t))]
        exact ENNReal.ofReal_le_ofReal hc
      have hz_cost : offCost I.g z ≤ ENNReal.ofReal (M * δ) := by
        calc
          offCost I.g z ≤ ENNReal.ofReal (∑ j ∈ A, I.g j (T + 1) * d j) :=
            btSched_cost_le I hI s T (T + 1) A hA d hd_nn hsT (by linarith)
          _ ≤ ENNReal.ofReal (M * δ) := by
            apply ENNReal.ofReal_le_ofReal
            calc ∑ j ∈ A, I.g j (T + 1) * d j
                ≤ ∑ j ∈ A, I.g j (T + 1) * δ :=
                  Finset.sum_le_sum fun j hj =>
                    mul_le_mul_of_nonneg_left (hd_le j hj)
                      (g_nonneg I hI s A hA hj (by linarith))
              _ = M * δ := by rw [← Finset.sum_mul]
      have hp2_nn : 0 ≤ p.2 :=
        le_trans (Finset.sum_nonneg fun j hj =>
          setIntegral_nonneg measurableSet_Ico fun t ht =>
            mul_nonneg (g_nonneg I hI s A hA hj ht.1) (hnn j t)) hc
      rw [hsplit, ENNReal.ofReal_add hp2_nn (mul_nonneg hM_nn hδ_pos.le)]
      exact add_le_add hx_cost hz_cost
    have hrnf_le_y : rnf I.g s A ρ ≤ offCost I.g y := sInf_le ⟨y, hy_feas, rfl⟩
    have hrnf_le : rnf I.g s A ρ ≤ ENNReal.ofReal (p.2 + M * δ) := hrnf_le_y.trans hy_cost
    have hp2_nn : 0 ≤ p.2 :=
      le_trans (Finset.sum_nonneg fun j hj =>
        setIntegral_nonneg measurableSet_Ico fun t ht =>
          mul_nonneg (g_nonneg I hI s A hA hj ht.1) (hnn j t)) hc
    have hV_le : V ≤ p.2 + M * δ := by
      rw [← ENNReal.ofReal_toReal hrnf_fin] at hrnf_le
      exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg hp2_nn (mul_nonneg hM_nn hδ_pos.le))).mp hrnf_le
    linarith
  -- 3. Apply geometric Hahn–Banach separation
  obtain ⟨f, u, hfE, hfp₀⟩ :=
    geometric_hahn_banach_closed_point hE_conv.closure isClosed_closure hp₀
  let a₀ : Fin m → ℝ := fun j => if hj : j ∈ A then f (Pi.single ⟨j, hj⟩ 1, 0) else 0
  let γ : ℝ := f (0, 1)
  have hf_eq : ∀ p : ({j : Fin m // j ∈ A} → ℝ) × ℝ,
      f p = (∑ j : {j : Fin m // j ∈ A}, a₀ j.1 * p.1 j) + γ * p.2 := by
    intro p
    have hp_decomp : p =
        (∑ j : {j : Fin m // j ∈ A}, p.1 j • (Pi.single j (1 : ℝ), (0 : ℝ))) +
          p.2 • ((0 : {j : Fin m // j ∈ A} → ℝ), (1 : ℝ)) := by
      apply Prod.ext
      · ext k
        simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, smul_zero, add_zero,
          Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
          mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      · simp [Prod.snd_sum]
    conv_lhs => rw [hp_decomp]
    rw [map_add, map_sum, map_smul, smul_eq_mul, mul_comm p.2 γ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    simp [a₀, j.2]
  have hzero_in : ∀ (w : {j : Fin m // j ∈ A} → ℝ) (c : ℝ),
      (∀ j, w j ≤ 0) → 0 ≤ c → (w, c) ∈ E := by
    intro w c hw hc
    refine ⟨0, fun _ => measurable_const, fun _ _ => le_rfl, fun _ _ _ => rfl,
      fun _ _ _ => rfl, fun _ => by simp, fun j => by simpa using hw j, by simpa using hc⟩
  -- Sign of γ: γ ≤ 0
  have hγ_le : γ ≤ 0 := by
    by_contra h
    push Not at h
    set t := max 0 (u / γ + 1)
    have ht0 : 0 ≤ t := le_max_left _ _
    have hmem : ((0 : {j : Fin m // j ∈ A} → ℝ), t) ∈ closure E :=
      subset_closure (hzero_in 0 t (fun _ => le_rfl) ht0)
    have hlt := hfE _ hmem
    rw [hf_eq] at hlt
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add] at hlt
    have : u + γ ≤ γ * t := by
      have ht1 : u / γ + 1 ≤ t := le_max_right _ _
      have := mul_le_mul_of_nonneg_left ht1 h.le
      have hcancel : γ * (u / γ + 1) = u + γ := by field_simp
      linarith
    linarith
  -- Sign of a₀: a₀ j ≥ 0 for j ∈ A
  have ha₀_nn : ∀ j ∈ A, 0 ≤ a₀ j := by
    intro j hj
    by_contra h
    push Not at h
    set t := max 0 (u / (-a₀ j) + 1)
    have ht0 : 0 ≤ t := le_max_left _ _
    let w : {k : Fin m // k ∈ A} → ℝ := fun k => if k = ⟨j, hj⟩ then -t else 0
    have hw : ∀ k, w k ≤ 0 := fun k => by simp only [w]; split_ifs <;> linarith
    have hmem : (w, (0 : ℝ)) ∈ closure E := subset_closure (hzero_in w 0 hw le_rfl)
    have hlt := hfE _ hmem
    rw [hf_eq] at hlt
    have hsum_w : ∑ k : {k : Fin m // k ∈ A}, a₀ k.1 * w k = a₀ j * (-t) := by
      rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp [w]
      · intro k _ hk; simp [w, hk]
      · simp
    rw [hsum_w, mul_zero, add_zero] at hlt
    have hneg : 0 < -a₀ j := by linarith
    have ha0_ne : a₀ j ≠ 0 := h.ne
    have ht1 : u / (-a₀ j) + 1 ≤ t := le_max_right _ _
    have := mul_le_mul_of_nonneg_left ht1 hneg.le
    have hcancel : (-a₀ j) * (u / (-a₀ j) + 1) = u + (-a₀ j) := by field_simp; ring
    linarith
  -- Strict negativity of γ via Slater point on [s, T)
  have hγ_neg : γ < 0 := by
    refine lt_of_le_of_ne hγ_le ?_
    intro hγ0
    let d_sl : Fin m → ℝ := fun j => (1 + 1 / R) * ρ j
    have hd_sl_nn : ∀ j ∈ A, 0 ≤ d_sl j := fun j hj => by
      have := hρ j hj; positivity
    have hd_sl_sum : s + ∑ j ∈ A, d_sl j = T := by
      have : ∑ j ∈ A, d_sl j = (1 + 1 / R) * R := by
        simp only [d_sl, ← Finset.mul_sum, R]
      rw [this]
      have : (1 + 1 / R) * R = R + 1 := by field_simp
      linarith
    let x_sl := btSched s A d_sl
    let c_sl := ∑ j ∈ A, ∫ t in Ico s T, I.g j t * x_sl j t
    have hsl_in : (fun j : {j : Fin m // j ∈ A} => d_sl j.1, c_sl) ∈ E := by
      refine ⟨x_sl, btSched_measurable s A d_sl, btSched_nonneg s A d_sl,
        fun j hj t => btSched_eq_zero_of_notMem s A d_sl hj t, ?_,
        btSched_sum_le_one s A d_sl hd_sl_nn, ?_, le_rfl⟩
      · intro j t ht
        by_cases hlt : t < s
        · exact btSched_eq_zero_of_lt s A d_sl hd_sl_nn j hlt
        · have hge : T ≤ t := by
            by_contra hltT; exact ht ⟨not_lt.mp hlt, not_le.mp hltT⟩
          exact btSched_eq_zero_of_ge s A d_sl hd_sl_nn j (by linarith)
      · intro j
        exact (btSched_setIntegral s T A d_sl hd_sl_nn hd_sl_sum.le j.2).ge
    have hlt := (hfE _ (subset_closure hsl_in)).trans hfp₀
    rw [hf_eq, hf_eq, hγ0, zero_mul, zero_mul, add_zero, add_zero] at hlt
    have hsum_eq1 : (∑ j : {j : Fin m // j ∈ A}, a₀ j.1 * d_sl j.1) =
        (1 + 1 / R) * ∑ j ∈ A, a₀ j * ρ j := by
      have h1 : ∀ j : {j : Fin m // j ∈ A}, a₀ j.1 * d_sl j.1 = (1 + 1 / R) * (a₀ j.1 * ρ j.1) :=
        fun j => by simp only [d_sl]; ring
      simp_rw [h1, ← Finset.mul_sum]
      congr 1
      exact Finset.sum_attach A (fun j => a₀ j * ρ j)
    have hsum_eq2 : (∑ j : {j : Fin m // j ∈ A}, a₀ j.1 * p₀.1 j) = ∑ j ∈ A, a₀ j * ρ j :=
      Finset.sum_attach A (fun j => a₀ j * ρ j)
    rw [hsum_eq1, hsum_eq2] at hlt
    have hsum_nn : 0 ≤ ∑ j ∈ A, a₀ j * ρ j :=
      Finset.sum_nonneg fun j hj => mul_nonneg (ha₀_nn j hj) (hρ j hj).le
    have h1R : 0 < 1 / R := by positivity
    nlinarith
  -- 4. Rescale by -γ > 0
  have hnegγ : 0 < -γ := by linarith
  let ã : Fin m → ℝ := fun j => a₀ j / (-γ)
  have hã_nn : ∀ j ∈ A, 0 ≤ ã j := fun j hj => div_nonneg (ha₀_nn j hj) hnegγ.le
  have hE_ineq : ∀ p ∈ E,
      (∑ j : {j : Fin m // j ∈ A}, ã j.1 * p.1 j) - p.2 ≤
        (∑ j ∈ A, ã j * ρ j) - (V - ε) := by
    intro p hp
    have hlt := (hfE p (subset_closure hp)).trans hfp₀
    rw [hf_eq, hf_eq] at hlt
    have hdiv := div_le_div_of_nonneg_right hlt.le hnegγ.le
    have hγ_ne : γ ≠ 0 := hγ_neg.ne
    have hL : ((∑ j : {j : Fin m // j ∈ A}, a₀ j.1 * p.1 j) + γ * p.2) / (-γ) =
        (∑ j : {j : Fin m // j ∈ A}, ã j.1 * p.1 j) - p.2 := by
      rw [add_div, Finset.sum_div]
      have h1 : ∀ j : {j : Fin m // j ∈ A}, a₀ j.1 * p.1 j / (-γ) = ã j.1 * p.1 j :=
        fun j => by simp only [ã]; ring
      have h2 : γ * p.2 / (-γ) = -p.2 := by field_simp
      simp_rw [h1]; linarith
    have hR' : ((∑ j : {j : Fin m // j ∈ A}, a₀ j.1 * p₀.1 j) + γ * p₀.2) / (-γ) =
        (∑ j ∈ A, ã j * ρ j) - (V - ε) := by
      rw [add_div, Finset.sum_div]
      have h1 : ∀ j : {j : Fin m // j ∈ A}, a₀ j.1 * p₀.1 j / (-γ) = ã j.1 * ρ j.1 :=
        fun j => by simp only [ã, p₀]; ring
      have h2 : γ * p₀.2 / (-γ) = -(V - ε) := by simp only [p₀]; field_simp
      have h3 : (∑ j : {j : Fin m // j ∈ A}, ã j.1 * ρ j.1) = ∑ j ∈ A, ã j * ρ j :=
        Finset.sum_attach A (fun j => ã j * ρ j)
      simp_rw [h1]
      linarith
    linarith
  -- 5. Construct the pointwise argmax schedule on [s, T)
  let G : Fin m → ℝ → ℝ := fun j => (Ici s).indicator (I.g j)
  have hG_meas : ∀ j ∈ A, Measurable (G j) := fun j hj =>
    measurable_indicator_of_continuousOn measurableSet_Ici (g_continuousOn I hI s A hA hj)
  let B : ℝ → ℝ := fun t => max 0 (A.sup' hA_ne (fun j => ã j - G j t))
  have hB_meas : Measurable B :=
    measurable_const.max (measurable_sup' A hA_ne fun j hj => measurable_const.sub (hG_meas j hj))
  let S : Fin m → Set ℝ := fun j =>
    if j ∈ A then
      Ico s T ∩ {t | 0 < B t} ∩ {t | ã j - G j t = B t} ∩
        ⋂ i ∈ A.filter (· < j), {t | ã i - G i t < B t}
    else ∅
  have hS_meas : ∀ j, MeasurableSet (S j) := by
    intro j
    simp only [S]
    split_ifs with hj
    · refine ((measurableSet_Ico.inter (measurableSet_lt measurable_const hB_meas)).inter
        (measurableSet_eq_fun (measurable_const.sub (hG_meas j hj)) hB_meas)).inter ?_
      refine Finset.measurableSet_biInter _ fun i hi => ?_
      exact measurableSet_lt (measurable_const.sub (hG_meas i (Finset.mem_filter.mp hi).1)) hB_meas
    · exact MeasurableSet.empty
  let x_max : Fin m → ℝ → ℝ := fun j => (S j).indicator (fun _ => 1)
  have hxmax_meas : ∀ j, Measurable (x_max j) :=
    fun j => measurable_const.indicator (hS_meas j)
  have hxmax_nn : ∀ j t, 0 ≤ x_max j t :=
    fun j t => indicator_nonneg (fun _ _ => zero_le_one) t
  have hxmax_out : ∀ j, j ∉ A → ∀ t, x_max j t = 0 := by
    intro j hj t; simp [x_max, S, hj]
  have hxmax_supp : ∀ j t, t ∉ Ico s T → x_max j t = 0 := by
    intro j t ht
    apply indicator_of_notMem
    intro hmem
    simp only [S] at hmem
    split_ifs at hmem with hj
    · exact ht hmem.1.1.1
    · exact hmem
  have hxmax_sum : ∀ t, ∑ j, x_max j t ≤ 1 := by
    intro t
    by_cases hne : ∃ j, t ∈ S j
    · obtain ⟨j, hjS⟩ := hne
      have huniq : ∀ i, i ≠ j → x_max i t = 0 := by
        intro i hij
        apply indicator_of_notMem
        intro hiS
        have hiA : i ∈ A := by by_contra h; simp [S, h] at hiS
        have hjA : j ∈ A := by by_contra h; simp [S, h] at hjS
        simp only [S, hiA, hjA, ↓reduceIte, mem_inter_iff, mem_ofPred_eq, mem_iInter] at hiS hjS
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · have h1 := hjS.2 i (Finset.mem_filter.mpr ⟨hiA, hlt⟩)
          linarith [hiS.1.2]
        · have h1 := hiS.2 j (Finset.mem_filter.mpr ⟨hjA, hgt⟩)
          linarith [hjS.1.2]
      rw [Finset.sum_eq_single j (fun i _ hij => huniq i hij) (by simp)]
      simp [x_max, indicator_of_mem hjS]
    · push Not at hne
      have h0 : ∀ j, x_max j t = 0 := fun j => indicator_of_notMem (hne j) _
      simp [h0]
  have hxmax_point : ∀ t ∈ Ico s T, ∑ j ∈ A, (ã j - I.g j t) * x_max j t = B t := by
    intro t ht
    by_cases hB0 : B t = 0
    · have h0 : ∀ j ∈ A, x_max j t = 0 := by
        intro j hj
        apply indicator_of_notMem
        intro hmem
        simp only [S, hj, ↓reduceIte, mem_inter_iff, mem_ofPred_eq] at hmem
        linarith [hmem.1.1.2]
      rw [hB0, Finset.sum_eq_zero]
      intro j hj; simp [h0 j hj]
    · have hBpos : 0 < B t := lt_of_le_of_ne (le_max_left _ _) (Ne.symm hB0)
      have hB_eq_sup : B t = A.sup' hA_ne (fun j => ã j - G j t) := by
        simp only [B, max_eq_right_iff]
        by_contra hlt
        push Not at hlt
        have : B t = 0 := max_eq_left hlt.le
        exact hB0 this
      obtain ⟨j₀, hj₀A, hj₀_eq⟩ :=
        Finset.exists_mem_eq_sup' hA_ne (fun j => ã j - G j t)
      let F := A.filter (fun j => ã j - G j t = B t)
      have hF_ne : F.Nonempty := ⟨j₀, Finset.mem_filter.mpr ⟨hj₀A, by linarith⟩⟩
      let jstar := F.min' hF_ne
      have hjstar_mem : jstar ∈ F := Finset.min'_mem F hF_ne
      have hjstarA : jstar ∈ A := (Finset.mem_filter.mp hjstar_mem).1
      have hjstar_eq : ã jstar - G jstar t = B t := (Finset.mem_filter.mp hjstar_mem).2
      have hjstar_S : t ∈ S jstar := by
        simp only [S, hjstarA, ↓reduceIte, mem_inter_iff, mem_ofPred_eq, mem_iInter]
        refine ⟨⟨⟨ht, hBpos⟩, hjstar_eq⟩, fun i hi => ?_⟩
        have hiA := (Finset.mem_filter.mp hi).1
        have hilt := (Finset.mem_filter.mp hi).2
        have hle : ã i - G i t ≤ B t := by
          rw [hB_eq_sup]; exact Finset.le_sup' (fun j => ã j - G j t) hiA
        refine lt_of_le_of_ne hle ?_
        intro heq
        have hiF : i ∈ F := Finset.mem_filter.mpr ⟨hiA, heq⟩
        exact not_le.mpr hilt (Finset.min'_le F i hiF)
      have hother : ∀ j ∈ A, j ≠ jstar → x_max j t = 0 := by
        intro j hj hne
        apply indicator_of_notMem
        intro hjS
        simp only [S, hj, ↓reduceIte, mem_inter_iff, mem_ofPred_eq, mem_iInter] at hjS
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hjF : j ∈ F := Finset.mem_filter.mpr ⟨hj, hjS.1.2⟩
          exact not_le.mpr hlt (Finset.min'_le F j hjF)
        · have h1 := hjS.2 jstar (Finset.mem_filter.mpr ⟨hjstarA, hgt⟩)
          linarith
      rw [Finset.sum_eq_single jstar (fun j hj hne => by rw [hother j hj hne, mul_zero])
        (fun h => (h hjstarA).elim)]
      simp only [x_max, indicator_of_mem hjstar_S, mul_one]
      have hGeq : G jstar t = I.g jstar t := indicator_of_mem ht.1 (I.g jstar)
      rw [← hGeq, hjstar_eq]
  -- Plug x_max into hE_ineq
  let p_max : ({j : Fin m // j ∈ A} → ℝ) × ℝ :=
    (fun j => ∫ t in Ico s T, x_max j.1 t, ∑ j ∈ A, ∫ t in Ico s T, I.g j t * x_max j t)
  have hp_max_in : p_max ∈ E :=
    ⟨x_max, hxmax_meas, hxmax_nn, hxmax_out, hxmax_supp, hxmax_sum,
      fun _ => le_rfl, le_rfl⟩
  have hB_int_le : ∫ t in Ico s T, B t ≤ (∑ j ∈ A, ã j * ρ j) - (V - ε) := by
    have h_ineq := hE_ineq p_max hp_max_in
    have hsum_int : ∫ t in Ico s T, B t =
        (∑ j : {j : Fin m // j ∈ A}, ã j.1 * p_max.1 j) - p_max.2 := by
      have h1 : ∫ t in Ico s T, B t =
          ∫ t in Ico s T, ∑ j ∈ A, (ã j - I.g j t) * x_max j t :=
        setIntegral_congr_fun measurableSet_Ico (fun t ht => (hxmax_point t ht).symm)
      rw [h1, integral_finsetSum _ (fun j hj => by
        have hix := integrableOn_sched_Ico s T (hxmax_meas j) (hxmax_nn j)
          (hx_le_one x_max hxmax_nn hxmax_sum j)
        have hig := integrableOn_cost_Ico I hI s T A hA hsT hj (hxmax_meas j) (hxmax_nn j)
          (hx_le_one x_max hxmax_nn hxmax_sum j)
        have : (fun t => (ã j - I.g j t) * x_max j t) =
            fun t => ã j * x_max j t - I.g j t * x_max j t := by ext t; ring
        rw [this]; exact (hix.const_mul (ã j)).sub hig)]
      have h2 : ∀ j ∈ A, ∫ t in Ico s T, (ã j - I.g j t) * x_max j t =
          ã j * (∫ t in Ico s T, x_max j t) - ∫ t in Ico s T, I.g j t * x_max j t := by
        intro j hj
        have hix := integrableOn_sched_Ico s T (hxmax_meas j) (hxmax_nn j)
          (hx_le_one x_max hxmax_nn hxmax_sum j)
        have hig := integrableOn_cost_Ico I hI s T A hA hsT hj (hxmax_meas j) (hxmax_nn j)
          (hx_le_one x_max hxmax_nn hxmax_sum j)
        have : (fun t => (ã j - I.g j t) * x_max j t) =
            fun t => ã j * x_max j t - I.g j t * x_max j t := by ext t; ring
        rw [this, integral_sub (hix.const_mul (ã j)) hig, integral_const_mul]
      rw [Finset.sum_congr rfl h2, Finset.sum_sub_distrib]
      congr 1
      exact (Finset.sum_attach A (fun j => ã j * ∫ t in Ico s T, x_max j t)).symm
    linarith
  -- 6. Shift down by c = B T so β vanishes on [T, ∞)
  let c : ℝ := B T
  have hc_nn : 0 ≤ c := le_max_left _ _
  have hB_ge_c : ∀ t ∈ Ico s T, c ≤ B t := by
    intro t ht
    simp only [c, B, max_le_iff]
    refine ⟨le_max_left _ _, ?_⟩
    rw [Finset.sup'_le_iff]
    intro j hj
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (Finset.le_sup' (fun i => ã i - G i t) hj)
    have hGt : G j t = I.g j t := indicator_of_mem ht.1 (I.g j)
    have hGT : G j T = I.g j T := indicator_of_mem hsT (I.g j)
    rw [hGt, hGT]
    linarith [g_monoOn I hI s A hA hj ht.1 hsT ht.2.le]
  let a' : Fin m → ℝ := fun j => if j ∈ A then max (ã j - c) 0 else 0
  let β' : ℝ → ℝ := (Ico s T).indicator (fun t => B t - c)
  have hB_cont_Ici : ContinuousOn B (Ici s) := by
    have hcont : ContinuousOn (fun t => max 0 (A.sup' hA_ne (fun j => ã j - I.g j t))) (Ici s) :=
      continuousOn_max continuousOn_const (continuousOn_sup' A hA_ne fun j hj =>
        continuousOn_const.sub (g_continuousOn I hI s A hA hj))
    refine hcont.congr fun t ht => ?_
    simp only [B]
    congr 1
    refine Finset.sup'_congr hA_ne rfl fun j _ => ?_
    simp [G, indicator_of_mem ht]
  have hB_int_Ico : IntegrableOn B (Ico s T) :=
    ((hB_cont_Ici.mono Icc_subset_Ici_self).integrableOn_Icc).mono_set Ico_subset_Icc_self
  have hβ'_feas : IsOffDualFeas I.g s A a' β' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h1 : IntegrableOn (fun t => B t - c) (Ico s T) :=
        hB_int_Ico.sub (integrableOn_const (hs := measure_Ico_lt_top.ne))
      exact (integrable_indicator_iff measurableSet_Ico).mpr h1 |>.integrableOn
    · intro j hj; simp [a', hj]
    · refine Eventually.of_forall fun t _ => ?_
      by_cases ht : t ∈ Ico s T
      · simp only [β', indicator_of_mem ht]; linarith [hB_ge_c t ht]
      · simp only [β', indicator_of_notMem ht]; exact le_rfl
    · intro j hj
      refine Eventually.of_forall fun t hts => ?_
      have hgt_nn : 0 ≤ I.g j t := g_nonneg I hI s A hA hj hts
      simp only [a', hj, ↓reduceIte, max_le_iff]
      by_cases htT : t < T
      · have ht : t ∈ Ico s T := ⟨hts, htT⟩
        simp only [β', indicator_of_mem ht]
        have hGt : G j t = I.g j t := indicator_of_mem hts (I.g j)
        have hle : ã j - I.g j t ≤ B t := by
          rw [← hGt]
          exact le_trans (Finset.le_sup' (fun i => ã i - G i t) hj) (le_max_right _ _)
        exact ⟨by linarith, by linarith [hB_ge_c t ht]⟩
      · have ht : t ∉ Ico s T := fun h => htT h.2
        simp only [β', indicator_of_notMem ht, zero_add]
        have hTle : T ≤ t := not_lt.mp htT
        have hGT : G j T = I.g j T := indicator_of_mem hsT (I.g j)
        have hle1 : ã j - I.g j T ≤ c := by
          rw [← hGT]
          exact le_trans (Finset.le_sup' (fun i => ã i - G i T) hj) (le_max_right _ _)
        have hle2 : I.g j T ≤ I.g j t := g_monoOn I hI s A hA hj hsT hts hTle
        exact ⟨by linarith, hgt_nn⟩
  refine ⟨a', β', hβ'_feas, ?_⟩
  have hβ'_int : ∫ t in Ici s, β' t = (∫ t in Ico s T, B t) - c * (T - s) := by
    rw [setIntegral_indicator measurableSet_Ico, inter_eq_right.mpr Ico_subset_Ici_self,
      integral_sub hB_int_Ico (integrableOn_const (hs := measure_Ico_lt_top.ne)),
      setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ico,
      ENNReal.toReal_ofReal (by linarith), mul_comm]
  have ha'_sum : ∑ j ∈ A, (ã j - c) * ρ j ≤ ∑ j ∈ A, a' j * ρ j := by
    refine Finset.sum_le_sum fun j hj => ?_
    simp only [a', hj, ↓reduceIte]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hρ j hj).le
  have hsum_expand : ∑ j ∈ A, (ã j - c) * ρ j = (∑ j ∈ A, ã j * ρ j) - c * R := by
    have : ∀ j ∈ A, (ã j - c) * ρ j = ã j * ρ j - c * ρ j := fun j _ => by ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold offDualObj
  rw [hβ'_int]
  have hTs : T - s = R + 1 := by simp only [T]; ring
  rw [hTs]
  linarith

/-! ### Canonical minimal `β` and compactness / Fatou argument -/

private noncomputable def betaOf {m : ℕ} (G : Fin m → ℝ → ℝ) (s : ℝ) (A : Finset (Fin m))
    (hA_ne : A.Nonempty) (a : Fin m → ℝ) (t : ℝ) : ℝ :=
  if s ≤ t then max 0 (A.sup' hA_ne (fun j => a j - G j t)) else 0

private lemma betaOf_nonneg {m : ℕ} (G : Fin m → ℝ → ℝ) (s : ℝ) (A : Finset (Fin m))
    (hA_ne : A.Nonempty) (a : Fin m → ℝ) (t : ℝ) : 0 ≤ betaOf G s A hA_ne a t := by
  unfold betaOf
  split_ifs
  · exact le_max_left _ _
  · rfl

private lemma betaOf_continuousOn {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (hA_ne : A.Nonempty) (hA : ∀ j ∈ A, I.r j ≤ s) (a : Fin m → ℝ) :
    ContinuousOn (betaOf I.g s A hA_ne a) (Ici s) := by
  have hcont : ContinuousOn (fun t => max 0 (A.sup' hA_ne (fun j => a j - I.g j t))) (Ici s) :=
    continuousOn_max continuousOn_const (continuousOn_sup' A hA_ne fun j hj =>
      continuousOn_const.sub (g_continuousOn I hI s A hA hj))
  exact hcont.congr fun t ht => by simp [betaOf, mem_Ici.mp ht]

private lemma betaOf_continuous_a {m : ℕ} (G : Fin m → ℝ → ℝ) (s : ℝ) (A : Finset (Fin m))
    (hA_ne : A.Nonempty) (t : ℝ) : Continuous (fun a : Fin m → ℝ => betaOf G s A hA_ne a t) := by
  unfold betaOf
  split_ifs
  · refine continuous_const.max ?_
    induction hA_ne using Finset.Nonempty.cons_induction with
    | singleton j =>
      simp only [Finset.sup'_singleton]
      exact (continuous_apply j).sub continuous_const
    | cons j B hj hB ih =>
      have heq : (fun a : Fin m → ℝ =>
          (Finset.cons j B hj).sup' (Finset.cons_nonempty hj) (fun k => a k - G k t)) =
          fun a => max (a j - G j t) (B.sup' hB (fun k => a k - G k t)) := by
        ext a; rw [Finset.sup'_cons]
      rw [heq]
      exact ((continuous_apply j).sub continuous_const).max ih
  · exact continuous_const

private lemma betaOf_feas_and_le {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (hA_ne : A.Nonempty) (hA : ∀ j ∈ A, I.r j ≤ s)
    {a : Fin m → ℝ} {β : ℝ → ℝ} (hfeas : IsOffDualFeas I.g s A a β) :
    IsOffDualFeas I.g s A a (betaOf I.g s A hA_ne a) ∧
      ∫ t in Ici s, betaOf I.g s A hA_ne a t ≤ ∫ t in Ici s, β t := by
  set μ : Measure ℝ := volume.restrict (Ici s)
  have hae_le : ∀ᵐ t ∂μ, betaOf I.g s A hA_ne a t ≤ β t := by
    have hnn : ∀ᵐ t ∂μ, 0 ≤ β t := (ae_restrict_iff' measurableSet_Ici).mpr hfeas.2.2.1
    have hmem : ∀ᵐ t ∂μ, s ≤ t := ae_restrict_mem measurableSet_Ici
    have hball : ∀ᵐ t ∂μ, ∀ j ∈ A, a j ≤ β t + I.g j t :=
      (ae_ball_iff (Finset.countable_toSet A)).mpr fun j hj =>
        (ae_restrict_iff' measurableSet_Ici).mpr (hfeas.2.2.2 j hj)
    filter_upwards [hnn, hmem, hball] with t htβ hts htc
    simp only [betaOf, hts, ↓reduceIte, max_le_iff]
    refine ⟨htβ, ?_⟩
    rw [Finset.sup'_le_iff]
    intro j hj
    linarith [htc j hj]
  have hmeas : AEStronglyMeasurable (betaOf I.g s A hA_ne a) μ :=
    (betaOf_continuousOn I hI s A hA_ne hA a).aestronglyMeasurable measurableSet_Ici
  have hint : IntegrableOn (betaOf I.g s A hA_ne a) (Ici s) := by
    refine hfeas.1.mono' hmeas ?_
    filter_upwards [hae_le] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (betaOf_nonneg I.g s A hA_ne a t)]
    exact ht
  refine ⟨⟨hint, hfeas.2.1, Eventually.of_forall (fun t _ => betaOf_nonneg I.g s A hA_ne a t),
    fun j hj => Eventually.of_forall fun t hts => ?_⟩,
    integral_mono_ae hint hfeas.1 hae_le⟩
  simp only [betaOf, hts, ↓reduceIte]
  have hle : a j - I.g j t ≤ max 0 (A.sup' hA_ne (fun i => a i - I.g i t)) :=
    le_trans (Finset.le_sup' (fun i => a i - I.g i t) hj) (le_max_right _ _)
  linarith

private lemma dual_a_upper_bound {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (hA_ne : A.Nonempty) (ρ : Fin m → ℝ) (hA : ∀ j ∈ A, I.r j ≤ s)
    (hρ : ∀ j ∈ A, 0 < ρ j) {a : Fin m → ℝ} {β : ℝ → ℝ} (hfeas : IsOffDualFeas I.g s A a β)
    (hobj : -1 ≤ offDualObj s A ρ a β) :
    ∀ j ∈ A, a j ≤ 2 * (A.sup' hA_ne (fun i => I.g i (s + 2 * ∑ k ∈ A, ρ k))) +
      1 / (∑ k ∈ A, ρ k) := by
  set R : ℝ := ∑ k ∈ A, ρ k
  have hR : 0 < R := Finset.sum_pos hρ hA_ne
  set U : ℝ := s + 2 * R
  have hsU : s ≤ U := by linarith
  set C : ℝ := A.sup' hA_ne (fun i => I.g i U)
  obtain ⟨jstar, hjstarA, hjstar_max⟩ := Finset.exists_max_image A a hA_ne
  have hsum_le : ∑ k ∈ A, a k * ρ k ≤ a jstar * R := by
    calc ∑ k ∈ A, a k * ρ k ≤ ∑ k ∈ A, a jstar * ρ k :=
          Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hjstar_max k hk) (hρ k hk).le
      _ = a jstar * R := by rw [← Finset.mul_sum]
  have hβ_ge : 2 * R * (a jstar - C) ≤ ∫ t in Ici s, β t := by
    have hae : ∀ᵐ t ∂(volume.restrict (Icc s U)), a jstar - C ≤ β t := by
      have h1 : ∀ᵐ t ∂(volume.restrict (Ici s)), a jstar ≤ β t + I.g jstar t :=
        (ae_restrict_iff' measurableSet_Ici).mpr (hfeas.2.2.2 jstar hjstarA)
      have h2 : ∀ᵐ t ∂(volume.restrict (Icc s U)), a jstar ≤ β t + I.g jstar t :=
        ae_restrict_of_ae_restrict_of_subset Icc_subset_Ici_self h1
      filter_upwards [h2, ae_restrict_mem measurableSet_Icc] with t htc ht
      have hg1 : I.g jstar t ≤ I.g jstar U := g_monoOn I hI s A hA hjstarA ht.1 hsU ht.2
      have hg2 : I.g jstar U ≤ C := Finset.le_sup' (fun i => I.g i U) hjstarA
      linarith
    have hIcc : 2 * R * (a jstar - C) ≤ ∫ t in Icc s U, β t := by
      calc 2 * R * (a jstar - C)
          = ∫ _t in Icc s U, (a jstar - C) := by
            rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc,
              ENNReal.toReal_ofReal (by linarith)]
            ring
        _ ≤ ∫ t in Icc s U, β t :=
            integral_mono_ae (integrableOn_const (hs := measure_Icc_lt_top.ne))
              (hfeas.1.mono_set Icc_subset_Ici_self) hae
    exact hIcc.trans (setIntegral_mono_set hfeas.1
      ((ae_restrict_iff' measurableSet_Ici).mpr hfeas.2.2.1)
      (Eventually.of_forall Icc_subset_Ici_self))
  unfold offDualObj at hobj
  have hbound : R * a jstar ≤ 2 * R * C + 1 := by linarith
  intro j hj
  have h1 : R * a j ≤ 2 * R * C + 1 := le_trans (mul_le_mul_of_nonneg_left (hjstar_max j hj) hR.le) hbound
  have h2 : (R * a j) / R ≤ (2 * R * C + 1) / R := div_le_div_of_nonneg_right h1 hR.le
  have hL : R * a j / R = a j := by field_simp
  have hR' : (2 * R * C + 1) / R = 2 * C + 1 / R := by field_simp
  linarith

private lemma fatou_betaOf {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (hA_ne : A.Nonempty) (hA : ∀ j ∈ A, I.r j ≤ s)
    {a_seq : ℕ → Fin m → ℝ} {a : Fin m → ℝ} (ha : Tendsto a_seq atTop (𝓝 a))
    {C_seq : ℕ → ℝ} {L : ℝ} (hC : Tendsto C_seq atTop (𝓝 L)) (hL : 0 ≤ L)
    (hint : ∀ k, IntegrableOn (betaOf I.g s A hA_ne (a_seq k)) (Ici s))
    (hle : ∀ k, ∫ t in Ici s, betaOf I.g s A hA_ne (a_seq k) t ≤ C_seq k) :
    IntegrableOn (betaOf I.g s A hA_ne a) (Ici s) ∧
      ∫ t in Ici s, betaOf I.g s A hA_ne a t ≤ L := by
  set μ : Measure ℝ := volume.restrict (Ici s)
  have hmeas_k : ∀ k, AEMeasurable (fun t => ENNReal.ofReal (betaOf I.g s A hA_ne (a_seq k) t)) μ :=
    fun k => (hint k).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hpt : ∀ t, liminf (fun k => ENNReal.ofReal (betaOf I.g s A hA_ne (a_seq k) t)) atTop =
      ENNReal.ofReal (betaOf I.g s A hA_ne a t) := by
    intro t
    have hcont : ContinuousAt (fun b => ENNReal.ofReal (betaOf I.g s A hA_ne b t)) a :=
      (ENNReal.continuous_ofReal.comp (betaOf_continuous_a I.g s A hA_ne t)).continuousAt
    exact (hcont.tendsto.comp ha).liminf_eq
  have hlint_le : ∫⁻ t, ENNReal.ofReal (betaOf I.g s A hA_ne a t) ∂μ ≤ ENNReal.ofReal L := by
    calc
      ∫⁻ t, ENNReal.ofReal (betaOf I.g s A hA_ne a t) ∂μ
          = ∫⁻ t, liminf (fun k => ENNReal.ofReal (betaOf I.g s A hA_ne (a_seq k) t)) atTop ∂μ :=
            lintegral_congr fun t => (hpt t).symm
      _ ≤ liminf (fun k => ∫⁻ t, ENNReal.ofReal (betaOf I.g s A hA_ne (a_seq k) t) ∂μ) atTop :=
            lintegral_liminf_le' hmeas_k
      _ ≤ liminf (fun k => ENNReal.ofReal (C_seq k)) atTop := by
            refine Filter.liminf_le_liminf (Eventually.of_forall fun k => ?_)
            rw [← ofReal_integral_eq_lintegral_ofReal (hint k)
              (Eventually.of_forall (betaOf_nonneg I.g s A hA_ne (a_seq k)))]
            exact ENNReal.ofReal_le_ofReal (hle k)
      _ = ENNReal.ofReal L := (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hC).liminf_eq
  have hmeas_a : AEStronglyMeasurable (betaOf I.g s A hA_ne a) μ :=
    (betaOf_continuousOn I hI s A hA_ne hA a).aestronglyMeasurable measurableSet_Ici
  have hfin : HasFiniteIntegral (betaOf I.g s A hA_ne a) μ := by
    unfold HasFiniteIntegral
    have heq : (fun t => ‖betaOf I.g s A hA_ne a t‖ₑ) =
        fun t => ENNReal.ofReal (betaOf I.g s A hA_ne a t) := by
      ext t
      exact Real.enorm_eq_ofReal (betaOf_nonneg I.g s A hA_ne a t)
    rw [heq]
    exact lt_of_le_of_lt hlint_le ENNReal.ofReal_lt_top
  have hint_a : IntegrableOn (betaOf I.g s A hA_ne a) (Ici s) := ⟨hmeas_a, hfin⟩
  refine ⟨hint_a, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint_a
    (Eventually.of_forall (betaOf_nonneg I.g s A hA_ne a))] at hlint_le
  exact (ENNReal.ofReal_le_ofReal_iff hL).mp hlint_le

/-! ### Main theorem -/

theorem solution {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (ρ : Fin m → ℝ) (hA : ∀ j ∈ A, I.r j ≤ s) (hρ : ∀ j ∈ A, 0 < ρ j) :
    rnf I.g s A ρ ≠ ⊤ ∧
      ∃ (a : Fin m → ℝ) (β : ℝ → ℝ), IsOffMaxOptDual I.g s A ρ a β ∧
        offDualObj s A ρ a β = (rnf I.g s A ρ).toReal := by
  refine ⟨rnf_ne_top I hI s A ρ hA hρ, ?_⟩
  by_cases hA_ne : A.Nonempty
  · set V : ℝ := (rnf I.g s A ρ).toReal
    have hV_nn : 0 ≤ V := ENNReal.toReal_nonneg
    set R : ℝ := ∑ k ∈ A, ρ k
    have hR : 0 < R := Finset.sum_pos hρ hA_ne
    set B_hi : ℝ := 2 * (A.sup' hA_ne (fun i => I.g i (s + 2 * R))) + 1 / R
    let Box : Set (Fin m → ℝ) :=
      Set.pi Set.univ (fun j => if j ∈ A then Icc 0 B_hi else {0})
    have hBox_compact : IsCompact Box := by
      refine isCompact_univ_pi fun j => ?_
      split_ifs
      · exact isCompact_Icc
      · exact isCompact_singleton
    let zeroOut : (Fin m → ℝ) → (Fin m → ℝ) := fun a j => if j ∈ A then a j else 0
    have hzeroOut_beta : ∀ a, betaOf I.g s A hA_ne (zeroOut a) = betaOf I.g s A hA_ne a := by
      intro a; ext t; unfold betaOf
      split_ifs
      · congr 1; refine Finset.sup'_congr hA_ne rfl fun j hj => by simp [zeroOut, hj]
      · rfl
    have hzeroOut_obj : ∀ a β, offDualObj s A ρ (zeroOut a) β = offDualObj s A ρ a β := by
      intro a β; unfold offDualObj
      congr 1; refine Finset.sum_congr rfl fun j hj => by simp [zeroOut, hj]
    have hzeroOut_feas : ∀ a β, IsOffDualFeas I.g s A a β →
        IsOffDualFeas I.g s A (zeroOut a) β := by
      intro a β hfeas
      refine ⟨hfeas.1, fun j hj => by simpa [zeroOut, hj] using hfeas.2.1 j hj, hfeas.2.2.1,
        fun j hj => by simpa [zeroOut, hj] using hfeas.2.2.2 j hj⟩
    let O : Set (Fin m → ℝ) :=
      { a ∈ Box | IntegrableOn (betaOf I.g s A hA_ne a) (Ici s) ∧
        offDualObj s A ρ a (betaOf I.g s A hA_ne a) = V }
    have hO_feas : ∀ a ∈ O, IsOffDualFeas I.g s A a (betaOf I.g s A hA_ne a) := by
      intro a ⟨haBox, hint, _⟩
      refine ⟨hint, fun j hj => ?_,
        Eventually.of_forall (fun t _ => betaOf_nonneg I.g s A hA_ne a t),
        fun j hj => Eventually.of_forall fun t hts => ?_⟩
      · have h := haBox j (mem_univ j)
        simp only [hj, ↓reduceIte, mem_Icc] at h
        exact h.1
      · simp only [betaOf, hts, ↓reduceIte]
        have hle : a j - I.g j t ≤ max 0 (A.sup' hA_ne (fun i => a i - I.g i t)) :=
          le_trans (Finset.le_sup' (fun i => a i - I.g i t) hj) (le_max_right _ _)
        linarith
    -- 1. O is nonempty (from near-optimal duals + compactness + Fatou)
    have hO_ne : O.Nonempty := by
      have hex : ∀ k : ℕ, ∃ a ∈ Box, IntegrableOn (betaOf I.g s A hA_ne a) (Ici s) ∧
          V - 1 / ((k : ℝ) + 1) ≤ offDualObj s A ρ a (betaOf I.g s A hA_ne a) := by
        intro k
        have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        obtain ⟨a, β, hfeas, hobj⟩ := exists_near_opt_dual I hI s A hA_ne ρ hA hρ hε
        obtain ⟨hfeas', hβ_le⟩ := betaOf_feas_and_le I hI s A hA_ne hA hfeas
        have hobj' : V - 1 / ((k : ℝ) + 1) ≤ offDualObj s A ρ a (betaOf I.g s A hA_ne a) := by
          unfold offDualObj at hobj ⊢; linarith
        have hobj_ge : -1 ≤ offDualObj s A ρ a (betaOf I.g s A hA_ne a) := by
          have h1 : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          linarith
        have hbd := dual_a_upper_bound I hI s A hA_ne ρ hA hρ hfeas' hobj_ge
        refine ⟨zeroOut a, ?_, ?_, ?_⟩
        · intro j _
          by_cases hj : j ∈ A
          · simp only [hj, ↓reduceIte, mem_Icc, zeroOut]
            exact ⟨hfeas'.2.1 j hj, hbd j hj⟩
          · simp [hj, zeroOut]
        · rw [hzeroOut_beta]; exact hfeas'.1
        · rw [hzeroOut_beta, hzeroOut_obj]; exact hobj'
      choose a_seq ha_box ha_int ha_obj using hex
      obtain ⟨a_lim, ha_lim_box, φ, hφ_mono, hφ_tendsto⟩ :=
        hBox_compact.tendsto_subseq ha_box
      let C_seq : ℕ → ℝ := fun k =>
        (∑ j ∈ A, a_seq (φ k) j * ρ j) - V + 1 / ((φ k : ℝ) + 1)
      let L : ℝ := (∑ j ∈ A, a_lim j * ρ j) - V
      have h_inv_tendsto : Tendsto (fun k : ℕ => (1 : ℝ) / ((φ k : ℝ) + 1)) atTop (𝓝 0) := by
        have hnat : Tendsto (fun k : ℕ => (φ k : ℝ) + 1) atTop atTop :=
          (tendsto_natCast_atTop_atTop.comp hφ_mono.tendsto_atTop).atTop_add tendsto_const_nhds
        exact tendsto_const_nhds.div_atTop hnat
      have h_sum_tendsto : Tendsto (fun k => ∑ j ∈ A, a_seq (φ k) j * ρ j) atTop
          (𝓝 (∑ j ∈ A, a_lim j * ρ j)) :=
        tendsto_finsetSum A fun j _ =>
          ((continuous_apply j).continuousAt.tendsto.comp hφ_tendsto).mul tendsto_const_nhds
      have hC_tendsto : Tendsto C_seq atTop (𝓝 L) := by
        have := (h_sum_tendsto.sub (tendsto_const_nhds (x := V))).add h_inv_tendsto
        simpa [C_seq, L] using this
      have hC_ge : ∀ k, ∫ t in Ici s, betaOf I.g s A hA_ne (a_seq (φ k)) t ≤ C_seq k := by
        intro k
        have h := ha_obj (φ k)
        unfold offDualObj at h
        simp only [C_seq]
        linarith
      have hL_nn : 0 ≤ L := by
        have h0 : ∀ k, 0 ≤ C_seq k := fun k =>
          le_trans (setIntegral_nonneg measurableSet_Ici fun t _ =>
            betaOf_nonneg I.g s A hA_ne (a_seq (φ k)) t) (hC_ge k)
        exact ge_of_tendsto hC_tendsto (Eventually.of_forall h0)
      obtain ⟨hint_lim, hle_lim⟩ := fatou_betaOf I hI s A hA_ne hA hφ_tendsto hC_tendsto hL_nn
        (fun k => ha_int (φ k)) hC_ge
      have hfeas_lim : IsOffDualFeas I.g s A a_lim (betaOf I.g s A hA_ne a_lim) := by
        refine ⟨hint_lim, fun j hj => ?_,
          Eventually.of_forall (fun t _ => betaOf_nonneg I.g s A hA_ne a_lim t),
          fun j hj => Eventually.of_forall fun t hts => ?_⟩
        · have h := ha_lim_box j (mem_univ j)
          simp only [hj, ↓reduceIte, mem_Icc] at h
          exact h.1
        · simp only [betaOf, hts, ↓reduceIte]
          have hle : a_lim j - I.g j t ≤ max 0 (A.sup' hA_ne (fun i => a_lim i - I.g i t)) :=
            le_trans (Finset.le_sup' (fun i => a_lim i - I.g i t) hj) (le_max_right _ _)
          linarith
      have hweak := off_weak_duality I hI s A ρ hA hρ hfeas_lim
      have heq_V : offDualObj s A ρ a_lim (betaOf I.g s A hA_ne a_lim) = V := by
        unfold offDualObj at hweak ⊢
        simp only [L] at hle_lim
        linarith
      exact ⟨a_lim, ha_lim_box, hint_lim, heq_V⟩
    -- 2. O is closed (hence compact) by Fatou
    have hO_closed : IsClosed O := by
      refine IsSeqClosed.isClosed ?_
      intro a_seq a ha_mem ha_tendsto
      have ha_box : a ∈ Box := hBox_compact.isClosed.mem_of_tendsto ha_tendsto
        (Eventually.of_forall fun k => (ha_mem k).1)
      let C_seq : ℕ → ℝ := fun k => (∑ j ∈ A, a_seq k j * ρ j) - V
      let L : ℝ := (∑ j ∈ A, a j * ρ j) - V
      have hC_tendsto : Tendsto C_seq atTop (𝓝 L) :=
        (tendsto_finsetSum A fun j _ =>
          ((continuous_apply j).continuousAt.tendsto.comp ha_tendsto).mul
            tendsto_const_nhds).sub tendsto_const_nhds
      have hC_eq : ∀ k, ∫ t in Ici s, betaOf I.g s A hA_ne (a_seq k) t ≤ C_seq k := by
        intro k
        have h := (ha_mem k).2.2
        unfold offDualObj at h
        simp only [C_seq]
        linarith
      have hL_nn : 0 ≤ L := by
        have h0 : ∀ k, 0 ≤ C_seq k := fun k =>
          le_trans (setIntegral_nonneg measurableSet_Ici fun t _ =>
            betaOf_nonneg I.g s A hA_ne (a_seq k) t) (hC_eq k)
        exact ge_of_tendsto hC_tendsto (Eventually.of_forall h0)
      obtain ⟨hint_a, hle_a⟩ := fatou_betaOf I hI s A hA_ne hA ha_tendsto hC_tendsto hL_nn
        (fun k => (ha_mem k).2.1) hC_eq
      have hfeas_a : IsOffDualFeas I.g s A a (betaOf I.g s A hA_ne a) := by
        refine ⟨hint_a, fun j hj => ?_,
          Eventually.of_forall (fun t _ => betaOf_nonneg I.g s A hA_ne a t),
          fun j hj => Eventually.of_forall fun t hts => ?_⟩
        · have h := ha_box j (mem_univ j)
          simp only [hj, ↓reduceIte, mem_Icc] at h
          exact h.1
        · simp only [betaOf, hts, ↓reduceIte]
          have hle : a j - I.g j t ≤ max 0 (A.sup' hA_ne (fun i => a i - I.g i t)) :=
            le_trans (Finset.le_sup' (fun i => a i - I.g i t) hj) (le_max_right _ _)
          linarith
      have hweak := off_weak_duality I hI s A ρ hA hρ hfeas_a
      have heq_V : offDualObj s A ρ a (betaOf I.g s A hA_ne a) = V := by
        unfold offDualObj at hweak ⊢
        simp only [L] at hle_a
        linarith
      exact ⟨ha_box, hint_a, heq_V⟩
    have hO_compact : IsCompact O := hBox_compact.of_isClosed_subset hO_closed (fun _ h => h.1)
    -- 3. Maximize ∑_{j ∈ A} a j * ρ j over compact O
    have hcont_lin : ContinuousOn (fun a : Fin m → ℝ => ∑ j ∈ A, a j * ρ j) O :=
      (continuous_finsetSum A fun j _ => (continuous_apply j).mul continuous_const).continuousOn
    obtain ⟨a_max, ha_max_O, ha_max_isMax⟩ := hO_compact.exists_isMaxOn hO_ne hcont_lin
    refine ⟨a_max, betaOf I.g s A hA_ne a_max, ⟨⟨hO_feas a_max ha_max_O, ?_⟩, ?_⟩, ha_max_O.2.2⟩
    · intro a' β' hfeas'
      rw [ha_max_O.2.2]
      exact off_weak_duality I hI s A ρ hA hρ hfeas'
    · intro a' β' hopt'
      have hobj'_eq : offDualObj s A ρ a' β' = V := by
        apply le_antisymm (off_weak_duality I hI s A ρ hA hρ hopt'.1)
        change V ≤ offDualObj s A ρ a' β'
        rw [← ha_max_O.2.2]
        exact hopt'.2 a_max (betaOf I.g s A hA_ne a_max) (hO_feas a_max ha_max_O)
      obtain ⟨hfeas'', hβ_le⟩ := betaOf_feas_and_le I hI s A hA_ne hA hopt'.1
      have hobj''_eq : offDualObj s A ρ a' (betaOf I.g s A hA_ne a') = V := by
        apply le_antisymm (off_weak_duality I hI s A ρ hA hρ hfeas'')
        unfold offDualObj at hobj'_eq ⊢
        linarith
      have hbd := dual_a_upper_bound I hI s A hA_ne ρ hA hρ hfeas'' (by linarith)
      have ha''_O : zeroOut a' ∈ O := by
        refine ⟨?_, ?_, ?_⟩
        · intro j _
          by_cases hj : j ∈ A
          · simp only [hj, ↓reduceIte, mem_Icc, zeroOut]
            exact ⟨hfeas''.2.1 j hj, hbd j hj⟩
          · simp [hj, zeroOut]
        · rw [hzeroOut_beta]; exact hfeas''.1
        · rw [hzeroOut_beta, hzeroOut_obj]; exact hobj''_eq
      have hsum_le : ∑ j ∈ A, zeroOut a' j * ρ j ≤ ∑ j ∈ A, a_max j * ρ j :=
        ha_max_isMax ha''_O
      have hsum_eq : ∑ j ∈ A, zeroOut a' j * ρ j = ∑ j ∈ A, a' j * ρ j :=
        Finset.sum_congr rfl fun j hj => by simp [zeroOut, hj]
      have hmax_V := ha_max_O.2.2
      unfold offDualObj at hobj'_eq hmax_V
      linarith
  · -- Empty case: A = ∅
    rw [Finset.not_nonempty_iff_eq_empty] at hA_ne
    subst hA_ne
    have hrnf0 : rnf I.g s ∅ ρ = 0 := by
      apply le_antisymm _ zero_le
      have hx0 : IsOffFracSched s ∅ ρ 0 :=
        ⟨fun _ => measurable_const, fun _ _ => le_rfl, fun _ _ _ => rfl,
          fun _ _ _ => rfl, fun _ => by simp, fun _ hj => (Finset.notMem_empty _ hj).elim⟩
      calc rnf I.g s ∅ ρ ≤ offCost I.g 0 := sInf_le ⟨0, hx0, rfl⟩
        _ = 0 := by simp [offCost]
    have hfeas0 : IsOffDualFeas I.g s ∅ 0 0 :=
      ⟨integrableOn_zero, fun _ hj => (Finset.notMem_empty _ hj).elim,
        Eventually.of_forall (fun _ _ => le_rfl), fun _ hj => (Finset.notMem_empty _ hj).elim⟩
    have hopt0 : IsOffOptDual I.g s ∅ ρ 0 0 := by
      refine ⟨hfeas0, fun a' β' hfeas' => ?_⟩
      have hnn : 0 ≤ ∫ t in Ici s, β' t :=
        setIntegral_nonneg_ae measurableSet_Ici hfeas'.2.2.1
      simp only [offDualObj, Finset.sum_empty, zero_sub, Pi.zero_apply, integral_zero]
      linarith
    refine ⟨0, 0, ⟨hopt0, fun a' β' hopt' => ?_⟩, ?_⟩
    · have hle := hopt'.2 0 0 hfeas0
      simp only [offDualObj, Finset.sum_empty, zero_sub, Pi.zero_apply, integral_zero] at hle ⊢
      linarith
    · simp [offDualObj, hrnf0]
