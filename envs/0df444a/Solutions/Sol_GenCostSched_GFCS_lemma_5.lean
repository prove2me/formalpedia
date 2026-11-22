-- Prove2me | solution 1 for GenCostSched.GFCS.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:08:16.043599+00:00
-- url     : https://prove2.me/submissions/5667b46a-3169-4899-a834-91daf270f148

import Mathlib
import Definitions.Def_GenCostSched_GFCS_Model

open MeasureTheory Set GenCostSched.GFCS
open scoped ENNReal

/-! ### Section 1: Basic continuity, integrability, and `canonBeta` helpers -/

private lemma jobStanding_continuousOn {n : ℕ} {I : Instance n} {j : Fin n}
    (hI : I.JobStanding j) : ContinuousOn (I.g j) (Ici (I.r j)) :=
  fun t ht => (hI.2.2.2.2.2 t ht).continuousWithinAt

private lemma continuousOn_Ici_eq_of_ae_eq {s : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Ici s)) (hg : ContinuousOn g (Ici s))
    (hfg : f =ᵐ[volume.restrict (Ici s)] g) : ∀ t ∈ Ici s, f t = g t := by
  intro t₀ ht₀
  by_contra hne
  have hd : 0 < |f t₀ - g t₀| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hsub : ContinuousOn (fun t => f t - g t) (Ici s) := hf.sub hg
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousOn_iff.mp hsub t₀ ht₀ (|f t₀ - g t₀| / 2) (half_pos hd)
  have hsub_set : Ico t₀ (t₀ + δ) ⊆ {t ∈ Ici s | f t ≠ g t} := by
    intro t ht
    have hts : t ∈ Ici s := le_trans ht₀ ht.1
    refine ⟨hts, fun heq => ?_⟩
    have hdist : dist t t₀ < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
      linarith [ht.2]
    have hlt := hball t hts hdist
    rw [heq, sub_self, Real.dist_eq, zero_sub, abs_neg] at hlt
    linarith
  have hvol_pos : (0 : ℝ≥0∞) < volume (Ico t₀ (t₀ + δ)) := by
    rw [Real.volume_Ico]
    simp [hδ]
  have hvol_zero : volume {t ∈ Ici s | f t ≠ g t} = 0 := by
    have h1 : volume.restrict (Ici s) {t | f t ≠ g t} = 0 := ae_iff.mp hfg
    rw [Measure.restrict_apply' measurableSet_Ici] at h1
    have hset : {t ∈ Ici s | f t ≠ g t} = {t | f t ≠ g t} ∩ Ici s := by
      ext t; simp [and_comm]
    rw [hset]
    exact h1
  have hle : volume (Ico t₀ (t₀ + δ)) ≤ volume {t ∈ Ici s | f t ≠ g t} :=
    measure_mono hsub_set
  rw [hvol_zero] at hle
  exact not_lt_of_ge hle hvol_pos

private lemma const_eq_zero_of_integrableOn_Ici {s c : ℝ}
    (hc : IntegrableOn (fun _ : ℝ => c) (Ici s)) : c = 0 := by
  rcases (integrableOn_const_iff).mp hc with h0 | hfin
  · simpa using h0
  · rw [Real.volume_Ici] at hfin
    exact False.elim (lt_irrefl _ hfin)

private lemma continuousOn_Ici_eq_zero_of_nonneg_of_integral_Ico_le_zero
    {s T₀ T : ℝ} {f : ℝ → ℝ} (hs : s ≤ T₀) (hT : T₀ < T)
    (hf : ContinuousOn f (Ici s)) (hnn : ∀ t ∈ Ici s, 0 ≤ f t)
    (hint : ∫ t in Ico T₀ T, f t ≤ 0) : f T₀ = 0 := by
  by_contra hne
  have hpos : 0 < f T₀ := lt_of_le_of_ne (hnn T₀ hs) (Ne.symm hne)
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousOn_iff.mp hf T₀ hs (f T₀ / 2) (half_pos hpos)
  set δ' : ℝ := min (δ / 2) (T - T₀)
  have hδ' : 0 < δ' := lt_min (half_pos hδ) (sub_pos.mpr hT)
  have hsub : Ico T₀ (T₀ + δ') ⊆ Ico T₀ T :=
    Ico_subset_Ico_right (by linarith [min_le_right (δ / 2) (T - T₀)])
  have hf_int_big : IntegrableOn f (Ico T₀ T) :=
    (hf.mono (fun t ht => le_trans hs ht.1)).integrableOn_Icc.mono_set Ico_subset_Icc_self
  have hf_int_small : IntegrableOn f (Ico T₀ (T₀ + δ')) := hf_int_big.mono_set hsub
  have hge : ∀ t ∈ Ico T₀ (T₀ + δ'), f T₀ / 2 ≤ f t := by
    intro t ht
    have hts : t ∈ Ici s := le_trans hs ht.1
    have hdist : dist t T₀ < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
      have hle : δ' ≤ δ / 2 := min_le_left _ _
      linarith [ht.2]
    have hlt := hball t hts hdist
    rw [Real.dist_eq] at hlt
    linarith [(abs_lt.mp hlt).1]
  have h1 : ∫ t in Ico T₀ (T₀ + δ'), (f T₀ / 2) ≤ ∫ t in Ico T₀ (T₀ + δ'), f t := by
    apply setIntegral_mono_on (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))
      hf_int_small measurableSet_Ico
    exact hge
  have h2 : ∫ t in Ico T₀ (T₀ + δ'), f t ≤ ∫ t in Ico T₀ T, f t := by
    apply setIntegral_mono_set hf_int_big
    · filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
      exact hnn t (le_trans hs ht.1)
    · exact hsub.eventuallyLE
  have h3 : ∫ t in Ico T₀ (T₀ + δ'), (f T₀ / 2) = δ' * (f T₀ / 2) := by
    rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ico,
      ENNReal.toReal_ofReal (by linarith)]
    ring
  have hpos2 : 0 < δ' * (f T₀ / 2) := mul_pos hδ' (half_pos hpos)
  linarith

private noncomputable def canonBeta {m : ℕ} (G : Fin m → ℝ → ℝ) (S : Finset (Fin m))
    (a : Fin m → ℝ) (t : ℝ) : ℝ :=
  (insert (0 : ℝ) (S.image (fun j => a j - G j t))).max' (Finset.insert_nonempty _ _)

private lemma canonBeta_nonneg {m : ℕ} (G : Fin m → ℝ → ℝ) (S : Finset (Fin m))
    (a : Fin m → ℝ) (t : ℝ) : 0 ≤ canonBeta G S a t :=
  Finset.le_max' _ _ (Finset.mem_insert_self 0 _)

private lemma sub_le_canonBeta {m : ℕ} (G : Fin m → ℝ → ℝ) (S : Finset (Fin m))
    (a : Fin m → ℝ) {j : Fin m} (hj : j ∈ S) (t : ℝ) :
    a j - G j t ≤ canonBeta G S a t :=
  Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem (fun j => a j - G j t) hj))

private lemma canonBeta_le {m : ℕ} (G : Fin m → ℝ → ℝ) (S : Finset (Fin m))
    (a : Fin m → ℝ) {t y : ℝ} (hy0 : 0 ≤ y) (hy : ∀ j ∈ S, a j - G j t ≤ y) :
    canonBeta G S a t ≤ y := by
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx'
  · exact hy0
  · rcases Finset.mem_image.mp hx' with ⟨j, hj, rfl⟩
    exact hy j hj

private lemma canonBeta_eq_zero_or_exists {m : ℕ} (G : Fin m → ℝ → ℝ) (S : Finset (Fin m))
    (a : Fin m → ℝ) (t : ℝ) :
    canonBeta G S a t = 0 ∨ ∃ j ∈ S, canonBeta G S a t = a j - G j t := by
  have hmem := Finset.max'_mem (insert (0 : ℝ) (S.image (fun j => a j - G j t)))
    (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.mp hmem with h0 | h1
  · left; exact h0
  · right
    rcases Finset.mem_image.mp h1 with ⟨j, hj, hjeq⟩
    exact ⟨j, hj, hjeq.symm⟩

private lemma canonBeta_empty {m : ℕ} (G : Fin m → ℝ → ℝ) (a : Fin m → ℝ) (t : ℝ) :
    canonBeta G ∅ a t = 0 := by
  simp [canonBeta]

private lemma canonBeta_insert {m : ℕ} (G : Fin m → ℝ → ℝ) (S : Finset (Fin m))
    (j : Fin m) (a : Fin m → ℝ) (t : ℝ) :
    canonBeta G (insert j S) a t = max (a j - G j t) (canonBeta G S a t) := by
  apply le_antisymm
  · apply canonBeta_le
    · exact le_trans (canonBeta_nonneg G S a t) (le_max_right _ _)
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact le_max_left _ _
      · exact le_trans (sub_le_canonBeta G S a hi' t) (le_max_right _ _)
  · apply max_le
    · exact sub_le_canonBeta G (insert j S) a (Finset.mem_insert_self j S) t
    · apply canonBeta_le _ _ _ (canonBeta_nonneg G (insert j S) a t)
      intro i hi
      exact sub_le_canonBeta G (insert j S) a (Finset.mem_insert_of_mem hi) t

private lemma canonBeta_continuousOn {m : ℕ} {G : Fin m → ℝ → ℝ} {s : ℝ} {S : Finset (Fin m)}
    (hG : ∀ j ∈ S, ContinuousOn (G j) (Ici s)) (a : Fin m → ℝ) :
    ContinuousOn (canonBeta G S a) (Ici s) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have heq : canonBeta G ∅ a = fun _ => (0 : ℝ) := by ext t; exact canonBeta_empty G a t
    rw [heq]
    exact continuousOn_const
  | @insert j S' hj ih =>
    have h1 : ContinuousOn (fun t => a j - G j t) (Ici s) :=
      continuousOn_const.sub (hG j (Finset.mem_insert_self j S'))
    have h2 : ContinuousOn (canonBeta G S' a) (Ici s) :=
      ih (fun i hi => hG i (Finset.mem_insert_of_mem hi))
    have heq : canonBeta G (insert j S') a = fun t => max (a j - G j t) (canonBeta G S' a t) := by
      ext t; exact canonBeta_insert G S' j a t
    rw [heq]
    exact h1.sup h2

/-! ### Section 2: Uniqueness of optimal `β` and Lemma 4 -/

private lemma ae_restrict_Ici_iff {s : ℝ} {P : ℝ → Prop} :
    (∀ᵐ t ∂(volume.restrict (Ici s)), P t) ↔ ∀ᵐ t, s ≤ t → P t :=
  ae_restrict_iff' measurableSet_Ici

private lemma opt_dual_beta_ae_eq_canonBeta {m : ℕ} {G : Fin m → ℝ → ℝ} {s : ℝ}
    {S : Finset (Fin m)} {ρ a : Fin m → ℝ} {β : ℝ → ℝ}
    (hG : ∀ j ∈ S, ContinuousOn (G j) (Ici s))
    (hopt : IsOffOptDual G s S ρ a β) :
    β =ᵐ[volume.restrict (Ici s)] canonBeta G S a := by
  obtain ⟨⟨hβ_int, ha_nn, hβ_nn, hfeas⟩, hmax⟩ := hopt
  have hβ_nn' : ∀ᵐ t ∂(volume.restrict (Ici s)), 0 ≤ β t :=
    ae_restrict_Ici_iff.mpr hβ_nn
  have hfeas' : ∀ᵐ t ∂(volume.restrict (Ici s)), ∀ j ∈ S, a j - G j t ≤ β t := by
    rw [ae_all_iff]
    intro j
    by_cases hj : j ∈ S
    · filter_upwards [ae_restrict_Ici_iff.mpr (hfeas j hj)] with t ht _
      linarith
    · exact Filter.Eventually.of_forall (fun _ h => absurd h hj)
  have hle_ae : ∀ᵐ t ∂(volume.restrict (Ici s)), canonBeta G S a t ≤ β t := by
    filter_upwards [hβ_nn', hfeas'] with t h0 hS'
    exact canonBeta_le G S a h0 hS'
  have hcb_cont : ContinuousOn (canonBeta G S a) (Ici s) := canonBeta_continuousOn hG a
  have hcb_int : IntegrableOn (canonBeta G S a) (Ici s) := by
    refine hβ_int.mono' (hcb_cont.aestronglyMeasurable measurableSet_Ici) ?_
    filter_upwards [hle_ae] with t ht
    rw [Real.norm_of_nonneg (canonBeta_nonneg G S a t)]
    exact ht
  have hcb_feas : IsOffDualFeas G s S a (canonBeta G S a) := by
    refine ⟨hcb_int, ha_nn, Filter.Eventually.of_forall (fun t _ => canonBeta_nonneg G S a t), ?_⟩
    intro j hj
    exact Filter.Eventually.of_forall (fun t _ => by linarith [sub_le_canonBeta G S a hj t])
  have hobj_le : offDualObj s S ρ a (canonBeta G S a) ≤ offDualObj s S ρ a β :=
    hmax a (canonBeta G S a) hcb_feas
  have hint_le : ∫ t in Ici s, β t ≤ ∫ t in Ici s, canonBeta G S a t := by
    unfold offDualObj at hobj_le
    linarith
  have hdiff_nn : 0 ≤ᵐ[volume.restrict (Ici s)] fun t => β t - canonBeta G S a t := by
    filter_upwards [hle_ae] with t ht
    exact sub_nonneg.mpr ht
  have hdiff_int : IntegrableOn (fun t => β t - canonBeta G S a t) (Ici s) :=
    hβ_int.sub hcb_int
  have hdiff_int_eq : ∫ t in Ici s, (β t - canonBeta G S a t) = 0 := by
    have hge0 : 0 ≤ ∫ t in Ici s, (β t - canonBeta G S a t) :=
      integral_nonneg_of_ae hdiff_nn
    have hle0 : ∫ t in Ici s, (β t - canonBeta G S a t) ≤ 0 := by
      rw [integral_sub hβ_int hcb_int]
      linarith
    linarith
  have hzero_ae : (fun t => β t - canonBeta G S a t) =ᵐ[volume.restrict (Ici s)] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hdiff_nn hdiff_int).mp hdiff_int_eq
  filter_upwards [hzero_ae] with t ht
  exact sub_eq_zero.mp ht

private lemma opt_dual_beta_unique {m : ℕ} {G : Fin m → ℝ → ℝ} {s : ℝ}
    {S : Finset (Fin m)} {ρ a₁ a₂ : Fin m → ℝ} {β₁ β₂ : ℝ → ℝ}
    (hG : ∀ j ∈ S, ContinuousOn (G j) (Ici s))
    (h1 : IsOffOptDual G s S ρ a₁ β₁) (h2 : IsOffOptDual G s S ρ a₂ β₂) :
    ∀ᵐ t, s ≤ t → β₁ t = β₂ t := by
  classical
  have hcb1_ae : β₁ =ᵐ[volume.restrict (Ici s)] canonBeta G S a₁ :=
    opt_dual_beta_ae_eq_canonBeta hG h1
  have hcb2_ae : β₂ =ᵐ[volume.restrict (Ici s)] canonBeta G S a₂ :=
    opt_dual_beta_ae_eq_canonBeta hG h2
  have hcb1_int : IntegrableOn (canonBeta G S a₁) (Ici s) :=
    h1.1.1.congr_fun_ae hcb1_ae
  have hcb2_int : IntegrableOn (canonBeta G S a₂) (Ici s) :=
    h2.1.1.congr_fun_ae hcb2_ae
  let am : Fin m → ℝ := fun j => (a₁ j + a₂ j) / 2
  let βm : ℝ → ℝ := fun t => (canonBeta G S a₁ t + canonBeta G S a₂ t) / 2
  have hβm_int : IntegrableOn βm (Ici s) := (hcb1_int.add hcb2_int).div_const 2
  have hfeas_m : IsOffDualFeas G s S am βm := by
    refine ⟨hβm_int, ?_, ?_, ?_⟩
    · intro j hj
      exact div_nonneg (add_nonneg (h1.1.2.1 j hj) (h2.1.2.1 j hj)) (by norm_num)
    · exact Filter.Eventually.of_forall (fun t _ =>
        div_nonneg (add_nonneg (canonBeta_nonneg G S a₁ t) (canonBeta_nonneg G S a₂ t)) (by norm_num))
    · intro j hj
      exact Filter.Eventually.of_forall (fun t _ => by
        have l1 := sub_le_canonBeta G S a₁ hj t
        have l2 := sub_le_canonBeta G S a₂ hj t
        simp only [am, βm]
        linarith)
  have hobj_eq : offDualObj s S ρ a₁ β₁ = offDualObj s S ρ a₂ β₂ :=
    le_antisymm (h2.2 a₁ β₁ h1.1) (h1.2 a₂ β₂ h2.1)
  have hobj_m : offDualObj s S ρ am βm = offDualObj s S ρ a₁ β₁ := by
    have hi1 : ∫ t in Ici s, canonBeta G S a₁ t = ∫ t in Ici s, β₁ t :=
      integral_congr_ae hcb1_ae.symm
    have hi2 : ∫ t in Ici s, canonBeta G S a₂ t = ∫ t in Ici s, β₂ t :=
      integral_congr_ae hcb2_ae.symm
    have him : ∫ t in Ici s, βm t = ((∫ t in Ici s, β₁ t) + ∫ t in Ici s, β₂ t) / 2 := by
      simp only [βm]
      rw [integral_div, integral_add hcb1_int hcb2_int, hi1, hi2]
    have hsum : ∑ j ∈ S, am j * ρ j = (∑ j ∈ S, a₁ j * ρ j + ∑ j ∈ S, a₂ j * ρ j) / 2 := by
      simp only [am, add_div, add_mul, Finset.sum_add_distrib, div_mul_eq_mul_div,
        ← Finset.sum_div]
    unfold offDualObj at hobj_eq ⊢
    rw [hsum, him]
    linarith
  have hopt_m : IsOffOptDual G s S ρ am βm :=
    ⟨hfeas_m, fun a' β' hf' => by rw [hobj_m]; exact h1.2 a' β' hf'⟩
  have hcbm_ae : βm =ᵐ[volume.restrict (Ici s)] canonBeta G S am :=
    opt_dual_beta_ae_eq_canonBeta hG hopt_m
  have hcb1_cont := canonBeta_continuousOn hG a₁
  have hcb2_cont := canonBeta_continuousOn hG a₂
  have hcbm_cont := canonBeta_continuousOn hG am
  have hβm_cont : ContinuousOn βm (Ici s) := (hcb1_cont.add hcb2_cont).div_const 2
  have hcbm_eq : ∀ t ∈ Ici s, βm t = canonBeta G S am t :=
    continuousOn_Ici_eq_of_ae_eq hβm_cont hcbm_cont hcbm_ae
  let h : ℝ → ℝ := fun t => canonBeta G S a₂ t - canonBeta G S a₁ t
  let F : Finset ℝ := insert 0 (S.image (fun j => a₂ j - a₁ j))
  have hh_mem : ∀ t ∈ Ici s, h t ∈ (F : Set ℝ) := by
    intro t ht
    have hmt := hcbm_eq t ht
    rcases canonBeta_eq_zero_or_exists G S am t with h0 | ⟨j, hj, hjeq⟩
    · have h10 : canonBeta G S a₁ t = 0 := by
        have := canonBeta_nonneg G S a₁ t
        have := canonBeta_nonneg G S a₂ t
        simp only [βm] at hmt; linarith
      have h20 : canonBeta G S a₂ t = 0 := by
        simp only [βm] at hmt; linarith
      simp only [h, h10, h20, sub_self, F, Finset.coe_insert, mem_insert_iff, true_or]
    · have l1 : a₁ j - G j t ≤ canonBeta G S a₁ t := sub_le_canonBeta G S a₁ hj t
      have l2 : a₂ j - G j t ≤ canonBeta G S a₂ t := sub_le_canonBeta G S a₂ hj t
      have heq1 : canonBeta G S a₁ t = a₁ j - G j t := by
        simp only [βm, am] at hmt hjeq; linarith
      have heq2 : canonBeta G S a₂ t = a₂ j - G j t := by
        simp only [βm, am] at hmt hjeq; linarith
      have hht : h t = a₂ j - a₁ j := by simp only [h, heq1, heq2]; ring
      rw [hht]
      exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hj))
  have hh_cont : ContinuousOn h (Ici s) := hcb2_cont.sub hcb1_cont
  have hh_const : ∀ t ∈ Ici s, h t = h s := by
    intro t ht
    by_contra hne
    have hst : s < t := lt_of_le_of_ne ht (fun heq => hne (by rw [heq]))
    have hsub_Icc : Icc s t ⊆ Ici s := fun u hu => hu.1
    have hcont_Icc : ContinuousOn h (Icc s t) := hh_cont.mono hsub_Icc
    have himg : Icc (min (h s) (h t)) (max (h s) (h t)) ⊆ (F : Set ℝ) := by
      intro y hy
      rcases le_total (h s) (h t) with hle | hle
      · rw [min_eq_left hle, max_eq_right hle] at hy
        obtain ⟨u, hu, rfl⟩ := intermediate_value_Icc hst.le hcont_Icc hy
        exact hh_mem u (hsub_Icc hu)
      · rw [min_eq_right hle, max_eq_left hle] at hy
        obtain ⟨u, hu, rfl⟩ := intermediate_value_Icc' hst.le hcont_Icc hy
        exact hh_mem u (hsub_Icc hu)
    have hlt_mm : min (h s) (h t) < max (h s) (h t) := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [min_eq_right hlt.le, max_eq_left hlt.le]; exact hlt
      · rw [min_eq_left hgt.le, max_eq_right hgt.le]; exact hgt
    exact (Set.Icc_infinite hlt_mm).not_finite (F.finite_toSet.subset himg)
  have hh_int : IntegrableOn h (Ici s) := hcb2_int.sub hcb1_int
  have hconst_int : IntegrableOn (fun _ : ℝ => h s) (Ici s) :=
    hh_int.congr_fun hh_const measurableSet_Ici
  have hhs0 : h s = 0 := const_eq_zero_of_integrableOn_Ici hconst_int
  have hcb_eq : ∀ t ∈ Ici s, canonBeta G S a₁ t = canonBeta G S a₂ t := by
    intro t ht
    have := hh_const t ht
    rw [hhs0] at this
    exact (sub_eq_zero.mp this).symm
  rw [← ae_restrict_Ici_iff]
  filter_upwards [hcb1_ae, hcb2_ae, ae_restrict_mem measurableSet_Ici] with t ht1 ht2 hts
  rw [ht1, ht2, hcb_eq t hts]

private lemma lemma_4_aux {m : ℕ} {G : Fin m → ℝ → ℝ} {s : ℝ}
    {A : Finset (Fin m)} {ρ : Fin m → ℝ} {k : Fin m} (hk : k ∉ A)
    (hG : ∀ j ∈ insert k A, ContinuousOn (G j) (Ici s))
    {a : Fin m → ℝ} {β : ℝ → ℝ} (hold : IsOffOptDual G s A ρ a β)
    {a' : Fin m → ℝ} {β' : ℝ → ℝ} (hnew : IsOffOptDual G s (insert k A) ρ a' β') :
    ∀ᵐ t, s ≤ t → β t ≤ β' t := by
  classical
  let aMin : Fin m → ℝ := fun j => min (a j) (a' j)
  let βMin : ℝ → ℝ := fun t => min (β t) (β' t)
  let aMax : Fin m → ℝ := fun j => if j = k then a' k else max (a j) (a' j)
  let βMax : ℝ → ℝ := fun t => max (β t) (β' t)
  have hβMin_int : IntegrableOn βMin (Ici s) := hold.1.1.inf hnew.1.1
  have hβMax_int : IntegrableOn βMax (Ici s) := hold.1.1.sup hnew.1.1
  have hfeas_min : IsOffDualFeas G s A aMin βMin := by
    refine ⟨hβMin_int, ?_, ?_, ?_⟩
    · intro j hj
      exact le_min (hold.1.2.1 j hj) (hnew.1.2.1 j (Finset.mem_insert_of_mem hj))
    · filter_upwards [hold.1.2.2.1, hnew.1.2.2.1] with t ht1 ht2 hst
      exact le_min (ht1 hst) (ht2 hst)
    · intro j hj
      filter_upwards [hold.1.2.2.2 j hj, hnew.1.2.2.2 j (Finset.mem_insert_of_mem hj)]
        with t ht1 ht2 hst
      simp only [aMin, βMin]
      rcases le_total (β t) (β' t) with hle | hle
      · rw [min_eq_left hle]; exact le_trans (min_le_left _ _) (ht1 hst)
      · rw [min_eq_right hle]; exact le_trans (min_le_right _ _) (ht2 hst)
  have hfeas_max : IsOffDualFeas G s (insert k A) aMax βMax := by
    refine ⟨hβMax_int, ?_, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with hjk | hj'
      · rw [hjk]; simp [aMax, hnew.1.2.1 k (Finset.mem_insert_self k A)]
      · have hne : j ≠ k := fun heq => hk (heq ▸ hj')
        simp only [aMax, hne, ↓reduceIte]
        exact le_trans (hold.1.2.1 j hj') (le_max_left _ _)
    · filter_upwards [hold.1.2.2.1] with t ht1 hst
      exact le_trans (ht1 hst) (le_max_left _ _)
    · intro j hj
      rcases Finset.mem_insert.mp hj with hjk | hj'
      · rw [hjk]
        filter_upwards [hnew.1.2.2.2 k (Finset.mem_insert_self k A)] with t ht hst
        simp only [aMax, ↓reduceIte, βMax]
        linarith [ht hst, le_max_right (β t) (β' t)]
      · have hne : j ≠ k := fun heq => hk (heq ▸ hj')
        filter_upwards [hold.1.2.2.2 j hj', hnew.1.2.2.2 j (Finset.mem_insert_of_mem hj')]
          with t ht1 ht2 hst
        simp only [aMax, hne, ↓reduceIte, βMax]
        exact max_le (by linarith [ht1 hst, le_max_left (β t) (β' t)])
          (by linarith [ht2 hst, le_max_right (β t) (β' t)])
  have hsum_int : (∫ t in Ici s, βMin t) + ∫ t in Ici s, βMax t =
      (∫ t in Ici s, β t) + ∫ t in Ici s, β' t := by
    rw [← integral_add hβMin_int hβMax_int, ← integral_add hold.1.1 hnew.1.1]
    congr 1; ext t; exact min_add_max (β t) (β' t)
  have hsum_a : ∑ j ∈ A, aMin j * ρ j + ∑ j ∈ insert k A, aMax j * ρ j =
      ∑ j ∈ A, a j * ρ j + ∑ j ∈ insert k A, a' j * ρ j := by
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    have hA_eq : ∑ j ∈ A, aMax j * ρ j = ∑ j ∈ A, max (a j) (a' j) * ρ j := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hne : j ≠ k := fun heq => hk (heq ▸ hj)
      simp [aMax, hne]
    rw [hA_eq]
    have hk_eq : aMax k = a' k := by simp [aMax]
    rw [hk_eq]
    have hcomb : ∑ j ∈ A, aMin j * ρ j + ∑ j ∈ A, max (a j) (a' j) * ρ j =
        ∑ j ∈ A, a j * ρ j + ∑ j ∈ A, a' j * ρ j := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [aMin, ← add_mul, min_add_max]
    linarith
  have hobj_sum : offDualObj s A ρ aMin βMin + offDualObj s (insert k A) ρ aMax βMax =
      offDualObj s A ρ a β + offDualObj s (insert k A) ρ a' β' := by
    unfold offDualObj; linarith
  have hle_old : offDualObj s A ρ aMin βMin ≤ offDualObj s A ρ a β :=
    hold.2 aMin βMin hfeas_min
  have hle_new : offDualObj s (insert k A) ρ aMax βMax ≤ offDualObj s (insert k A) ρ a' β' :=
    hnew.2 aMax βMax hfeas_max
  have heq_new : offDualObj s (insert k A) ρ aMax βMax = offDualObj s (insert k A) ρ a' β' := by
    linarith
  have hopt_max : IsOffOptDual G s (insert k A) ρ aMax βMax :=
    ⟨hfeas_max, fun a'' β'' hf'' => by rw [heq_new]; exact hnew.2 a'' β'' hf''⟩
  have hae := opt_dual_beta_unique hG hnew hopt_max
  filter_upwards [hae] with t ht hst
  have heq := ht hst
  simp only [βMax] at heq
  linarith [le_max_left (β t) (β' t)]

/-! ### Section 3: Weak duality and strong duality from an optimal integral schedule -/

private lemma weak_duality_on_set {m : ℕ} {G : Fin m → ℝ → ℝ} {s : ℝ}
    {S : Finset (Fin m)} {a : Fin m → ℝ} {β : ℝ → ℝ} {x : Fin m → ℝ → ℝ} {E : Set ℝ}
    (hE_meas : MeasurableSet E) (hE_sub : E ⊆ Ici s)
    (hfeas : IsOffDualFeas G s S a β)
    (hx_int : ∀ j ∈ S, IntegrableOn (x j) E)
    (hgx_int : ∀ j ∈ S, IntegrableOn (fun t => G j t * x j t) E)
    (hx_nn : ∀ j ∈ S, ∀ t ∈ E, 0 ≤ x j t)
    (hx_cap : ∀ t ∈ E, ∑ j ∈ S, x j t ≤ 1) :
    ∑ j ∈ S, a j * (∫ t in E, x j t) - ∫ t in E, β t ≤
      ∑ j ∈ S, ∫ t in E, G j t * x j t := by
  have hβ_int_E : IntegrableOn β E := hfeas.1.mono_set hE_sub
  have hβ_nn_E : ∀ᵐ t ∂(volume.restrict E), 0 ≤ β t := by
    have hle_m : volume.restrict E ≤ volume.restrict (Ici s) := Measure.restrict_mono hE_sub le_rfl
    exact Measure.ae_le_iff_absolutelyContinuous.mpr (Measure.absolutelyContinuous_of_le hle_m)
      (ae_restrict_Ici_iff.mpr hfeas.2.2.1)
  have hdual_E : ∀ᵐ t ∂(volume.restrict E), ∀ j ∈ S, a j ≤ β t + G j t := by
    rw [ae_all_iff]
    intro j
    by_cases hj : j ∈ S
    · have hle_m : volume.restrict E ≤ volume.restrict (Ici s) := Measure.restrict_mono hE_sub le_rfl
      have h1 := Measure.ae_le_iff_absolutelyContinuous.mpr (Measure.absolutelyContinuous_of_le hle_m)
        (ae_restrict_Ici_iff.mpr (hfeas.2.2.2 j hj))
      filter_upwards [h1] with t ht _
      exact ht
    · exact Filter.Eventually.of_forall (fun _ h => absurd h hj)
  have hpt : ∀ᵐ t ∂(volume.restrict E),
      (∑ j ∈ S, a j * x j t) - β t ≤ ∑ j ∈ S, G j t * x j t := by
    filter_upwards [hβ_nn_E, hdual_E, ae_restrict_mem hE_meas] with t hβ0 hd htE
    have h1 : ∑ j ∈ S, a j * x j t ≤ ∑ j ∈ S, (β t + G j t) * x j t := by
      refine Finset.sum_le_sum (fun j hj => ?_)
      exact mul_le_mul_of_nonneg_right (hd j hj) (hx_nn j hj t htE)
    have h2 : ∑ j ∈ S, (β t + G j t) * x j t =
        β t * (∑ j ∈ S, x j t) + ∑ j ∈ S, G j t * x j t := by
      simp_rw [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    have h3 : β t * (∑ j ∈ S, x j t) ≤ β t * 1 :=
      mul_le_mul_of_nonneg_left (hx_cap t htE) hβ0
    linarith
  have hlhs_int : IntegrableOn (fun t => (∑ j ∈ S, a j * x j t) - β t) E :=
    (integrable_finsetSum S (fun j hj => (hx_int j hj).const_mul (a j))).sub hβ_int_E
  have hrhs_int : IntegrableOn (fun t => ∑ j ∈ S, G j t * x j t) E :=
    integrable_finsetSum S (fun j hj => hgx_int j hj)
  have hint_le := integral_mono_ae hlhs_int hrhs_int hpt
  rw [integral_sub (integrable_finsetSum S (fun j hj => (hx_int j hj).const_mul (a j))) hβ_int_E,
    integral_finsetSum S (fun j hj => (hx_int j hj).const_mul (a j)),
    integral_finsetSum S (fun j hj => hgx_int j hj)] at hint_le
  simp_rw [integral_const_mul] at hint_le
  exact hint_le

private lemma measurableSet_inter_lt_of_continuousOn {s : ℝ} {E : Set ℝ} {f g : ℝ → ℝ}
    (hE : MeasurableSet E) (hsub : E ⊆ Ici s)
    (hf : ContinuousOn f (Ici s)) (hg : ContinuousOn g (Ici s)) :
    MeasurableSet {t ∈ E | f t < g t} := by
  have hcont : Continuous (fun t : Ici s => g t.1 - f t.1) :=
    (hg.sub hf).domRestrict
  have hopen : IsOpen ((fun t : Ici s => g t.1 - f t.1) ⁻¹' Ioi (0 : ℝ)) :=
    isOpen_Ioi.preimage hcont
  rw [isOpen_induced_iff] at hopen
  obtain ⟨U, hU_open, hU_eq⟩ := hopen
  have heq : {t ∈ E | f t < g t} = E ∩ U := by
    ext t
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨htE, hlt⟩
      refine ⟨htE, ?_⟩
      have hmem : (⟨t, hsub htE⟩ : Ici s) ∈ (fun u : Ici s => g u.1 - f u.1) ⁻¹' Ioi 0 := by
        simpa [sub_pos] using hlt
      rw [← hU_eq] at hmem
      exact hmem
    · rintro ⟨htE, htU⟩
      refine ⟨htE, ?_⟩
      have hmem : (⟨t, hsub htE⟩ : Ici s) ∈ ((↑) : Ici s → ℝ) ⁻¹' U := htU
      rw [hU_eq] at hmem
      simpa [sub_pos] using hmem
  rw [heq]
  exact hE.inter hU_open.measurableSet

private lemma measurableSet_inter_le_of_continuousOn {s : ℝ} {E : Set ℝ} {f g : ℝ → ℝ}
    (hE : MeasurableSet E) (hsub : E ⊆ Ici s)
    (hf : ContinuousOn f (Ici s)) (hg : ContinuousOn g (Ici s)) :
    MeasurableSet {t ∈ E | f t ≤ g t} := by
  have heq : {t ∈ E | f t ≤ g t} = E \ {t ∈ E | g t < f t} := by
    ext t
    simp only [mem_ofPred_eq, mem_sdiff, not_and, not_lt]
    tauto
  rw [heq]
  exact hE.diff (measurableSet_inter_lt_of_continuousOn hE hsub hg hf)

private def IsBoxSched {m : ℕ} (s T : ℝ) (S : Finset (Fin m)) (y : Fin m → ℝ → ℝ) : Prop :=
  (∀ j, Measurable (y j)) ∧ (∀ j t, 0 ≤ y j t) ∧ (∀ j t, t ∉ Ico s T → y j t = 0) ∧
  (∀ j, j ∉ S → ∀ t, y j t = 0) ∧ (∀ t, ∑ j, y j t ≤ 1)

private lemma boxSched_le_one {m : ℕ} {s T : ℝ} {S : Finset (Fin m)} {y : Fin m → ℝ → ℝ}
    (hy : IsBoxSched s T S y) (j : Fin m) (t : ℝ) : y j t ≤ 1 := by
  calc y j t ≤ ∑ i, y i t :=
        Finset.single_le_sum (fun i _ => hy.2.1 i t) (Finset.mem_univ j)
    _ ≤ 1 := hy.2.2.2.2 t

private lemma boxSched_integrableOn {m : ℕ} {s T : ℝ} {S : Finset (Fin m)} {y : Fin m → ℝ → ℝ}
    (hy : IsBoxSched s T S y) (j : Fin m) : IntegrableOn (y j) (Ico s T) := by
  refine (integrableOn_const (C := (1 : ℝ))
    (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)).mono'
    (hy.1 j).aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_of_nonneg (hy.2.1 j t)]
  exact boxSched_le_one hy j t

private lemma boxSched_cost_integrableOn {m : ℕ} {I : Instance m} {s T : ℝ}
    {S : Finset (Fin m)} {y : Fin m → ℝ → ℝ}
    (hI : ∀ j, I.JobStanding j) (hS : ∀ j ∈ S, I.r j ≤ s)
    (hy : IsBoxSched s T S y) {j : Fin m} (hj : j ∈ S) :
    IntegrableOn (fun t => I.g j t * y j t) (Ico s T) := by
  have hg_cont : ContinuousOn (I.g j) (Icc s T) :=
    (jobStanding_continuousOn (hI j)).mono (fun t ht => le_trans (hS j hj) ht.1)
  have hg_int : IntegrableOn (I.g j) (Ico s T) :=
    hg_cont.integrableOn_Icc.mono_set Ico_subset_Icc_self
  refine hg_int.mono'
    (((hg_cont.mono Ico_subset_Icc_self).aestronglyMeasurable measurableSet_Ico).mul
      (hy.1 j).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
  have hgnn : 0 ≤ I.g j t := (hI j).2.2.1 t (le_trans (hS j hj) ht.1)
  rw [Real.norm_of_nonneg (mul_nonneg hgnn (hy.2.1 j t))]
  calc I.g j t * y j t ≤ I.g j t * 1 :=
        mul_le_mul_of_nonneg_left (boxSched_le_one hy j t) hgnn
    _ = I.g j t := mul_one _

private lemma lintegral_ofReal_eq_ofReal_setIntegral_of_support {f : ℝ → ℝ} {E : Set ℝ}
    (hE : MeasurableSet E) (hf_nn : ∀ t, 0 ≤ f t) (hf_zero : ∀ t, t ∉ E → f t = 0)
    (hf_int : IntegrableOn f E) :
    ∫⁻ t, ENNReal.ofReal (f t) = ENNReal.ofReal (∫ t in E, f t) := by
  have h1 : ∫⁻ t, ENNReal.ofReal (f t) = ∫⁻ t in E, ENNReal.ofReal (f t) := by
    rw [← lintegral_indicator hE]
    congr 1; ext t
    by_cases ht : t ∈ E
    · simp [ht]
    · simp [ht, hf_zero t ht]
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal hf_int (Filter.Eventually.of_forall hf_nn)]

private lemma strong_duality_of_opt_integral {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j)
    (s : ℝ) (S : Finset (Fin m)) (ρ : Fin m → ℝ)
    (hS : ∀ j ∈ S, I.r j ≤ s) (hρ : ∀ j ∈ S, 0 < ρ j)
    (x : Fin m → ℝ → ℝ) (hx : IsOptIntegral I.g s S ρ x) :
    ∃ (a : Fin m → ℝ) (β : ℝ → ℝ),
      IsOffDualFeas I.g s S a β ∧
      offDualObj s S ρ a β = ∑ j ∈ S, ∫ t in Ici s, I.g j t * x j t := by
  classical
  by_cases hS_empty : S = ∅
  · subst hS_empty
    refine ⟨0, 0, ⟨integrableOn_zero, by simp, by simp, by simp⟩, by simp [offDualObj]⟩
  have hS_ne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
  obtain ⟨⟨hx_meas, hx_bin, hx_bef, hx_out, hx_cap, hx_len, ⟨T_x, hx_fin⟩⟩, hx_opt⟩ := hx
  have hx_nn : ∀ j t, 0 ≤ x j t := fun j t => by
    rcases hx_bin j t with h | h <;> linarith
  have hx_le1 : ∀ j t, x j t ≤ 1 := fun j t => by
    rcases hx_bin j t with h | h <;> linarith
  set T₀ : ℝ := max s T_x
  have hsT₀ : s ≤ T₀ := le_max_left s T_x
  have hx_after : ∀ j t, T₀ < t → x j t = 0 := fun j t ht =>
    hx_fin j t (lt_of_le_of_lt (le_max_right s T_x) ht)
  set L : ℝ := ∑ j ∈ S, ρ j
  have hL_pos : 0 < L := Finset.sum_pos (fun j hj => hρ j hj) hS_ne
  set T : ℝ := T₀ + L + 2
  have hT₀T : T₀ < T := by linarith
  have hsT : s < T := lt_of_le_of_lt hsT₀ hT₀T
  -- Integrability and cost of x
  have hx_int_Icc : ∀ j, IntegrableOn (x j) (Icc s T₀) := fun j =>
    (integrableOn_const (C := (1 : ℝ)) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).mono'
      (hx_meas j).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => by rw [Real.norm_of_nonneg (hx_nn j t)]; exact hx_le1 j t))
  have hx_int_Ici : ∀ j, IntegrableOn (x j) (Ici s) := by
    intro j
    have heq : (Icc s T₀).indicator (x j) = (Ici s).indicator (x j) := by
      ext t
      by_cases ht : t ∈ Ici s
      · by_cases hle : t ≤ T₀
        · simp [ht, hle, mem_Icc, mem_Ici.mp ht]
        · have hgt : T₀ < t := not_le.mp hle
          simp [ht, hle, mem_Icc, hx_after j t hgt]
      · have hnot : t ∉ Icc s T₀ := fun h => ht h.1
        simp [ht, hnot]
    have hi : Integrable ((Icc s T₀).indicator (x j)) :=
      (integrable_indicator_iff measurableSet_Icc).mpr (hx_int_Icc j)
    rw [heq] at hi
    exact (integrable_indicator_iff measurableSet_Ici).mp hi
  have hx_len_real : ∀ j ∈ S, ∫ t in Ico s T₀, x j t = ρ j := by
    intro j hj
    have h1 : ∫⁻ t, ENNReal.ofReal (x j t) = ENNReal.ofReal (∫ t in Icc s T₀, x j t) := by
      apply lintegral_ofReal_eq_ofReal_setIntegral_of_support measurableSet_Icc (hx_nn j)
      · intro t ht
        rw [mem_Icc, not_and_or, not_le, not_le] at ht
        rcases ht with hlt | hgt
        · exact hx_bef j t hlt
        · exact hx_after j t hgt
      · exact hx_int_Icc j
    rw [hx_len j hj] at h1
    have h2 : ρ j = ∫ t in Icc s T₀, x j t :=
      (ENNReal.ofReal_eq_ofReal_iff (le_of_lt (hρ j hj))
        (setIntegral_nonneg measurableSet_Icc (fun t _ => hx_nn j t))).mp h1
    rw [h2]
    exact setIntegral_congr_set Ico_ae_eq_Icc
  have hgx_int_Icc : ∀ j ∈ S, IntegrableOn (fun t => I.g j t * x j t) (Icc s T₀) := by
    intro j hj
    have hg_cont : ContinuousOn (I.g j) (Icc s T₀) :=
      (jobStanding_continuousOn (hI j)).mono (fun t ht => le_trans (hS j hj) ht.1)
    refine hg_cont.integrableOn_Icc.mono'
      ((hg_cont.aestronglyMeasurable measurableSet_Icc).mul (hx_meas j).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hgnn : 0 ≤ I.g j t := (hI j).2.2.1 t (le_trans (hS j hj) ht.1)
    rw [Real.norm_of_nonneg (mul_nonneg hgnn (hx_nn j t))]
    calc I.g j t * x j t ≤ I.g j t * 1 := mul_le_mul_of_nonneg_left (hx_le1 j t) hgnn
      _ = I.g j t := mul_one _
  have hgx_int_Ici : ∀ j ∈ S, IntegrableOn (fun t => I.g j t * x j t) (Ici s) := by
    intro j hj
    have heq : (Icc s T₀).indicator (fun t => I.g j t * x j t) =
        (Ici s).indicator (fun t => I.g j t * x j t) := by
      ext t
      by_cases ht : t ∈ Ici s
      · by_cases hle : t ≤ T₀
        · simp [ht, hle, mem_Icc, mem_Ici.mp ht]
        · simp [ht, hle, mem_Icc, hx_after j t (not_le.mp hle)]
      · have hnot : t ∉ Icc s T₀ := fun h => ht h.1
        simp [ht, hnot]
    have hi : Integrable ((Icc s T₀).indicator (fun t => I.g j t * x j t)) :=
      (integrable_indicator_iff measurableSet_Icc).mpr (hgx_int_Icc j hj)
    rw [heq] at hi
    exact (integrable_indicator_iff measurableSet_Ici).mp hi
  have hgx_eq_Ico : ∀ j ∈ S,
      ∫ t in Ici s, I.g j t * x j t = ∫ t in Ico s T₀, I.g j t * x j t := by
    intro j hj
    have h1 : ∫ t in Ici s, I.g j t * x j t = ∫ t in Icc s T₀, I.g j t * x j t := by
      rw [← integral_indicator measurableSet_Ici, ← integral_indicator measurableSet_Icc]
      congr 1; ext t
      by_cases ht : t ∈ Ici s
      · by_cases hle : t ≤ T₀
        · simp [ht, hle, mem_Icc, mem_Ici.mp ht]
        · simp [ht, hle, mem_Icc, hx_after j t (not_le.mp hle)]
      · have hnot : t ∉ Icc s T₀ := fun h => ht h.1
        simp [ht, hnot]
    rw [h1]
    exact (setIntegral_congr_set Ico_ae_eq_Icc).symm
  set OPT : ℝ := ∑ j ∈ S, ∫ t in Ici s, I.g j t * x j t
  have hOPT_cost : offCost I.g x = ENNReal.ofReal OPT := by
    unfold offCost
    have hsum_S : ∑ j : Fin m, ∫⁻ t, ENNReal.ofReal (I.g j t * x j t) =
        ∑ j ∈ S, ∫⁻ t, ENNReal.ofReal (I.g j t * x j t) := by
      symm
      refine Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => ?_)
      simp [hx_out j hj]
    rw [hsum_S]
    have hterm : ∀ j ∈ S, ∫⁻ t, ENNReal.ofReal (I.g j t * x j t) =
        ENNReal.ofReal (∫ t in Ici s, I.g j t * x j t) := by
      intro j hj
      apply lintegral_ofReal_eq_ofReal_setIntegral_of_support measurableSet_Ici
      · intro t
        by_cases ht : s ≤ t
        · exact mul_nonneg ((hI j).2.2.1 t (le_trans (hS j hj) ht)) (hx_nn j t)
        · rw [hx_bef j t (not_le.mp ht), mul_zero]
      · intro t ht
        rw [hx_bef j t (not_le.mp ht), mul_zero]
      · exact hgx_int_Ici j hj
    rw [Finset.sum_congr rfl hterm, ← ENNReal.ofReal_sum_of_nonneg]
    intro j hj
    exact setIntegral_nonneg measurableSet_Ici
      (fun t ht => mul_nonneg ((hI j).2.2.1 t (le_trans (hS j hj) ht)) (hx_nn j t))
  -- Define open convex set U in (S → ℝ) × ℝ
  let U : Set ((S → ℝ) × ℝ) :=
    {p | ∃ y, IsBoxSched s T S y ∧
      (∀ j : S, p.1 j < ∫ t in Ico s T, y j.1 t) ∧
      (∑ j ∈ S, ∫ t in Ico s T, I.g j t * y j t) < p.2}
  have hU_open : IsOpen U := by
    have heq : U = ⋃ y : {y | IsBoxSched s T S y},
        {p : (S → ℝ) × ℝ | (∀ j : S, p.1 j < ∫ t in Ico s T, y.1 j.1 t) ∧
          (∑ j ∈ S, ∫ t in Ico s T, I.g j t * y.1 j t) < p.2} := by
      ext p
      simp only [U, mem_iUnion, mem_ofPred_eq]
      constructor
      · rintro ⟨y, hy, hw, hc⟩; exact ⟨⟨y, hy⟩, hw, hc⟩
      · rintro ⟨⟨y, hy⟩, hw, hc⟩; exact ⟨y, hy, hw, hc⟩
    rw [heq]
    refine isOpen_iUnion (fun y => ?_)
    refine IsOpen.inter ?_ (isOpen_lt continuous_const continuous_snd)
    change IsOpen {p : (S → ℝ) × ℝ | ∀ j : S, p.1 j < ∫ t in Ico s T, y.1 j.1 t}
    have hfin : {p : (S → ℝ) × ℝ | ∀ j : S, p.1 j < ∫ t in Ico s T, y.1 j.1 t} =
        ⋂ j : S, {p : (S → ℝ) × ℝ | p.1 j < ∫ t in Ico s T, y.1 j.1 t} := by
      ext p; simp only [mem_ofPred_eq, mem_iInter]
    rw [hfin]
    exact isOpen_iInter_of_finite (fun j =>
      isOpen_lt ((continuous_apply j).comp continuous_fst) continuous_const)
  have hU_conv : Convex ℝ U := by
    intro p₁ hp₁ p₂ hp₂ u v hu hv huv
    rcases hp₁ with ⟨y₁, hy₁, hw₁, hc₁⟩
    rcases hp₂ with ⟨y₂, hy₂, hw₂, hc₂⟩
    let y : Fin m → ℝ → ℝ := fun j t => u * y₁ j t + v * y₂ j t
    have hy : IsBoxSched s T S y := by
      refine ⟨fun j => (hy₁.1 j).const_mul u |>.add ((hy₂.1 j).const_mul v),
        fun j t => add_nonneg (mul_nonneg hu (hy₁.2.1 j t)) (mul_nonneg hv (hy₂.2.1 j t)),
        fun j t ht => by simp [y, hy₁.2.2.1 j t ht, hy₂.2.2.1 j t ht],
        fun j hj t => by simp [y, hy₁.2.2.2.1 j hj t, hy₂.2.2.2.1 j hj t],
        fun t => ?_⟩
      simp only [y, Finset.sum_add_distrib, ← Finset.mul_sum]
      calc u * ∑ j, y₁ j t + v * ∑ j, y₂ j t ≤ u * 1 + v * 1 :=
            add_le_add (mul_le_mul_of_nonneg_left (hy₁.2.2.2.2 t) hu)
              (mul_le_mul_of_nonneg_left (hy₂.2.2.2.2 t) hv)
        _ = 1 := by linarith
    refine ⟨y, hy, ?_, ?_⟩
    · intro j
      have hi : ∫ t in Ico s T, y j.1 t =
          u * (∫ t in Ico s T, y₁ j.1 t) + v * ∫ t in Ico s T, y₂ j.1 t := by
        simp only [y]
        rw [integral_add ((boxSched_integrableOn hy₁ j.1).const_mul u)
          ((boxSched_integrableOn hy₂ j.1).const_mul v),
          integral_const_mul, integral_const_mul]
      rw [hi]
      change u * p₁.1 j + v * p₂.1 j < _
      rcases eq_or_lt_of_le hu with rfl | hu'
      · have hv1 : v = 1 := by linarith
        subst hv1; simp [hw₂ j]
      · have h1 : u * p₁.1 j < u * ∫ t in Ico s T, y₁ j.1 t :=
          mul_lt_mul_of_pos_left (hw₁ j) hu'
        have h2 : v * p₂.1 j ≤ v * ∫ t in Ico s T, y₂ j.1 t :=
          mul_le_mul_of_nonneg_left (le_of_lt (hw₂ j)) hv
        linarith
    · have hi : ∑ j ∈ S, ∫ t in Ico s T, I.g j t * y j t =
          u * (∑ j ∈ S, ∫ t in Ico s T, I.g j t * y₁ j t) +
          v * (∑ j ∈ S, ∫ t in Ico s T, I.g j t * y₂ j t) := by
        have hterm : ∀ j ∈ S, ∫ t in Ico s T, I.g j t * y j t =
            u * (∫ t in Ico s T, I.g j t * y₁ j t) + v * ∫ t in Ico s T, I.g j t * y₂ j t := by
          intro j hj
          have hrew : (fun t => I.g j t * y j t) =
              fun t => u * (I.g j t * y₁ j t) + v * (I.g j t * y₂ j t) := by
            ext t; simp only [y]; ring
          rw [hrew, integral_add ((boxSched_cost_integrableOn hI hS hy₁ hj).const_mul u)
            ((boxSched_cost_integrableOn hI hS hy₂ hj).const_mul v),
            integral_const_mul, integral_const_mul]
        rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [hi]
      change _ < u * p₁.2 + v * p₂.2
      rcases eq_or_lt_of_le hu with rfl | hu'
      · have hv1 : v = 1 := by linarith
        subst hv1; simp [hc₂]
      · have h1 : u * (∑ j ∈ S, ∫ t in Ico s T, I.g j t * y₁ j t) < u * p₁.2 :=
          mul_lt_mul_of_pos_left hc₁ hu'
        have h2 : v * (∑ j ∈ S, ∫ t in Ico s T, I.g j t * y₂ j t) ≤ v * p₂.2 :=
          mul_le_mul_of_nonneg_left (le_of_lt hc₂) hv
        linarith
  -- (ρ|_S, OPT) ∉ U
  let p₀ : (S → ℝ) × ℝ := (fun j => ρ j.1, OPT)
  have hp₀_not : p₀ ∉ U := by
    rintro ⟨y, hy, hw, hc⟩
    have hy_feas : IsOffFracSched s S ρ y := by
      refine ⟨hy.1, hy.2.1, fun j t ht => hy.2.2.1 j t (fun h => not_lt.mpr h.1 ht),
        hy.2.2.2.1, hy.2.2.2.2, ?_⟩
      intro j hj
      rw [lintegral_ofReal_eq_ofReal_setIntegral_of_support measurableSet_Ico
        (hy.2.1 j) (hy.2.2.1 j) (boxSched_integrableOn hy j)]
      exact ENNReal.ofReal_le_ofReal (le_of_lt (hw ⟨j, hj⟩))
    have hcost_y : offCost I.g y =
        ENNReal.ofReal (∑ j ∈ S, ∫ t in Ico s T, I.g j t * y j t) := by
      unfold offCost
      have hsum_S : ∑ j : Fin m, ∫⁻ t, ENNReal.ofReal (I.g j t * y j t) =
          ∑ j ∈ S, ∫⁻ t, ENNReal.ofReal (I.g j t * y j t) := by
        symm
        refine Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => ?_)
        simp [hy.2.2.2.1 j hj]
      rw [hsum_S]
      have hterm : ∀ j ∈ S, ∫⁻ t, ENNReal.ofReal (I.g j t * y j t) =
          ENNReal.ofReal (∫ t in Ico s T, I.g j t * y j t) := by
        intro j hj
        apply lintegral_ofReal_eq_ofReal_setIntegral_of_support measurableSet_Ico
        · intro t
          by_cases ht : t ∈ Ico s T
          · exact mul_nonneg ((hI j).2.2.1 t (le_trans (hS j hj) ht.1)) (hy.2.1 j t)
          · rw [hy.2.2.1 j t ht, mul_zero]
        · intro t ht
          rw [hy.2.2.1 j t ht, mul_zero]
        · exact boxSched_cost_integrableOn hI hS hy hj
      rw [Finset.sum_congr rfl hterm, ← ENNReal.ofReal_sum_of_nonneg]
      intro j hj
      exact setIntegral_nonneg measurableSet_Ico
        (fun t ht => mul_nonneg ((hI j).2.2.1 t (le_trans (hS j hj) ht.1)) (hy.2.1 j t))
    have hle := hx_opt y hy_feas
    rw [hOPT_cost, hcost_y] at hle
    have hcost_nn : 0 ≤ ∑ j ∈ S, ∫ t in Ico s T, I.g j t * y j t :=
      Finset.sum_nonneg (fun j hj => setIntegral_nonneg measurableSet_Ico
        (fun t ht => mul_nonneg ((hI j).2.2.1 t (le_trans (hS j hj) ht.1)) (hy.2.1 j t)))
    have hle_real : OPT ≤ ∑ j ∈ S, ∫ t in Ico s T, I.g j t * y j t := by
      by_cases hOPT_nn : 0 ≤ OPT
      · exact (ENNReal.ofReal_le_ofReal_iff hcost_nn).mp hle
      · linarith
    exact not_lt.mpr hle_real hc
  -- Build Slater schedule y₀ on Ico s T
  let δ_sl : ℝ := 1 / (S.card : ℝ)
  have hcard_pos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr hS_ne.card_pos
  have hδ_pos : 0 < δ_sl := div_pos one_pos hcard_pos
  let len : Fin m → ℝ := fun j => if j ∈ S then ρ j + δ_sl else 0
  have hlen_nn : ∀ j, 0 ≤ len j := fun j => by
    by_cases hj : j ∈ S
    · simp only [len, hj, ↓reduceIte]; linarith [hρ j hj]
    · simp [len, hj]
  have hlen_sum : ∑ j : Fin m, len j = L + 1 := by
    have h1 : ∑ j : Fin m, len j = ∑ j ∈ S, (ρ j + δ_sl) := by
      rw [← Finset.sum_subset (Finset.subset_univ S)]
      · exact Finset.sum_congr rfl (fun j hj => by simp [len, hj])
      · intro j _ hj; simp [len, hj]
    rw [h1, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hcard_ne : (S.card : ℝ) ≠ 0 := ne_of_gt hcard_pos
    simp only [δ_sl, L]
    field_simp [hcard_ne]
  let st : Fin m → ℝ := fun j => s + ∑ i ∈ Finset.univ.filter (· < j), len i
  let y₀ : Fin m → ℝ → ℝ := fun j t => (Ico (st j) (st j + len j)).indicator (fun _ => (1 : ℝ)) t
  have hIco_sub : ∀ j, Ico (st j) (st j + len j) ⊆ Ico s T := by
    intro j t ht
    have hge : s ≤ st j := by
      simp only [st]
      have hsnn : 0 ≤ ∑ i ∈ Finset.univ.filter (· < j), len i :=
        Finset.sum_nonneg (fun i _ => hlen_nn i)
      linarith
    have hle : st j + len j ≤ s + ∑ i : Fin m, len i := by
      simp only [st]
      have hsub : insert j (Finset.univ.filter (· < j)) ⊆ Finset.univ := Finset.subset_univ _
      have hnotmem : j ∉ Finset.univ.filter (· < j) := by simp
      have hsum_le := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hlen_nn i)
      rw [Finset.sum_insert hnotmem] at hsum_le
      linarith
    exact ⟨le_trans hge ht.1, lt_of_lt_of_le ht.2 (by linarith [hlen_sum, hsT₀])⟩
  have hdisj : ∀ i j : Fin m, i < j →
      Disjoint (Ico (st i) (st i + len i)) (Ico (st j) (st j + len j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro t hti htj
    have hsub : insert i (Finset.univ.filter (· < i)) ⊆ Finset.univ.filter (· < j) := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk'
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans (Finset.mem_filter.mp hk').2 hij⟩
    have hnotmem : i ∉ Finset.univ.filter (· < i) := by simp
    have hsum_le := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hlen_nn k)
    rw [Finset.sum_insert hnotmem] at hsum_le
    have hst_le : st i + len i ≤ st j := by simp only [st]; linarith
    linarith [hti.2, htj.1]
  have hy₀_box : IsBoxSched s T S y₀ := by
    refine ⟨fun j => measurable_const.indicator measurableSet_Ico,
      fun j t => by by_cases h : t ∈ Ico (st j) (st j + len j) <;> simp [y₀, h],
      fun j t ht => by
        have hnot : t ∉ Ico (st j) (st j + len j) := fun h => ht (hIco_sub j h)
        simp [y₀, hnot],
      fun j hj t => by
        have hlen0 : len j = 0 := by simp [len, hj]
        simp [y₀, hlen0],
      fun t => ?_⟩
    by_cases hex : ∃ j : Fin m, t ∈ Ico (st j) (st j + len j)
    · rcases hex with ⟨j₀, hj₀⟩
      have hother : ∀ j : Fin m, j ≠ j₀ → y₀ j t = 0 := by
        intro j hne
        have hnot : t ∉ Ico (st j) (st j + len j) := by
          intro hjt
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact Set.disjoint_left.mp (hdisj j j₀ hlt) hjt hj₀
          · exact Set.disjoint_left.mp (hdisj j₀ j hgt) hj₀ hjt
        simp [y₀, hnot]
      rw [Finset.sum_eq_single j₀ (fun j _ hne => hother j hne) (by simp)]
      simp [y₀, hj₀]
    · push Not at hex
      have hzero : ∀ j : Fin m, y₀ j t = 0 := fun j => by simp [y₀, hex j]
      simp [hzero]
  have hy₀_len : ∀ j ∈ S, ρ j < ∫ t in Ico s T, y₀ j t := by
    intro j hj
    have heq : ∫ t in Ico s T, y₀ j t = len j := by
      simp only [y₀]
      rw [setIntegral_indicator measurableSet_Ico, inter_eq_right.mpr (hIco_sub j),
        setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Ico]
      have hnn := hlen_nn j
      rw [add_sub_cancel_left, ENNReal.toReal_ofReal hnn]
    rw [heq]
    simp only [len, hj, ↓reduceIte]
    linarith
  -- Apply geometric Hahn-Banach to U and p₀
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hU_conv hU_open hp₀_not
  let a₀ : Fin m → ℝ := fun j => if h : j ∈ S then f (Pi.single ⟨j, h⟩ 1, 0) else 0
  let γ : ℝ := - f (0, 1)
  have hf_eval : ∀ p : (S → ℝ) × ℝ, f p = (∑ j : S, a₀ j.1 * p.1 j) - γ * p.2 := by
    intro ⟨w, c⟩
    have hdecomp : (w, c) = (∑ j : S, w j • (Pi.single j (1 : ℝ), (0 : ℝ))) + c • ((0 : S → ℝ), (1 : ℝ)) := by
      apply Prod.ext
      · ext i
        simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]
    conv_lhs => rw [hdecomp]
    rw [map_add, map_sum, map_smul, smul_eq_mul]
    simp only [map_smul, smul_eq_mul, a₀, γ]
    have hsum : ∑ j : S, w j * f (Pi.single j 1, 0) =
        ∑ j : S, (if h : j.1 ∈ S then f (Pi.single ⟨j.1, h⟩ 1, 0) else 0) * w j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp [j.2, mul_comm]
    rw [hsum]
    ring
  -- Slater point in U: (ρ|_S, cost(y₀) + 1)
  let c₀ : ℝ := (∑ j ∈ S, ∫ t in Ico s T, I.g j t * y₀ j t) + 1
  have hslater : (fun j : S => ρ j.1, c₀) ∈ U :=
    ⟨y₀, hy₀_box, fun j => hy₀_len j.1 j.2, by simp [c₀]⟩
  have hγ_pos : 0 < γ := by
    have h1 := hf (fun j : S => ρ j.1, c₀) hslater
    rw [hf_eval, hf_eval] at h1
    have h2 : γ * OPT < γ * c₀ := by linarith
    have hγ_nn : 0 ≤ γ := by
      by_contra hlt
      push Not at hlt
      let M : ℝ := (|f (fun j : S => ρ j.1, c₀) - f p₀| + 1) / (-γ)
      have hM_pos : 0 < M := div_pos (by positivity) (by linarith)
      have hmem : (fun j : S => ρ j.1, c₀ + M) ∈ U :=
        ⟨y₀, hy₀_box, fun j => hy₀_len j.1 j.2, by dsimp [c₀]; linarith⟩
      have h3 := hf _ hmem
      rw [hf_eval, hf_eval] at h3
      have hdiff : f (fun j : S => ρ j.1, c₀) - f p₀ =
          (∑ j : S, a₀ j.1 * ρ j.1 - γ * c₀) - (∑ j : S, a₀ j.1 * ρ j.1 - γ * OPT) := by
        rw [hf_eval, hf_eval]
      have hγM : -γ * M = |f (fun j : S => ρ j.1, c₀) - f p₀| + 1 :=
        mul_div_cancel₀ _ (ne_of_gt (by linarith))
      have habs : -(f (fun j : S => ρ j.1, c₀) - f p₀) ≤ |f (fun j : S => ρ j.1, c₀) - f p₀| :=
        neg_le_abs _
      linarith
    rcases eq_or_lt_of_le hγ_nn with h0 | hpos
    · rw [← h0] at h2; simp at h2
    · exact hpos
  have ha₀_nn : ∀ j ∈ S, 0 ≤ a₀ j := by
    intro j hj
    by_contra hlt
    push Not at hlt
    let M : ℝ := (|f (fun i : S => ρ i.1, c₀) - f p₀| + 1) / (-a₀ j)
    have hM_pos : 0 < M := div_pos (by positivity) (by linarith)
    let wM : S → ℝ := fun i => ρ i.1 - M * (if i = ⟨j, hj⟩ then 1 else 0)
    have hmem : (wM, c₀) ∈ U := by
      refine ⟨y₀, hy₀_box, fun i => ?_, by dsimp [c₀]; linarith⟩
      have hsub_le : wM i ≤ ρ i.1 := by
        dsimp [wM]
        split_ifs <;> linarith
      exact lt_of_le_of_lt hsub_le (hy₀_len i.1 i.2)
    have h3 := hf (wM, c₀) hmem
    have hfwM : f (wM, c₀) = f (fun i : S => ρ i.1, c₀) - a₀ j * M := by
      rw [hf_eval, hf_eval]
      have hsum_eq : ∑ i : S, a₀ i.1 * wM i = (∑ i : S, a₀ i.1 * ρ i.1) - a₀ j * M := by
        have hterm : ∀ i : S, a₀ i.1 * wM i =
            a₀ i.1 * ρ i.1 - (if i = ⟨j, hj⟩ then a₀ j * M else 0) := by
          intro i
          by_cases hi : i = ⟨j, hj⟩
          · subst hi; simp [wM]; ring
          · simp [wM, hi]
        rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib]
        simp
      rw [hsum_eq]; ring
    rw [hfwM] at h3
    have haM : -a₀ j * M = |f (fun i : S => ρ i.1, c₀) - f p₀| + 1 :=
      mul_div_cancel₀ _ (ne_of_gt (by linarith))
    have habs : -(f (fun i : S => ρ i.1, c₀) - f p₀) ≤ |f (fun i : S => ρ i.1, c₀) - f p₀| :=
      neg_le_abs _
    linarith
  -- Normalize a := a₀ / γ
  let a : Fin m → ℝ := fun j => a₀ j / γ
  have ha_nn : ∀ j ∈ S, 0 ≤ a j := fun j hj => div_nonneg (ha₀_nn j hj) (le_of_lt hγ_pos)
  have hbox_ineq : ∀ y, IsBoxSched s T S y →
      (∑ j ∈ S, a j * ∫ t in Ico s T, y j t) - (∑ j ∈ S, ∫ t in Ico s T, I.g j t * y j t) ≤
        (∑ j ∈ S, a j * ρ j) - OPT := by
    intro y hy
    have hmul : ∀ ε > 0,
        (∑ j ∈ S, a₀ j * ((∫ t in Ico s T, y j t) - ε)) -
          γ * ((∑ j ∈ S, ∫ t in Ico s T, I.g j t * y j t) + ε) <
        (∑ j ∈ S, a₀ j * ρ j) - γ * OPT := by
      intro ε hε
      have hmem : (fun j : S => (∫ t in Ico s T, y j.1 t) - ε,
          (∑ j ∈ S, ∫ t in Ico s T, I.g j t * y j t) + ε) ∈ U :=
        ⟨y, hy, fun j => by linarith, by linarith⟩
      have hlt := hf _ hmem
      rw [hf_eval, hf_eval] at hlt
      dsimp only [p₀] at hlt
      have hs1 : ∑ j : S, a₀ j.1 * ((∫ t in Ico s T, y j.1 t) - ε) =
          ∑ j ∈ S, a₀ j * ((∫ t in Ico s T, y j t) - ε) :=
        Finset.sum_bij (fun j _ => j.1) (fun j _ => j.2)
          (fun _ _ _ _ h => Subtype.ext h)
          (fun j hj => ⟨⟨j, hj⟩, Finset.mem_univ _, rfl⟩) (fun _ _ => rfl)
      have hs2 : ∑ j : S, a₀ j.1 * ρ j.1 = ∑ j ∈ S, a₀ j * ρ j :=
        Finset.sum_bij (fun j _ => j.1) (fun j _ => j.2)
          (fun _ _ _ _ h => Subtype.ext h)
          (fun j hj => ⟨⟨j, hj⟩, Finset.mem_univ _, rfl⟩) (fun _ _ => rfl)
      rw [hs1, hs2] at hlt
      exact hlt
    have hle0 : (∑ j ∈ S, a₀ j * ∫ t in Ico s T, y j t) -
        γ * (∑ j ∈ S, ∫ t in Ico s T, I.g j t * y j t) ≤
        (∑ j ∈ S, a₀ j * ρ j) - γ * OPT := by
      by_contra hgt
      push Not at hgt
      set K : ℝ := (∑ j ∈ S, a₀ j) + γ
      have hK_pos : 0 < K := by
        have hsnn : 0 ≤ ∑ j ∈ S, a₀ j := Finset.sum_nonneg ha₀_nn
        linarith
      set D : ℝ := ((∑ j ∈ S, a₀ j * ∫ t in Ico s T, y j t) -
          γ * (∑ j ∈ S, ∫ t in Ico s T, I.g j t * y j t)) -
          ((∑ j ∈ S, a₀ j * ρ j) - γ * OPT)
      have hD_pos : 0 < D := sub_pos.mpr hgt
      set ε : ℝ := D / (2 * K)
      have hε_pos : 0 < ε := div_pos hD_pos (by linarith)
      have hlt := hmul ε hε_pos
      have hrew : ∑ j ∈ S, a₀ j * ((∫ t in Ico s T, y j t) - ε) =
          (∑ j ∈ S, a₀ j * ∫ t in Ico s T, y j t) - (∑ j ∈ S, a₀ j) * ε := by
        simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
      rw [hrew] at hlt
      have hKε : K * ε = D / 2 := by
        dsimp [ε]
        have hKne : K ≠ 0 := ne_of_gt hK_pos
        field_simp [hKne]
      dsimp [K, D] at hKε
      linarith
    have hdiv := div_le_div_of_nonneg_right hle0 (le_of_lt hγ_pos)
    have hγne : γ ≠ 0 := ne_of_gt hγ_pos
    have hlhs : ((∑ j ∈ S, a₀ j * ∫ t in Ico s T, y j t) -
        γ * ∑ j ∈ S, ∫ t in Ico s T, I.g j t * y j t) / γ =
        (∑ j ∈ S, a j * ∫ t in Ico s T, y j t) - ∑ j ∈ S, ∫ t in Ico s T, I.g j t * y j t := by
      rw [sub_div, Finset.sum_div, mul_div_cancel_left₀ _ hγne]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => by simp only [a]; ring)
    have hrhs : ((∑ j ∈ S, a₀ j * ρ j) - γ * OPT) / γ = (∑ j ∈ S, a j * ρ j) - OPT := by
      rw [sub_div, Finset.sum_div, mul_div_cancel_left₀ _ hγne]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => by simp only [a]; ring)
    rw [hlhs, hrhs] at hdiv
    exact hdiv
  -- Build pointwise optimal measurable schedule y* on Ico s T
  let β : ℝ → ℝ := canonBeta I.g S a
  have hG_cont : ∀ j ∈ S, ContinuousOn (I.g j) (Ici s) := fun j hj =>
    (jobStanding_continuousOn (hI j)).mono (fun t ht => le_trans (hS j hj) ht)
  have hβ_cont : ContinuousOn β (Ici s) := canonBeta_continuousOn hG_cont a
  let E : Fin m → Set ℝ := fun j =>
    if j ∈ S then
      {t ∈ Ico s T | 0 < a j - I.g j t} ∩
      (⋂ i ∈ S, {t ∈ Ico s T | a i - I.g i t ≤ a j - I.g j t}) ∩
      (⋂ i ∈ S.filter (· < j), {t ∈ Ico s T | a i - I.g i t < a j - I.g j t})
    else ∅
  have hE_meas : ∀ j, MeasurableSet (E j) := by
    intro j
    by_cases hj : j ∈ S
    · simp only [E, hj, ↓reduceIte]
      have hsub : Ico s T ⊆ Ici s := fun t ht => ht.1
      have hc_j : ContinuousOn (fun t => a j - I.g j t) (Ici s) :=
        continuousOn_const.sub (hG_cont j hj)
      refine ((measurableSet_inter_lt_of_continuousOn measurableSet_Ico hsub
        continuousOn_const hc_j).inter ?_).inter ?_
      · refine Finset.measurableSet_biInter S (fun i hi => ?_)
        exact measurableSet_inter_le_of_continuousOn measurableSet_Ico hsub
          (continuousOn_const.sub (hG_cont i hi)) hc_j
      · refine Finset.measurableSet_biInter (S.filter (· < j)) (fun i hi => ?_)
        exact measurableSet_inter_lt_of_continuousOn measurableSet_Ico hsub
          (continuousOn_const.sub (hG_cont i (Finset.mem_filter.mp hi).1)) hc_j
    · simp [E, hj]
  have hE_sub : ∀ j, E j ⊆ Ico s T := by
    intro j t ht
    by_cases hj : j ∈ S
    · simp only [E, hj, ↓reduceIte] at ht
      exact ht.1.1.1
    · simp [E, hj] at ht
  have hE_disj : ∀ i j : Fin m, i ≠ j → Disjoint (E i) (E j) := by
    intro i j hne
    rw [Set.disjoint_left]
    intro t hti htj
    have hiS : i ∈ S := by by_contra h; simp [E, h] at hti
    have hjS : j ∈ S := by by_contra h; simp [E, h] at htj
    simp only [E, hiS, hjS, ↓reduceIte, mem_inter_iff, mem_iInter] at hti htj
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 := (hti.1.2 j hjS).2
      have h2 := (htj.2 i (Finset.mem_filter.mpr ⟨hiS, hlt⟩)).2
      linarith
    · have h1 := (htj.1.2 i hiS).2
      have h2 := (hti.2 j (Finset.mem_filter.mpr ⟨hjS, hgt⟩)).2
      linarith
  let yStar : Fin m → ℝ → ℝ := fun j t => (E j).indicator (fun _ => (1 : ℝ)) t
  have hyStar_box : IsBoxSched s T S yStar := by
    refine ⟨fun j => measurable_const.indicator (hE_meas j),
      fun j t => by by_cases h : t ∈ E j <;> simp [yStar, h],
      fun j t ht => by
        have hnot : t ∉ E j := fun h => ht (hE_sub j h)
        simp [yStar, hnot],
      fun j hj t => by simp [yStar, E, hj],
      fun t => ?_⟩
    by_cases hex : ∃ j : Fin m, t ∈ E j
    · rcases hex with ⟨j₀, hj₀⟩
      rw [Finset.sum_eq_single j₀ (fun j _ hne => by
        have hnot : t ∉ E j := Set.disjoint_left.mp (hE_disj j j₀ hne) |> fun h => fun h' => h h' hj₀
        simp [yStar, hnot]) (by simp)]
      simp [yStar, hj₀]
    · push Not at hex
      have hzero : ∀ j : Fin m, yStar j t = 0 := fun j => by simp [yStar, hex j]
      simp [hzero]
  have hyStar_eq_β : ∀ t ∈ Ico s T, ∑ j ∈ S, (a j - I.g j t) * yStar j t = β t := by
    intro t ht
    by_cases hβ0 : β t = 0
    · rw [hβ0]
      refine Finset.sum_eq_zero (fun j hj => ?_)
      have hle : a j - I.g j t ≤ 0 := by linarith [sub_le_canonBeta I.g S a hj t]
      have hnot : t ∉ E j := by
        simp only [E, hj, ↓reduceIte, mem_inter_iff, mem_ofPred_eq]
        rintro ⟨⟨⟨_, hpos⟩, _⟩, _⟩; linarith
      simp [yStar, hnot]
    · have hβ_pos : 0 < β t := lt_of_le_of_ne (canonBeta_nonneg I.g S a t) (Ne.symm hβ0)
      let Mset : Finset (Fin m) := S.filter (fun j => a j - I.g j t = β t)
      have hM_ne : Mset.Nonempty := by
        rcases canonBeta_eq_zero_or_exists I.g S a t with h0 | ⟨j, hj, hjeq⟩
        · exact absurd h0 hβ0
        · exact ⟨j, Finset.mem_filter.mpr ⟨hj, hjeq.symm⟩⟩
      let j₀ : Fin m := Mset.min' hM_ne
      have hj₀_mem : j₀ ∈ Mset := Finset.min'_mem Mset hM_ne
      have hj₀_S : j₀ ∈ S := (Finset.mem_filter.mp hj₀_mem).1
      have hj₀_eq : a j₀ - I.g j₀ t = β t := (Finset.mem_filter.mp hj₀_mem).2
      have ht_Ej₀ : t ∈ E j₀ := by
        simp only [E, hj₀_S, ↓reduceIte, mem_inter_iff, mem_ofPred_eq, mem_iInter]
        refine ⟨⟨⟨ht, by linarith⟩, fun i hi => ⟨ht, ?_⟩⟩, fun i hi => ⟨ht, ?_⟩⟩
        · rw [hj₀_eq]; exact sub_le_canonBeta I.g S a hi t
        · obtain ⟨hiS, hilt⟩ := Finset.mem_filter.mp hi
          have hle := sub_le_canonBeta I.g S a hiS t
          rw [hj₀_eq]
          refine lt_of_le_of_ne hle (fun heq => ?_)
          have hiM : i ∈ Mset := Finset.mem_filter.mpr ⟨hiS, heq⟩
          have hge := Finset.min'_le Mset i hiM
          exact not_le_of_gt hilt hge
      rw [Finset.sum_eq_single j₀]
      · simp [yStar, ht_Ej₀, hj₀_eq]
      · intro j _ hne
        have hnot : t ∉ E j := fun h => Set.disjoint_left.mp (hE_disj j j₀ hne) h ht_Ej₀
        simp [yStar, hnot]
      · intro hnot; exact absurd hj₀_S hnot
  have hβ_int_Ico : IntegrableOn β (Ico s T) :=
    (hβ_cont.mono (fun t ht => ht.1)).integrableOn_Icc.mono_set Ico_subset_Icc_self
  have hβ_Ico_le : ∫ t in Ico s T, β t ≤ (∑ j ∈ S, a j * ρ j) - OPT := by
    have h1 : ∫ t in Ico s T, β t =
        (∑ j ∈ S, a j * ∫ t in Ico s T, yStar j t) -
        (∑ j ∈ S, ∫ t in Ico s T, I.g j t * yStar j t) := by
      have hcongr : ∫ t in Ico s T, β t =
          ∫ t in Ico s T, ∑ j ∈ S, (a j * yStar j t - I.g j t * yStar j t) := by
        refine setIntegral_congr_fun measurableSet_Ico (fun t ht => ?_)
        rw [← hyStar_eq_β t ht]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      have hsub_int : ∀ j ∈ S, IntegrableOn (fun t => a j * yStar j t - I.g j t * yStar j t) (Ico s T) :=
        fun j hj => ((boxSched_integrableOn hyStar_box j).const_mul (a j)).sub
          (boxSched_cost_integrableOn hI hS hyStar_box hj)
      rw [hcongr, integral_finsetSum S hsub_int]
      have hterm : ∀ j ∈ S, ∫ t in Ico s T, (a j * yStar j t - I.g j t * yStar j t) =
          a j * (∫ t in Ico s T, yStar j t) - ∫ t in Ico s T, I.g j t * yStar j t := by
        intro j hj
        rw [integral_sub ((boxSched_integrableOn hyStar_box j).const_mul (a j))
          (boxSched_cost_integrableOn hI hS hyStar_box hj), integral_const_mul]
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
    rw [h1]
    exact hbox_ineq yStar hyStar_box
  -- Test against x on Ico s T₀ to get (∑ a_j ρ_j) - OPT ≤ ∫_{Ico s T₀} β
  have hβ_Ico_T₀_ge : (∑ j ∈ S, a j * ρ j) - OPT ≤ ∫ t in Ico s T₀, β t := by
    have hβ_int_T₀ : IntegrableOn β (Ico s T₀) :=
      hβ_int_Ico.mono_set (Ico_subset_Ico_right hT₀T.le)
    have hpt : ∀ t ∈ Ico s T₀, ∑ j ∈ S, (a j * x j t - I.g j t * x j t) ≤ β t := by
      intro t _
      calc ∑ j ∈ S, (a j * x j t - I.g j t * x j t)
          = ∑ j ∈ S, (a j - I.g j t) * x j t := Finset.sum_congr rfl (fun j _ => by ring)
        _ ≤ ∑ j ∈ S, β t * x j t :=
            Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right
              (sub_le_canonBeta I.g S a hj t) (hx_nn j t))
        _ = β t * ∑ j ∈ S, x j t := (Finset.mul_sum S _ _).symm
        _ ≤ β t * 1 := mul_le_mul_of_nonneg_left
            (le_trans (Finset.sum_le_univ_sum_of_nonneg (fun j => hx_nn j t)) (hx_cap t))
            (canonBeta_nonneg I.g S a t)
        _ = β t := mul_one _
    have hx_int_T₀ : ∀ j ∈ S, IntegrableOn (x j) (Ico s T₀) :=
      fun j _ => (hx_int_Icc j).mono_set Ico_subset_Icc_self
    have hgx_int_T₀ : ∀ j ∈ S, IntegrableOn (fun t => I.g j t * x j t) (Ico s T₀) :=
      fun j hj => (hgx_int_Icc j hj).mono_set Ico_subset_Icc_self
    have hsub_int_T₀ : ∀ j ∈ S, IntegrableOn (fun t => a j * x j t - I.g j t * x j t) (Ico s T₀) :=
      fun j hj => ((hx_int_T₀ j hj).const_mul (a j)).sub (hgx_int_T₀ j hj)
    have hint_le : ∫ t in Ico s T₀, (∑ j ∈ S, (a j * x j t - I.g j t * x j t)) ≤
        ∫ t in Ico s T₀, β t :=
      setIntegral_mono_on (integrable_finsetSum S hsub_int_T₀) hβ_int_T₀ measurableSet_Ico hpt
    rw [integral_finsetSum S hsub_int_T₀] at hint_le
    have hlhs_eq : ∑ j ∈ S, ∫ t in Ico s T₀, (a j * x j t - I.g j t * x j t) =
        (∑ j ∈ S, a j * ρ j) - OPT := by
      have hterm : ∀ j ∈ S, ∫ t in Ico s T₀, (a j * x j t - I.g j t * x j t) =
          a j * ρ j - ∫ t in Ici s, I.g j t * x j t := by
        intro j hj
        rw [integral_sub ((hx_int_T₀ j hj).const_mul (a j)) (hgx_int_T₀ j hj),
          integral_const_mul, hx_len_real j hj, hgx_eq_Ico j hj]
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
    rw [hlhs_eq] at hint_le
    exact hint_le
  -- Split Ico s T = Ico s T₀ ∪ Ico T₀ T to show ∫_{Ico T₀ T} β ≤ 0
  have hsplit : ∫ t in Ico s T, β t = (∫ t in Ico s T₀, β t) + ∫ t in Ico T₀ T, β t := by
    have hunion : Ico s T₀ ∪ Ico T₀ T = Ico s T := Ico_union_Ico_eq_Ico hsT₀ hT₀T.le
    have hdisj_T₀ : Disjoint (Ico s T₀) (Ico T₀ T) :=
      Set.disjoint_left.mpr (fun _ h1 h2 => not_lt.mpr h2.1 h1.2)
    rw [← hunion, setIntegral_union hdisj_T₀ measurableSet_Ico
      (hβ_int_Ico.mono_set (Ico_subset_Ico_right hT₀T.le))
      (hβ_int_Ico.mono_set (Ico_subset_Ico_left hsT₀))]
  have htail_le0 : ∫ t in Ico T₀ T, β t ≤ 0 := by linarith
  have hβ_T₀ : β T₀ = 0 :=
    continuousOn_Ici_eq_zero_of_nonneg_of_integral_Ico_le_zero hsT₀ hT₀T hβ_cont
      (fun t _ => canonBeta_nonneg I.g S a t) htail_le0
  -- Monotonicity of g_j implies β(t) = 0 for all t ≥ T₀
  have hβ_zero_after : ∀ t, T₀ ≤ t → β t = 0 := by
    intro t ht
    apply le_antisymm _ (canonBeta_nonneg I.g S a t)
    apply canonBeta_le I.g S a le_rfl
    intro j hj
    have hle1 : a j - I.g j T₀ ≤ 0 := by
      linarith [sub_le_canonBeta I.g S a hj T₀]
    have hmono : I.g j T₀ ≤ I.g j t :=
      (hI j).2.2.2.1 (le_trans (hS j hj) hsT₀) (le_trans (hS j hj) (le_trans hsT₀ ht)) ht
    linarith
  have hβ_int_Ici : IntegrableOn β (Ici s) := by
    have heq : (Icc s T₀).indicator β = (Ici s).indicator β := by
      ext t
      by_cases ht : t ∈ Ici s
      · by_cases hle : t ≤ T₀
        · simp [ht, hle, mem_Icc, mem_Ici.mp ht]
        · simp [ht, hle, mem_Icc, hβ_zero_after t (le_of_lt (not_le.mp hle))]
      · have hnot : t ∉ Icc s T₀ := fun h => ht h.1
        simp [ht, hnot]
    have hi : Integrable ((Icc s T₀).indicator β) :=
      (integrable_indicator_iff measurableSet_Icc).mpr
        ((hβ_cont.mono (fun t ht => ht.1)).integrableOn_Icc)
    rw [heq] at hi
    exact (integrable_indicator_iff measurableSet_Ici).mp hi
  have hβ_int_eq : ∫ t in Ici s, β t = ∫ t in Ico s T₀, β t := by
    have h1 : ∫ t in Ici s, β t = ∫ t in Icc s T₀, β t := by
      rw [← integral_indicator measurableSet_Ici, ← integral_indicator measurableSet_Icc]
      congr 1; ext t
      by_cases ht : t ∈ Ici s
      · by_cases hle : t ≤ T₀
        · simp [ht, hle, mem_Icc, mem_Ici.mp ht]
        · simp [ht, hle, mem_Icc, hβ_zero_after t (le_of_lt (not_le.mp hle))]
      · have hnot : t ∉ Icc s T₀ := fun h => ht h.1
        simp [ht, hnot]
    rw [h1]
    exact (setIntegral_congr_set Ico_ae_eq_Icc).symm
  have htail_ge0 : 0 ≤ ∫ t in Ico T₀ T, β t :=
    setIntegral_nonneg measurableSet_Ico (fun t _ => canonBeta_nonneg I.g S a t)
  refine ⟨a, β, ⟨hβ_int_Ici, ha_nn, Filter.Eventually.of_forall (fun t _ => canonBeta_nonneg I.g S a t),
    fun j hj => Filter.Eventually.of_forall (fun t _ => by linarith [sub_le_canonBeta I.g S a hj t])⟩, ?_⟩
  unfold offDualObj
  rw [hβ_int_eq]
  linarith

/-! ### Section 4: `IsAlg2Run` invariants and time-restriction optimality -/

private structure Alg2Inv {n : ℕ} (I : Instance n) (X : ℕ → Fin n → ℝ → ℝ) (m : ℕ) : Prop where
  meas : ∀ j, Measurable (X m j)
  bin : ∀ j t, X m j t = 0 ∨ X m j t = 1
  unseen : ∀ j : Fin n, m ≤ j.val → ∀ t, X m j t = 0
  bef : ∀ j t, t < I.r j → X m j t = 0
  fin : ∃ T : ℝ, ∀ j t, T < t → X m j t = 0
  cap : ∀ t, ∑ j, X m j t ≤ 1
  total : ∀ j : Fin n, j.val < m → ∫ t, X m j t = I.v j

private lemma alg2Inv_nn {n : ℕ} {I : Instance n} {X : ℕ → Fin n → ℝ → ℝ} {m : ℕ}
    (h : Alg2Inv I X m) (j : Fin n) (t : ℝ) : 0 ≤ X m j t := by
  rcases h.bin j t with h0 | h1 <;> linarith

private lemma alg2Inv_le1 {n : ℕ} {I : Instance n} {X : ℕ → Fin n → ℝ → ℝ} {m : ℕ}
    (h : Alg2Inv I X m) (j : Fin n) (t : ℝ) : X m j t ≤ 1 := by
  rcases h.bin j t with h0 | h1 <;> linarith

private lemma alg2Inv_integrable {n : ℕ} {I : Instance n} (hI : I.Standing)
    {X : ℕ → Fin n → ℝ → ℝ} {m : ℕ} (h : Alg2Inv I X m) (j : Fin n) :
    Integrable (X m j) := by
  rcases h.fin with ⟨T, hT⟩
  have hzero : ∀ t, t ∉ Icc (0 : ℝ) (max 0 T) → X m j t = 0 := by
    intro t ht
    rw [mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with hlt | hgt
    · exact h.bef j t (lt_of_lt_of_le hlt (hI.1 j).2.1)
    · exact hT j t (lt_of_le_of_lt (le_max_right 0 T) hgt)
  have heq : (Icc (0 : ℝ) (max 0 T)).indicator (X m j) = X m j := by
    ext t
    by_cases ht : t ∈ Icc (0 : ℝ) (max 0 T)
    · simp [ht]
    · simp [ht, hzero t ht]
  rw [← heq, integrable_indicator_iff measurableSet_Icc]
  refine (integrableOn_const (C := (1 : ℝ))
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).mono'
    (h.meas j).aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_of_nonneg (alg2Inv_nn h j t)]
  exact alg2Inv_le1 h j t

private lemma alg2_invariants {n : ℕ} {I : Instance n} (hI : I.Standing)
    {X : ℕ → Fin n → ℝ → ℝ} (hX : I.IsAlg2Run X) :
    ∀ m ≤ n, Alg2Inv I X m := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_, ?_, ⟨0, ?_⟩, ?_, ?_⟩
    · intro j; rw [hX.1]; exact measurable_const
    · intro j t; rw [hX.1]; left; rfl
    · intro j _ t; rw [hX.1]; rfl
    · intro j t _; rw [hX.1]; rfl
    · intro j t _; rw [hX.1]; rfl
    · intro t; rw [hX.1]; simp
    · intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ m ih =>
    intro hm
    have hm_lt : m < n := Nat.lt_of_succ_le hm
    let k : Fin n := ⟨m, hm_lt⟩
    have hprev : Alg2Inv I X k.val := ih (Nat.le_of_succ_le hm)
    obtain ⟨hkeep, ⟨⟨hy_meas, hy_bin, hy_bef, hy_out, hy_cap, hy_len, ⟨Ty, hTy⟩⟩, _⟩, _⟩ := hX.2 k
    let y : Fin n → ℝ → ℝ := tailFrom (I.r k) (X (k.val + 1))
    have htail_eq : ∀ j t, I.r k ≤ t → X (k.val + 1) j t = y j t := fun j t ht => by
      simp [y, tailFrom, ht]
    have hsplit_fn : ∀ j, X (k.val + 1) j =
        (Iio (I.r k)).indicator (X k.val j) + (Ici (I.r k)).indicator (y j) := by
      intro j; ext t
      by_cases ht : t < I.r k
      · have hnot : t ∉ Ici (I.r k) := not_le.mpr ht
        simp [ht, hnot, hkeep j t ht]
      · have hge : I.r k ≤ t := not_lt.mp ht
        simp [ht, hge, htail_eq j t hge]
    have hmeas' : ∀ j, Measurable (X (k.val + 1) j) := by
      intro j; rw [hsplit_fn j]
      exact ((hprev.meas j).indicator measurableSet_Iio).add
        ((hy_meas j).indicator measurableSet_Ici)
    have hbin' : ∀ j t, X (k.val + 1) j t = 0 ∨ X (k.val + 1) j t = 1 := by
      intro j t
      by_cases ht : t < I.r k
      · rw [hkeep j t ht]; exact hprev.bin j t
      · rw [htail_eq j t (not_lt.mp ht)]; exact hy_bin j t
    have hunseen' : ∀ j : Fin n, k.val + 1 ≤ j.val → ∀ t, X (k.val + 1) j t = 0 := by
      intro j hj t
      by_cases ht : t < I.r k
      · rw [hkeep j t ht]; exact hprev.unseen j (Nat.le_of_succ_le hj) t
      · rw [htail_eq j t (not_lt.mp ht)]
        have hnot : j ∉ insert k (I.aliveOld (X k.val) k) := by
          intro hmem
          rcases Finset.mem_insert.mp hmem with rfl | hmem'
          · omega
          · have hlt : j < k := (Finset.mem_filter.mp hmem').2.1
            exact absurd hlt (not_lt.mpr (Nat.le_of_succ_le hj))
        exact hy_out j hnot t
    have hbef' : ∀ j t, t < I.r j → X (k.val + 1) j t = 0 := by
      intro j t ht
      by_cases htk : t < I.r k
      · rw [hkeep j t htk]; exact hprev.bef j t ht
      · have hge : I.r k ≤ t := not_lt.mp htk
        have hlt_r : I.r k < I.r j := lt_of_le_of_lt hge ht
        have hkj : k < j := by
          by_contra hle
          exact not_lt.mpr (hI.2 (not_lt.mp hle)) hlt_r
        exact hunseen' j hkj t
    have hfin' : ∃ T : ℝ, ∀ j t, T < t → X (k.val + 1) j t = 0 := by
      rcases hprev.fin with ⟨Tp, hTp⟩
      refine ⟨max (max Tp Ty) (I.r k), fun j t ht => ?_⟩
      have hge : I.r k ≤ t := le_of_lt (lt_of_le_of_lt (le_max_right _ _) ht)
      rw [htail_eq j t hge]
      exact hTy j t (lt_of_le_of_lt (le_trans (le_max_right Tp Ty) (le_max_left _ _)) ht)
    have hcap' : ∀ t, ∑ j, X (k.val + 1) j t ≤ 1 := by
      intro t
      by_cases ht : t < I.r k
      · simp_rw [hkeep _ t ht]; exact hprev.cap t
      · simp_rw [htail_eq _ t (not_lt.mp ht)]; exact hy_cap t
    -- Exact total processing for seen jobs j.val < k.val + 1
    have hprev_int : ∀ j, Integrable (X k.val j) := alg2Inv_integrable hI hprev
    have hy_nn : ∀ j t, 0 ≤ y j t := fun j t => by rcases hy_bin j t with h | h <;> linarith
    have hy_le1 : ∀ j t, y j t ≤ 1 := fun j t => by rcases hy_bin j t with h | h <;> linarith
    have hy_int : ∀ j, Integrable (y j) := by
      intro j
      have hzero : ∀ t, t ∉ Icc (I.r k) (max (I.r k) Ty) → y j t = 0 := by
        intro t ht
        rw [mem_Icc, not_and_or, not_le, not_le] at ht
        rcases ht with hlt | hgt
        · exact hy_bef j t hlt
        · exact hTy j t (lt_of_le_of_lt (le_max_right _ _) hgt)
      have heq : (Icc (I.r k) (max (I.r k) Ty)).indicator (y j) = y j := by
        ext t
        by_cases ht : t ∈ Icc (I.r k) (max (I.r k) Ty)
        · simp [ht]
        · simp [ht, hzero t ht]
      rw [← heq, integrable_indicator_iff measurableSet_Icc]
      refine (integrableOn_const (C := (1 : ℝ))
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).mono'
        (hy_meas j).aestronglyMeasurable ?_
      filter_upwards with t
      rw [Real.norm_of_nonneg (hy_nn j t)]
      exact hy_le1 j t
    have htotal' : ∀ j : Fin n, j.val < k.val + 1 → ∫ t, X (k.val + 1) j t = I.v j := by
      intro j hj
      have hsplit_int : ∫ t, X (k.val + 1) j t =
          (∫ t in Iio (I.r k), X k.val j t) + ∫ t, y j t := by
        have h1 : ∫ t, X (k.val + 1) j t =
            (∫ t, (Iio (I.r k)).indicator (X k.val j) t) +
            ∫ t, (Ici (I.r k)).indicator (y j) t := by
          rw [hsplit_fn j]
          exact integral_add ((hprev_int j).indicator measurableSet_Iio)
            ((hy_int j).indicator measurableSet_Ici)
        rw [h1, integral_indicator measurableSet_Iio]
        congr 1
        have heq_y : (Ici (I.r k)).indicator (y j) = y j := by
          ext t
          by_cases ht : I.r k ≤ t
          · simp [ht]
          · simp only [mem_Ici, ht, not_false_eq_true, indicator_of_notMem]
            exact (hy_bef j t (not_le.mp ht)).symm
        rw [heq_y]
      rw [hsplit_int]
      have hy_int_eq : ∀ i ∈ insert k (I.aliveOld (X k.val) k),
          0 ≤ I.residual (X k.val) k i → ∫ t, y i t = I.residual (X k.val) k i := by
        intro i hi hres_nn
        have h1 := hy_len i hi
        rw [← ofReal_integral_eq_lintegral_ofReal (hy_int i)
          (Filter.Eventually.of_forall (hy_nn i))] at h1
        exact (ENNReal.ofReal_eq_ofReal_iff
          (integral_nonneg (hy_nn i)) hres_nn).mp h1
      by_cases hjk : j = k
      · subst hjk
        have hXk0 : X k.val k = 0 := funext (hprev.unseen k le_rfl)
        have hresk : I.residual (X k.val) k k = I.v k := by
          simp [Instance.residual, hXk0]
        have h1 : ∫ t in Iio (I.r k), X k.val k t = 0 := by simp [hXk0]
        have h2 : ∫ t, y k t = I.v k := by
          rw [hy_int_eq k (Finset.mem_insert_self _ _) (by rw [hresk]; exact le_of_lt (hI.1 k).1), hresk]
        linarith
      · have hjlt : j < k := lt_of_le_of_ne (Nat.lt_succ_iff.mp hj) hjk
        by_cases halive : j ∈ I.aliveOld (X k.val) k
        · have hres_pos : 0 < I.residual (X k.val) k j := (Finset.mem_filter.mp halive).2.2
          have h2 := hy_int_eq j (Finset.mem_insert_of_mem halive) (le_of_lt hres_pos)
          rw [h2]
          unfold Instance.residual
          ring
        · have hres_le0 : I.residual (X k.val) k j ≤ 0 := by
            by_contra hpos
            push Not at hpos
            exact halive (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjlt, hpos⟩)
          have hge_v : I.v j ≤ ∫ t in Iio (I.r k), X k.val j t := by
            unfold Instance.residual at hres_le0; linarith
          have hle_v : ∫ t in Iio (I.r k), X k.val j t ≤ I.v j := by
            rw [← hprev.total j hjlt]
            exact setIntegral_le_integral (hprev_int j)
              (Filter.Eventually.of_forall (alg2Inv_nn hprev j))
          have hnotS : j ∉ insert k (I.aliveOld (X k.val) k) := by
            intro hmem
            rcases Finset.mem_insert.mp hmem with rfl | hmem'
            · exact hjk rfl
            · exact halive hmem'
          have hy0 : ∫ t, y j t = 0 := by simp [y, hy_out j hnotS]
          linarith
    exact ⟨hmeas', hbin', hunseen', hbef', hfin', hcap', htotal'⟩

private lemma step_dual_opt_next {n : ℕ} {I : Instance n} (hI : I.Standing)
    {X : ℕ → Fin n → ℝ → ℝ} (hX : I.IsAlg2Run X)
    {A : Fin n → Fin n → ℝ} {B : Fin n → ℝ → ℝ}
    (hAB : ∀ k : Fin n, IsOffOptDual I.g (I.r k) (insert k (I.aliveOld (X k.val) k))
      (I.residual (X k.val) k) (A k) (B k))
    {k k' : Fin n} (hk' : k'.val = k.val + 1) :
    IsOffOptDual I.g (I.r k') (I.aliveOld (X k'.val) k') (I.residual (X k'.val) k') (A k) (B k) := by
  have hk_lt_k' : k < k' := by
    change k.val < k'.val; omega
  have hr_le : I.r k ≤ I.r k' := hI.2 hk_lt_k'.le
  have hinv_k : Alg2Inv I X k.val := alg2_invariants hI hX k.val (le_of_lt k.isLt)
  have hinv_k' : Alg2Inv I X k'.val := alg2_invariants hI hX k'.val (le_of_lt k'.isLt)
  have hinv_int : ∀ j, Integrable (X k'.val j) := alg2Inv_integrable hI hinv_k'
  let Sk : Finset (Fin n) := insert k (I.aliveOld (X k.val) k)
  let Ak' : Finset (Fin n) := I.aliveOld (X k'.val) k'
  let ρk : Fin n → ℝ := I.residual (X k.val) k
  let ρk' : Fin n → ℝ := I.residual (X k'.val) k'
  let y : Fin n → ℝ → ℝ := tailFrom (I.r k) (X (k.val + 1))
  have hy_eq : ∀ j t, I.r k ≤ t → y j t = X k'.val j t := fun j t ht => by
    simp [y, tailFrom, ht, hk']
  -- Step 1: Ak' ⊆ Sk
  have hAk'_sub : Ak' ⊆ Sk := by
    intro j hj
    obtain ⟨_, hjlt, hres_pos⟩ := Finset.mem_filter.mp hj
    by_cases hjk : j = k
    · subst hjk; exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ j, lt_of_le_of_ne (by omega) hjk, ?_⟩
      have hkeep_k := (hX.2 k).1
      have hIio_eq : ∫ t in Iio (I.r k), X k.val j t = ∫ t in Iio (I.r k), X k'.val j t := by
        refine setIntegral_congr_fun measurableSet_Iio (fun t ht => ?_)
        rw [hk', hkeep_k j t ht]
      have hIio_le : ∫ t in Iio (I.r k), X k'.val j t ≤ ∫ t in Iio (I.r k'), X k'.val j t :=
        setIntegral_mono_set (hinv_int j).integrableOn
          (Filter.Eventually.of_forall (alg2Inv_nn hinv_k' j))
          (Iio_subset_Iio hr_le).eventuallyLE
      unfold Instance.residual at hres_pos ⊢
      linarith
  -- Step 2: Check hypotheses for strong duality at r_k
  have hSk_r : ∀ j ∈ Sk, I.r j ≤ I.r k := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj'
    · exact le_rfl
    · exact hI.2 (le_of_lt (Finset.mem_filter.mp hj').2.1)
  have hSk_ρ : ∀ j ∈ Sk, 0 < ρk j := by
    intro j hj
    rcases Finset.mem_insert.mp hj with hjk | hj'
    · rw [hjk]
      have hXk0 : X k.val k = 0 := funext (hinv_k.unseen k le_rfl)
      have : ρk k = I.v k := by simp [ρk, Instance.residual, hXk0]
      rw [this]; exact (hI.1 k).1
    · exact (Finset.mem_filter.mp hj').2.2
  have hy_opt : IsOptIntegral I.g (I.r k) Sk ρk y := (hX.2 k).2.1
  -- Strong duality at r_k
  obtain ⟨a_sd, β_sd, hsd_feas, hsd_obj⟩ :=
    strong_duality_of_opt_integral I hI.1 (I.r k) Sk ρk hSk_r hSk_ρ y hy_opt
  -- Integrability of g_j * X k' j on Ici (I.r k)
  rcases hinv_k'.fin with ⟨Tx, hTx⟩
  have hgx_int_Ici : ∀ j ∈ Sk, IntegrableOn (fun t => I.g j t * X k'.val j t) (Ici (I.r k)) := by
    intro j hj
    set M : ℝ := max (I.r k) Tx
    have hg_cont : ContinuousOn (I.g j) (Icc (I.r k) M) :=
      (jobStanding_continuousOn (hI.1 j)).mono (fun t ht => le_trans (hSk_r j hj) ht.1)
    have hint_Icc : IntegrableOn (fun t => I.g j t * X k'.val j t) (Icc (I.r k) M) := by
      refine hg_cont.integrableOn_Icc.mono'
        ((hg_cont.aestronglyMeasurable measurableSet_Icc).mul
          (hinv_k'.meas j).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have hgnn : 0 ≤ I.g j t := (hI.1 j).2.2.1 t (le_trans (hSk_r j hj) ht.1)
      rw [Real.norm_of_nonneg (mul_nonneg hgnn (alg2Inv_nn hinv_k' j t))]
      calc I.g j t * X k'.val j t ≤ I.g j t * 1 :=
            mul_le_mul_of_nonneg_left (alg2Inv_le1 hinv_k' j t) hgnn
        _ = I.g j t := mul_one _
    have heq : (Icc (I.r k) M).indicator (fun t => I.g j t * X k'.val j t) =
        (Ici (I.r k)).indicator (fun t => I.g j t * X k'.val j t) := by
      ext t
      by_cases ht : t ∈ Ici (I.r k)
      · by_cases hle : t ≤ M
        · simp [ht, hle, mem_Icc, mem_Ici.mp ht]
        · have hgt : Tx < t := lt_of_le_of_lt (le_max_right _ _) (not_le.mp hle)
          simp [ht, hle, mem_Icc, hTx j t hgt]
      · have hnot : t ∉ Icc (I.r k) M := fun h => ht h.1
        simp [ht, hnot]
    have hi : Integrable ((Icc (I.r k) M).indicator (fun t => I.g j t * X k'.val j t)) :=
      (integrable_indicator_iff measurableSet_Icc).mpr hint_Icc
    rw [heq] at hi
    exact (integrable_indicator_iff measurableSet_Ici).mp hi
  -- Residual identity: for j ∈ Sk, ∫_{Ici (r k)} X k' j = ρk j and ∫_{Ici (r k')} X k' j = ρk' j
  have hX_Ici_k' : ∀ j ∈ Sk, ∫ t in Ici (I.r k'), X k'.val j t = ρk' j := by
    intro j hj
    have hj_lt : j.val < k'.val := by
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · omega
      · have := (Finset.mem_filter.mp hj').2.1
        change j.val < k.val at this
        omega
    have hsplit : ∫ t, X k'.val j t =
        (∫ t in Iio (I.r k'), X k'.val j t) + ∫ t in Ici (I.r k'), X k'.val j t := by
      have hunion : Iio (I.r k') ∪ Ici (I.r k') = univ := Iio_union_Ici
      have hdisj_k' : Disjoint (Iio (I.r k')) (Ici (I.r k')) :=
        Set.disjoint_left.mpr (fun _ h1 h2 => not_lt.mpr (mem_Ici.mp h2) (mem_Iio.mp h1))
      rw [← setIntegral_univ, ← hunion,
        setIntegral_union hdisj_k' measurableSet_Ici
          (hinv_int j).integrableOn (hinv_int j).integrableOn]
    rw [hinv_k'.total j hj_lt] at hsplit
    unfold ρk' Instance.residual
    linarith
  have hX_Ici_k : ∀ j ∈ Sk, ∫ t in Ici (I.r k), X k'.val j t = ρk j := by
    intro j hj
    have hj_lt : j.val < k'.val := by
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · omega
      · have := (Finset.mem_filter.mp hj').2.1
        change j.val < k.val at this
        omega
    have hsplit : ∫ t, X k'.val j t =
        (∫ t in Iio (I.r k), X k'.val j t) + ∫ t in Ici (I.r k), X k'.val j t := by
      have hunion : Iio (I.r k) ∪ Ici (I.r k) = univ := Iio_union_Ici
      have hdisj_k : Disjoint (Iio (I.r k)) (Ici (I.r k)) :=
        Set.disjoint_left.mpr (fun _ h1 h2 => not_lt.mpr (mem_Ici.mp h2) (mem_Iio.mp h1))
      rw [← setIntegral_univ, ← hunion,
        setIntegral_union hdisj_k measurableSet_Ici
          (hinv_int j).integrableOn (hinv_int j).integrableOn]
    have hkeep_k := (hX.2 k).1
    have hIio_eq : ∫ t in Iio (I.r k), X k'.val j t = ∫ t in Iio (I.r k), X k.val j t :=
      setIntegral_congr_fun measurableSet_Iio (fun t ht => by rw [hk', hkeep_k j t ht])
    rw [hinv_k'.total j hj_lt, hIio_eq] at hsplit
    unfold ρk Instance.residual
    linarith
  -- For j ∈ Sk \ Ak', X k' j = 0 a.e. on Ici (r k')
  have hdead_ae : ∀ j ∈ Sk, j ∉ Ak' →
      ∀ᵐ t ∂(volume.restrict (Ici (I.r k'))), X k'.val j t = 0 := by
    intro j hj hjnot
    have hj_lt : j < k' := by
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · exact hk_lt_k'
      · exact lt_trans (Finset.mem_filter.mp hj').2.1 hk_lt_k'
    have hρ_le0 : ρk' j ≤ 0 := by
      by_contra hpos
      push Not at hpos
      exact hjnot (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj_lt, hpos⟩)
    have hint0 : ∫ t in Ici (I.r k'), X k'.val j t = 0 := by
      have hge0 : 0 ≤ ∫ t in Ici (I.r k'), X k'.val j t :=
        setIntegral_nonneg measurableSet_Ici (fun t _ => alg2Inv_nn hinv_k' j t)
      rw [hX_Ici_k' j hj] at hge0 ⊢
      linarith
    exact (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (alg2Inv_nn hinv_k' j))
      (hinv_int j).integrableOn).mp hint0
  have hdead_cost : ∀ j ∈ Sk, j ∉ Ak' → ∫ t in Ici (I.r k'), I.g j t * X k'.val j t = 0 := by
    intro j hj hjnot
    have hae : (fun t => I.g j t * X k'.val j t) =ᵐ[volume.restrict (Ici (I.r k'))] fun _ => (0 : ℝ) := by
      filter_upwards [hdead_ae j hj hjnot] with t ht
      simp [ht]
    rw [integral_congr_ae hae, integral_zero]
  -- Exact equality offDualObj(r_k, Sk, ρk, A k, B k) = ∑_{j ∈ Sk} ∫_{Ici (r k)} g_j * X k' j
  have hcost_y_eq : ∑ j ∈ Sk, ∫ t in Ici (I.r k), I.g j t * y j t =
      ∑ j ∈ Sk, ∫ t in Ici (I.r k), I.g j t * X k'.val j t := by
    refine Finset.sum_congr rfl (fun j _ => setIntegral_congr_fun measurableSet_Ici (fun t ht => ?_))
    rw [hy_eq j t ht]
  have hobj_ge : ∑ j ∈ Sk, ∫ t in Ici (I.r k), I.g j t * X k'.val j t ≤
      offDualObj (I.r k) Sk ρk (A k) (B k) := by
    rw [← hcost_y_eq, ← hsd_obj]
    exact (hAB k).2 a_sd β_sd hsd_feas
  have hobj_le : offDualObj (I.r k) Sk ρk (A k) (B k) ≤
      ∑ j ∈ Sk, ∫ t in Ici (I.r k), I.g j t * X k'.val j t := by
    have hwd := weak_duality_on_set measurableSet_Ici Subset.rfl (hAB k).1
      (fun j _ => (hinv_int j).integrableOn) hgx_int_Ici
      (fun j _ t _ => alg2Inv_nn hinv_k' j t)
      (fun t _ => le_trans (Finset.sum_le_univ_sum_of_nonneg (fun j => alg2Inv_nn hinv_k' j t))
        (hinv_k'.cap t))
    unfold offDualObj
    have hsum : ∑ j ∈ Sk, A k j * ρk j = ∑ j ∈ Sk, A k j * ∫ t in Ici (I.r k), X k'.val j t :=
      Finset.sum_congr rfl (fun j hj => by rw [hX_Ici_k j hj])
    rw [hsum]
    exact hwd
  have hstrong : offDualObj (I.r k) Sk ρk (A k) (B k) =
      ∑ j ∈ Sk, ∫ t in Ici (I.r k), I.g j t * X k'.val j t :=
    le_antisymm hobj_le hobj_ge
  -- Feasibility of (A k, B k) for (I.r k', Ak')
  have hfeas_next : IsOffDualFeas I.g (I.r k') Ak' (A k) (B k) := by
    refine ⟨(hAB k).1.1.mono_set (Ici_subset_Ici.mpr hr_le),
      fun j hj => (hAB k).1.2.1 j (hAk'_sub hj), ?_, ?_⟩
    · filter_upwards [(hAB k).1.2.2.1] with t ht hst
      exact ht (le_trans hr_le hst)
    · intro j hj
      filter_upwards [(hAB k).1.2.2.2 j (hAk'_sub hj)] with t ht hst
      exact ht (le_trans hr_le hst)
  -- Split Ici (r k) = Ico (r k) (r k') ∪ Ici (r k')
  have hunion : Ico (I.r k) (I.r k') ∪ Ici (I.r k') = Ici (I.r k) := Ico_union_Ici_eq_Ici hr_le
  have hdisj : Disjoint (Ico (I.r k) (I.r k')) (Ici (I.r k')) :=
    Set.disjoint_left.mpr (fun _ h1 h2 => not_lt.mpr h2 h1.2)
  have hhead_sub : Ico (I.r k) (I.r k') ⊆ Ici (I.r k) := fun t ht => ht.1
  have htail_sub : Ici (I.r k') ⊆ Ici (I.r k) := Ici_subset_Ici.mpr hr_le
  have hB_split : ∫ t in Ici (I.r k), B k t =
      (∫ t in Ico (I.r k) (I.r k'), B k t) + ∫ t in Ici (I.r k'), B k t := by
    rw [← hunion, setIntegral_union hdisj measurableSet_Ici
      ((hAB k).1.1.mono_set hhead_sub) ((hAB k).1.1.mono_set htail_sub)]
  have ha_split : ∑ j ∈ Sk, A k j * ρk j =
      (∑ j ∈ Sk, A k j * ∫ t in Ico (I.r k) (I.r k'), X k'.val j t) +
      ∑ j ∈ Ak', A k j * ρk' j := by
    have h1 : ∀ j ∈ Sk, A k j * ρk j =
        A k j * (∫ t in Ico (I.r k) (I.r k'), X k'.val j t) +
        A k j * (∫ t in Ici (I.r k'), X k'.val j t) := by
      intro j hj
      rw [← hX_Ici_k j hj, ← hunion,
        setIntegral_union hdisj measurableSet_Ici
          (hinv_int j).integrableOn (hinv_int j).integrableOn, mul_add]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
    congr 1
    have h2 : ∑ j ∈ Sk, A k j * ∫ t in Ici (I.r k'), X k'.val j t =
        ∑ j ∈ Ak', A k j * ∫ t in Ici (I.r k'), X k'.val j t := by
      symm
      refine Finset.sum_subset hAk'_sub (fun j hj hjnot => ?_)
      have h0 : ∫ t in Ici (I.r k'), X k'.val j t = 0 := by
        rw [integral_congr_ae (hdead_ae j hj hjnot), integral_zero]
      rw [h0, mul_zero]
    rw [h2]
    exact Finset.sum_congr rfl (fun j hj => by rw [hX_Ici_k' j (hAk'_sub hj)])
  have hprimal_split : ∑ j ∈ Sk, ∫ t in Ici (I.r k), I.g j t * X k'.val j t =
      (∑ j ∈ Sk, ∫ t in Ico (I.r k) (I.r k'), I.g j t * X k'.val j t) +
      ∑ j ∈ Ak', ∫ t in Ici (I.r k'), I.g j t * X k'.val j t := by
    have h1 : ∀ j ∈ Sk, ∫ t in Ici (I.r k), I.g j t * X k'.val j t =
        (∫ t in Ico (I.r k) (I.r k'), I.g j t * X k'.val j t) +
        ∫ t in Ici (I.r k'), I.g j t * X k'.val j t := by
      intro j hj
      rw [← hunion, setIntegral_union hdisj measurableSet_Ici
        ((hgx_int_Ici j hj).mono_set hhead_sub) ((hgx_int_Ici j hj).mono_set htail_sub)]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
    congr 1
    symm
    exact Finset.sum_subset hAk'_sub (fun j hj hjnot => hdead_cost j hj hjnot)
  have hhead_wd : (∑ j ∈ Sk, A k j * ∫ t in Ico (I.r k) (I.r k'), X k'.val j t) -
      ∫ t in Ico (I.r k) (I.r k'), B k t ≤
      ∑ j ∈ Sk, ∫ t in Ico (I.r k) (I.r k'), I.g j t * X k'.val j t :=
    weak_duality_on_set measurableSet_Ico hhead_sub (hAB k).1
      (fun j _ => (hinv_int j).integrableOn)
      (fun j hj => (hgx_int_Ici j hj).mono_set hhead_sub)
      (fun j _ t _ => alg2Inv_nn hinv_k' j t)
      (fun t _ => le_trans (Finset.sum_le_univ_sum_of_nonneg (fun j => alg2Inv_nn hinv_k' j t))
        (hinv_k'.cap t))
  have htail_wd : ∀ a' β', IsOffDualFeas I.g (I.r k') Ak' a' β' →
      offDualObj (I.r k') Ak' ρk' a' β' ≤
        ∑ j ∈ Ak', ∫ t in Ici (I.r k'), I.g j t * X k'.val j t := by
    intro a' β' hf'
    have hwd := weak_duality_on_set measurableSet_Ici Subset.rfl hf'
      (fun j _ => (hinv_int j).integrableOn)
      (fun j hj => (hgx_int_Ici j (hAk'_sub hj)).mono_set htail_sub)
      (fun j _ t _ => alg2Inv_nn hinv_k' j t)
      (fun t _ => le_trans (Finset.sum_le_univ_sum_of_nonneg (fun j => alg2Inv_nn hinv_k' j t))
        (hinv_k'.cap t))
    unfold offDualObj
    have hsum : ∑ j ∈ Ak', a' j * ρk' j =
        ∑ j ∈ Ak', a' j * ∫ t in Ici (I.r k'), X k'.val j t :=
      Finset.sum_congr rfl (fun j hj => by rw [hX_Ici_k' j (hAk'_sub hj)])
    rw [hsum]
    exact hwd
  have htail_eq : offDualObj (I.r k') Ak' ρk' (A k) (B k) =
      ∑ j ∈ Ak', ∫ t in Ici (I.r k'), I.g j t * X k'.val j t := by
    have hle := htail_wd (A k) (B k) hfeas_next
    unfold offDualObj at hstrong hle ⊢
    linarith
  refine ⟨hfeas_next, fun a' β' hf' => ?_⟩
  rw [htail_eq]
  exact htail_wd a' β' hf'

/-! ### Section 5: Monotonicity of `B` across arrivals and main theorem -/

private lemma B_mono_succ {n : ℕ} {I : Instance n} (hI : I.Standing)
    {X : ℕ → Fin n → ℝ → ℝ} (hX : I.IsAlg2Run X)
    {A : Fin n → Fin n → ℝ} {B : Fin n → ℝ → ℝ}
    (hAB : ∀ k : Fin n, IsOffOptDual I.g (I.r k) (insert k (I.aliveOld (X k.val) k))
      (I.residual (X k.val) k) (A k) (B k))
    {k k' : Fin n} (hk' : k'.val = k.val + 1) :
    ∀ᵐ t, I.r k' ≤ t → B k t ≤ B k' t := by
  have hnotmem : k' ∉ I.aliveOld (X k'.val) k' := by
    intro hmem
    exact lt_irrefl k' (Finset.mem_filter.mp hmem).2.1
  have hG : ∀ j ∈ insert k' (I.aliveOld (X k'.val) k'), ContinuousOn (I.g j) (Ici (I.r k')) := by
    intro j hj
    have hrj : I.r j ≤ I.r k' := by
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · exact le_rfl
      · exact hI.2 (le_of_lt (Finset.mem_filter.mp hj').2.1)
    exact (jobStanding_continuousOn (hI.1 j)).mono (fun t ht => le_trans hrj ht)
  exact lemma_4_aux hnotmem hG (step_dual_opt_next hI hX hAB hk') (hAB k')

private lemma B_mono {n : ℕ} {I : Instance n} (hI : I.Standing)
    {X : ℕ → Fin n → ℝ → ℝ} (hX : I.IsAlg2Run X)
    {A : Fin n → Fin n → ℝ} {B : Fin n → ℝ → ℝ}
    (hAB : ∀ k : Fin n, IsOffOptDual I.g (I.r k) (insert k (I.aliveOld (X k.val) k))
      (I.residual (X k.val) k) (A k) (B k)) :
    ∀ j k : Fin n, j ≤ k → ∀ᵐ t, I.r k ≤ t → B j t ≤ B k t := by
  intro j k hjk
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show j.val ≤ k.val from hjk)
  induction d generalizing k with
  | zero =>
    have heq : k = j := Fin.ext (by omega)
    subst heq
    exact Filter.Eventually.of_forall (fun _ _ => le_rfl)
  | succ d ih =>
    have hm_lt : j.val + d < n := by omega
    let m : Fin n := ⟨j.val + d, hm_lt⟩
    have hjm : j ≤ m := show j.val ≤ j.val + d by omega
    have hmk : k.val = m.val + 1 := by simp [m]; omega
    have hrmk : I.r m ≤ I.r k := hI.2 (show m.val ≤ k.val by omega)
    have h1 := ih m hjm (by simp [m])
    have h2 := B_mono_succ hI hX hAB hmk
    filter_upwards [h1, h2] with t ht1 ht2 hkt
    exact le_trans (ht1 (le_trans hrmk hkt)) (ht2 hkt)

private lemma measurableSet_segment {n : ℕ} (I : Instance n) (k : Fin n) :
    MeasurableSet (I.segment k) := by
  have heq : I.segment k =
      Ici (I.r k) ∩ ⋂ k' ∈ Finset.univ.filter (k < ·), Iio (I.r k') := by
    ext t
    simp [Instance.segment]
  rw [heq]
  exact measurableSet_Ici.inter
    (Finset.measurableSet_biInter _ (fun _ _ => measurableSet_Iio))

private lemma segment_disjoint {n : ℕ} (I : Instance n) {k₁ k₂ : Fin n} (hne : k₁ ≠ k₂) :
    Disjoint (I.segment k₁) (I.segment k₂) := by
  rw [Set.disjoint_left]
  intro t ht1 ht2
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact not_lt.mpr ht2.1 (ht1.2 k₂ hlt)
  · exact not_lt.mpr ht1.1 (ht2.2 k₁ hgt)

private lemma concatDual_eq_on_segment {n : ℕ} (I : Instance n) (B : Fin n → ℝ → ℝ)
    {k : Fin n} {t : ℝ} (ht : t ∈ I.segment k) :
    I.concatDual B t = B k t := by
  unfold Instance.concatDual
  rw [Finset.sum_eq_single k]
  · simp [ht]
  · intro m _ hne
    have hnot : t ∉ I.segment m := fun hm => Set.disjoint_left.mp (segment_disjoint I hne) hm ht
    simp [hnot]
  · intro hnot; exact absurd (Finset.mem_univ k) hnot

private lemma exists_segment_of_le {n : ℕ} (I : Instance n) {j : Fin n} {t : ℝ}
    (ht : I.r j ≤ t) : ∃ k : Fin n, j ≤ k ∧ t ∈ I.segment k := by
  classical
  let K : Finset (Fin n) := Finset.univ.filter (fun k : Fin n => I.r k ≤ t)
  have hjK : j ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ j, ht⟩
  let k : Fin n := K.max' ⟨j, hjK⟩
  have hkK : k ∈ K := Finset.max'_mem K ⟨j, hjK⟩
  refine ⟨k, Finset.le_max' K j hjK, (Finset.mem_filter.mp hkK).2, fun k' hk' => ?_⟩
  by_contra hle
  push Not at hle
  have hk'K : k' ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ k', hle⟩
  exact not_le_of_gt hk' (Finset.le_max' K k' hk'K)

theorem solution {n : ℕ} (I : Instance n) (hI : I.Standing) (X : ℕ → Fin n → ℝ → ℝ)
    (hX : I.IsAlg2Run X) (A : Fin n → Fin n → ℝ) (B : Fin n → ℝ → ℝ)
    (hAB : ∀ k : Fin n, IsOffOptDual I.g (I.r k) (insert k (I.aliveOld (X k.val) k))
      (I.residual (X k.val) k) (A k) (B k)) :
    I.IsDualFeas (fun k => A k k) (I.concatDual B) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 1. IntegrableOn (I.concatDual B) (Ici 0)
    change IntegrableOn (fun t => ∑ k : Fin n, (I.segment k).indicator (B k) t) (Ici 0)
    refine integrable_finsetSum Finset.univ (fun k _ => ?_)
    have hsub1 : I.segment k ⊆ Ici (I.r k) := fun t ht => ht.1
    have hsub2 : Ici (I.r k) ⊆ Ici 0 := Ici_subset_Ici.mpr (hI.1 k).2.1
    have hint_seg : IntegrableOn (B k) (I.segment k) := (hAB k).1.1.mono_set hsub1
    have hint_all : Integrable ((I.segment k).indicator (B k)) :=
      (integrable_indicator_iff (measurableSet_segment I k)).mpr hint_seg
    exact hint_all.integrableOn
  · -- 2. ∀ j, 0 ≤ A j j
    intro j
    exact (hAB j).1.2.1 j (Finset.mem_insert_self j _)
  · -- 3. ∀ᵐ t, 0 ≤ t → 0 ≤ I.concatDual B t
    have hall : ∀ᵐ t, ∀ k : Fin n, I.r k ≤ t → 0 ≤ B k t := by
      rw [ae_all_iff]
      intro k
      exact (hAB k).1.2.2.1
    filter_upwards [hall] with t ht _
    unfold Instance.concatDual
    refine Finset.sum_nonneg (fun k _ => ?_)
    by_cases hmem : t ∈ I.segment k
    · simp only [hmem, indicator_of_mem]
      exact ht k hmem.1
    · simp [hmem]
  · -- 4. ∀ j, ∀ᵐ t, I.r j ≤ t → A j j ≤ I.concatDual B t + I.g j t
    intro j
    have hfeas_j : ∀ᵐ t, I.r j ≤ t → A j j ≤ B j t + I.g j t :=
      (hAB j).1.2.2.2 j (Finset.mem_insert_self j _)
    have hmono_all : ∀ᵐ t, ∀ k : Fin n, j ≤ k → I.r k ≤ t → B j t ≤ B k t := by
      rw [ae_all_iff]
      intro k
      by_cases hjk : j ≤ k
      · filter_upwards [B_mono hI hX hAB j k hjk] with t ht _ hkt
        exact ht hkt
      · exact Filter.Eventually.of_forall (fun _ h => absurd h hjk)
    filter_upwards [hfeas_j, hmono_all] with t hfj hmt hjt
    obtain ⟨k, hjk, hseg⟩ := exists_segment_of_le I hjt
    rw [concatDual_eq_on_segment I B hseg]
    have h1 : A j j ≤ B j t + I.g j t := hfj hjt
    have h2 : B j t ≤ B k t := hmt k hjk hseg.1
    linarith
