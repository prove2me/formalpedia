-- Prove2me | solution 1 for GenCostSched.GFCS.eq_20
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:06:28.435544+00:00
-- url     : https://prove2.me/submissions/04a5cfb1-0e55-4f18-aa05-0c17e54e806c

import Mathlib
import Definitions.Def_GenCostSched_GFCS_Model

open MeasureTheory Set
open scoped ENNReal

namespace GFCSEq20Aux
open GenCostSched.GFCS

/-! ### 1. Basic regularity of `g` and `g'` -/

lemma g_contOn {m : ℕ} (I : Instance m) (j : Fin m) (hj : I.JobStanding j)
    {s : ℝ} (hs : I.r j ≤ s) : ContinuousOn (I.g j) (Ici s) := by
  intro t ht
  exact ((hj.2.2.2.2.2 t (hs.trans ht)).continuousWithinAt).mono (Ici_subset_Ici.2 hs)

lemma gp_nonneg {m : ℕ} (I : Instance m) (j : Fin m) (hj : I.JobStanding j)
    (t : ℝ) (ht : I.r j ≤ t) : 0 ≤ I.g' j t := by
  have hd := hj.2.2.2.2.2 t ht
  have hmono := hj.2.2.2.1
  have := hmono.derivWithin_nonneg (x := t)
  rwa [hd.derivWithin (uniqueDiffOn_Ici _ t (mem_Ici.2 ht))] at this

lemma gp_int {m : ℕ} (I : Instance m) (j : Fin m) (hj : I.JobStanding j)
    (a b : ℝ) (ha : I.r j ≤ a) : IntegrableOn (I.g' j) (Icc a b) := by
  have hd := hj.2.2.2.2.2
  have hcont : ContinuousOn (I.g j) (Icc a b) :=
    (g_contOn I j hj ha).mono Icc_subset_Ici_self
  have h1 : IntegrableOn (I.g' j) (Ioc a b) := by
    apply intervalIntegral.integrableOn_deriv_of_nonneg hcont
    · intro t ht
      exact (hd t (ha.trans ht.1.le)).hasDerivAt (Ici_mem_nhds (lt_of_le_of_lt ha ht.1))
    · intro t ht
      exact gp_nonneg I j hj t (ha.trans ht.1.le)
  exact (integrableOn_Icc_iff_integrableOn_Ioc).2 h1

lemma g_ftc {m : ℕ} (I : Instance m) (j : Fin m) (hj : I.JobStanding j)
    {t T : ℝ} (ht : I.r j ≤ t) (htT : t ≤ T) :
    ∫ τ in Ioc t T, I.g' j τ = I.g j T - I.g j t := by
  rw [← intervalIntegral.integral_of_le htT]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le htT
  · exact (g_contOn I j hj ht).mono Icc_subset_Ici_self
  · intro τ hτ
    exact (hj.2.2.2.2.2 τ (ht.trans hτ.1.le)).hasDerivAt
      (Ici_mem_nhds (lt_of_le_of_lt ht hτ.1))
  · exact ⟨(gp_int I j hj t T ht).mono_set Ioc_subset_Icc_self, by
      rw [Ioc_eq_empty_of_le htT]; exact integrableOn_empty⟩

/-! ### 2. Canonical minimal dual `betaMin` -/

noncomputable def betaMin {m : ℕ} (G : Fin m → ℝ → ℝ) (A : Finset (Fin m))
    (a : Fin m → ℝ) (t : ℝ) : ℝ :=
  if h : A.Nonempty then max 0 (A.sup' h (fun j => a j - G j t)) else 0

lemma betaMin_nonneg {m : ℕ} (G : Fin m → ℝ → ℝ) (A : Finset (Fin m))
    (a : Fin m → ℝ) (t : ℝ) : 0 ≤ betaMin G A a t := by
  unfold betaMin
  split_ifs with h
  · exact le_max_left _ _
  · exact le_rfl

lemma le_betaMin_add {m : ℕ} (G : Fin m → ℝ → ℝ) (A : Finset (Fin m))
    (a : Fin m → ℝ) {j : Fin m} (hj : j ∈ A) (t : ℝ) :
    a j ≤ betaMin G A a t + G j t := by
  unfold betaMin
  have hne : A.Nonempty := ⟨j, hj⟩
  rw [dif_pos hne]
  have h1 : a j - G j t ≤ A.sup' hne (fun k => a k - G k t) :=
    Finset.le_sup' (fun k => a k - G k t) hj
  linarith [le_max_right (0 : ℝ) (A.sup' hne (fun k => a k - G k t))]

lemma betaMin_le {m : ℕ} (G : Fin m → ℝ → ℝ) (A : Finset (Fin m))
    (a : Fin m → ℝ) (t y : ℝ) (hy : 0 ≤ y) (h : ∀ j ∈ A, a j ≤ y + G j t) :
    betaMin G A a t ≤ y := by
  unfold betaMin
  split_ifs with hne
  · apply max_le hy
    rw [Finset.sup'_le_iff]
    intro j hj
    linarith [h j hj]
  · exact hy

lemma betaMin_eq_zero_of_le {m : ℕ} (G : Fin m → ℝ → ℝ) (A : Finset (Fin m))
    (a : Fin m → ℝ) (t : ℝ) (h : ∀ j ∈ A, a j ≤ G j t) :
    betaMin G A a t = 0 := by
  apply le_antisymm _ (betaMin_nonneg G A a t)
  exact betaMin_le G A a t 0 le_rfl (fun j hj => by linarith [h j hj])

lemma continuousOn_finset_sup' {ι : Type*} {s : Set ℝ} {F : Finset ι} (hF : F.Nonempty)
    {φ : ι → ℝ → ℝ} (hφ : ∀ i ∈ F, ContinuousOn (φ i) s) :
    ContinuousOn (fun t => F.sup' hF (fun i => φ i t)) s := by
  induction hF using Finset.Nonempty.cons_induction with
  | singleton i =>
    simpa using hφ i (Finset.mem_singleton_self i)
  | cons i S hi hS ih =>
    have h1 : ContinuousOn (φ i) s := hφ i (Finset.mem_cons_self i S)
    have h2 : ContinuousOn (fun t => S.sup' hS (fun j => φ j t)) s :=
      ih (fun j hj => hφ j (Finset.mem_cons_of_mem hj))
    have heq : (fun t => (Finset.cons i S hi).sup' ⟨i, Finset.mem_cons_self i S⟩ (fun j => φ j t)) =
        fun t => max (φ i t) (S.sup' hS (fun j => φ j t)) := by
      funext t
      exact Finset.sup'_cons (f := fun j => φ j t) hS
    rw [heq]
    exact continuous_max.comp_continuousOn (h1.prodMk h2)

lemma betaMin_continuousOn {m : ℕ} (G : Fin m → ℝ → ℝ) (A : Finset (Fin m))
    (a : Fin m → ℝ) (S : Set ℝ) (hG : ∀ j ∈ A, ContinuousOn (G j) S) :
    ContinuousOn (betaMin G A a) S := by
  unfold betaMin
  by_cases hne : A.Nonempty
  · simp only [dif_pos hne]
    exact continuous_max.comp_continuousOn
      (continuousOn_const.prodMk
        (continuousOn_finset_sup' hne (fun j hj => continuousOn_const.sub (hG j hj))))
  · simp only [dif_neg hne]
    exact continuousOn_const

lemma betaMin_antitoneOn {m : ℕ} (G : Fin m → ℝ → ℝ) (A : Finset (Fin m))
    (a : Fin m → ℝ) (S : Set ℝ) (hG : ∀ j ∈ A, MonotoneOn (G j) S) :
    AntitoneOn (betaMin G A a) S := by
  intro u hu v hv huv
  apply betaMin_le G A a v (betaMin G A a u) (betaMin_nonneg G A a u)
  intro j hj
  have h1 := le_betaMin_add G A a hj u
  have h2 := hG j hj hu hv huv
  linarith

lemma betaMin_sub_le_sum {m : ℕ} (G : Fin m → ℝ → ℝ) (A : Finset (Fin m))
    (a : Fin m → ℝ) (S : Set ℝ) (hG : ∀ j ∈ A, MonotoneOn (G j) S)
    {u v : ℝ} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≤ v) :
    betaMin G A a u - betaMin G A a v ≤ ∑ j ∈ A, (G j v - G j u) := by
  have hsum_nn : ∀ j ∈ A, 0 ≤ G j v - G j u := fun j hj => sub_nonneg.2 (hG j hj hu hv huv)
  unfold betaMin
  by_cases hne : A.Nonempty
  · simp only [dif_pos hne]
    rcases le_total (0 : ℝ) (A.sup' hne (fun j => a j - G j u)) with hpos | hneg
    · rw [max_eq_right hpos]
      obtain ⟨k, hkA, hk⟩ := Finset.exists_mem_eq_sup' hne (fun j => a j - G j u)
      rw [hk]
      have hkv : a k - G k v ≤ max 0 (A.sup' hne (fun j => a j - G j v)) :=
        le_trans (Finset.le_sup' (fun j => a j - G j v) hkA) (le_max_right _ _)
      have hsingle : G k v - G k u ≤ ∑ j ∈ A, (G j v - G j u) :=
        Finset.single_le_sum hsum_nn hkA
      linarith
    · rw [max_eq_left hneg]
      have hv_nn : 0 ≤ max 0 (A.sup' hne (fun j => a j - G j v)) := le_max_left _ _
      have hS_nn : 0 ≤ ∑ j ∈ A, (G j v - G j u) := Finset.sum_nonneg hsum_nn
      linarith
  · simp only [dif_neg hne, sub_self]
    exact Finset.sum_nonneg hsum_nn

/-! ### 3. Bounded-horizon schedules `Y` and Strong Duality -/

def InHorizon {m : ℕ} (s T' : ℝ) (A : Finset (Fin m)) (y : Fin m → ℝ → ℝ) : Prop :=
  (∀ j, Measurable (y j)) ∧ (∀ j t, 0 ≤ y j t) ∧ (∀ j t, t < s → y j t = 0) ∧
  (∀ j t, T' < t → y j t = 0) ∧ (∀ j, j ∉ A → ∀ t, y j t = 0) ∧ (∀ t, ∑ j, y j t ≤ 1)

lemma inHorizon_le_one {m : ℕ} {s T' : ℝ} {A : Finset (Fin m)} {y : Fin m → ℝ → ℝ}
    (hy : InHorizon s T' A y) (j : Fin m) (t : ℝ) : y j t ≤ 1 := by
  calc y j t ≤ ∑ k, y k t := Finset.single_le_sum (fun k _ => hy.2.1 k t) (Finset.mem_univ j)
    _ ≤ 1 := hy.2.2.2.2.2 t

lemma inHorizon_integrableOn {m : ℕ} {s T' : ℝ} {A : Finset (Fin m)} {y : Fin m → ℝ → ℝ}
    (hy : InHorizon s T' A y) (j : Fin m) : IntegrableOn (y j) (Icc s T') := by
  refine Measure.integrableOn_of_bounded (M := 1) (by simp) (hy.1 j).aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (hy.2.1 j t)]
  exact inHorizon_le_one hy j t

lemma inHorizon_integrableOn_g {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j)
    {s T' : ℝ} (_hsT' : s ≤ T') {A : Finset (Fin m)} (hA : ∀ j ∈ A, I.r j ≤ s)
    {y : Fin m → ℝ → ℝ} (hy : InHorizon s T' A y) {j : Fin m} (hj : j ∈ A) :
    IntegrableOn (fun t => I.g j t * y j t) (Icc s T') := by
  have hgc : ContinuousOn (I.g j) (Icc s T') :=
    (g_contOn I j (hI j) (hA j hj)).mono Icc_subset_Ici_self
  have hgm : AEStronglyMeasurable (I.g j) (volume.restrict (Icc s T')) :=
    hgc.aestronglyMeasurable measurableSet_Icc
  refine hgc.integrableOn_Icc.mono' (hgm.mul (hy.1 j).aestronglyMeasurable) ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards with t ht
  have hgnn : 0 ≤ I.g j t := (hI j).2.2.1 t ((hA j hj).trans ht.1)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hgnn (hy.2.1 j t))]
  nlinarith [inHorizon_le_one hy j t, hy.2.1 j t]

lemma inHorizon_lintegral_eq {m : ℕ} {s T' : ℝ} {A : Finset (Fin m)} {y : Fin m → ℝ → ℝ}
    (hy : InHorizon s T' A y) (j : Fin m) :
    ∫⁻ t, ENNReal.ofReal (y j t) = ENNReal.ofReal (∫ t in Icc s T', y j t) := by
  rw [ofReal_integral_eq_lintegral_ofReal (inHorizon_integrableOn hy j)
    (Filter.Eventually.of_forall (fun t => hy.2.1 j t))]
  rw [← lintegral_indicator measurableSet_Icc]
  congr 1; funext t
  by_cases ht : t ∈ Icc s T'
  · rw [indicator_of_mem ht]
  · rw [indicator_of_notMem ht]
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · simp [hy.2.2.1 j t h]
    · simp [hy.2.2.2.1 j t h]

lemma inHorizon_offCost_eq {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j)
    {s T' : ℝ} (hsT' : s ≤ T') {A : Finset (Fin m)} (hA : ∀ j ∈ A, I.r j ≤ s)
    {y : Fin m → ℝ → ℝ} (hy : InHorizon s T' A y) :
    offCost I.g y = ENNReal.ofReal (∑ j ∈ A, ∫ t in Icc s T', I.g j t * y j t) := by
  unfold offCost
  have hsum : ∑ j : Fin m, ∫⁻ t, ENNReal.ofReal (I.g j t * y j t) =
      ∑ j ∈ A, ∫⁻ t, ENNReal.ofReal (I.g j t * y j t) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ A)
    intro j _ hjA
    simp [hy.2.2.2.2.1 j hjA]
  rw [hsum, ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro j hj
    have hnn : ∀ t ∈ Icc s T', 0 ≤ I.g j t * y j t := fun t ht =>
      mul_nonneg ((hI j).2.2.1 t ((hA j hj).trans ht.1)) (hy.2.1 j t)
    rw [ofReal_integral_eq_lintegral_ofReal (inHorizon_integrableOn_g I hI hsT' hA hy hj)
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hnn))]
    rw [← lintegral_indicator measurableSet_Icc]
    congr 1; funext t
    by_cases ht : t ∈ Icc s T'
    · rw [indicator_of_mem ht]
    · rw [indicator_of_notMem ht]
      simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with h | h
      · simp [hy.2.2.1 j t h]
      · simp [hy.2.2.2.1 j t h]
  · intro j hj
    exact setIntegral_nonneg measurableSet_Icc (fun t ht =>
      mul_nonneg ((hI j).2.2.1 t ((hA j hj).trans ht.1)) (hy.2.1 j t))

lemma strong_duality {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (ρ : Fin m → ℝ) (hA : ∀ j ∈ A, I.r j ≤ s) (hρ : ∀ j ∈ A, 0 < ρ j)
    (x : Fin m → ℝ → ℝ) (hx : IsOptIntegral I.g s A ρ x) :
    ∃ a' β', IsOffDualFeas I.g s A a' β' ∧ (offCost I.g x).toReal ≤ offDualObj s A ρ a' β' := by
  obtain ⟨⟨hx1, hx2, hx3, hx4, hx5, hx6, ⟨T0, hT0⟩⟩, hxopt⟩ := hx
  set T : ℝ := max T0 s
  set T' : ℝ := T + 1
  have hsT : s ≤ T := le_max_right _ _
  have hTT' : T < T' := by linarith
  have hsT' : s ≤ T' := le_trans hsT hTT'.le
  have hT : ∀ j t, T < t → x j t = 0 := fun j t ht =>
    hT0 j t (lt_of_le_of_lt (le_max_left _ _) ht)
  have hxnn : ∀ j t, 0 ≤ x j t := fun j t => by
    rcases hx2 j t with h | h <;> linarith
  have hxY : InHorizon s T' A x :=
    ⟨hx1, hxnn, hx3, fun j t ht => hT j t (lt_trans hTT' ht), hx4, hx5⟩
  -- work and cost functionals on InHorizon s T' A
  let work : (Fin m → ℝ → ℝ) → (↑A → ℝ) := fun y j => ∫ t in Icc s T', y j.1 t
  let costR : (Fin m → ℝ → ℝ) → ℝ := fun y => ∑ j ∈ A, ∫ t in Icc s T', I.g j t * y j t
  have hwork_x : ∀ j : ↑A, work x j = ρ j.1 := by
    intro j
    have h1 := hx6 j.1 j.2
    rw [inHorizon_lintegral_eq hxY j.1] at h1
    have hnn : 0 ≤ ∫ t in Icc s T', x j.1 t :=
      setIntegral_nonneg measurableSet_Icc (fun t _ => hxnn j.1 t)
    exact (ENNReal.ofReal_eq_ofReal_iff hnn (hρ j.1 j.2).le).1 h1
  have hcost_x_nn : 0 ≤ costR x := by
    apply Finset.sum_nonneg
    intro j hj
    exact setIntegral_nonneg measurableSet_Icc (fun t ht =>
      mul_nonneg ((hI j).2.2.1 t ((hA j hj).trans ht.1)) (hxnn j t))
  have hcost_x : (offCost I.g x).toReal = costR x := by
    rw [inHorizon_offCost_eq I hI hsT' hA hxY, ENNReal.toReal_ofReal hcost_x_nn]
  -- Open convex epigraph U in (↑A → ℝ) × ℝ
  let U : Set ((↑A → ℝ) × ℝ) :=
    {p | ∃ y, InHorizon s T' A y ∧ (∀ j : ↑A, p.1 j < work y j) ∧ costR y < p.2}
  have hU_open : IsOpen U := by
    have hEq : U = ⋃ (y : Fin m → ℝ → ℝ) (_ : InHorizon s T' A y),
        (⋂ j : ↑A, {p : (↑A → ℝ) × ℝ | p.1 j < work y j}) ∩
          {p : (↑A → ℝ) × ℝ | costR y < p.2} := by
      ext p
      simp only [U, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_iInter]
      constructor
      · rintro ⟨y, hy, h1, h2⟩; exact ⟨y, hy, h1, h2⟩
      · rintro ⟨y, hy, h1, h2⟩; exact ⟨y, hy, h1, h2⟩
    rw [hEq]
    refine isOpen_biUnion (fun y _ => ?_)
    refine IsOpen.inter ?_ (isOpen_lt continuous_const continuous_snd)
    exact isOpen_iInter_of_finite (fun j =>
      isOpen_lt ((continuous_apply j).comp continuous_fst) continuous_const)
  have hU_conv : Convex ℝ U := by
    rintro ⟨v₁, c₁⟩ ⟨y₁, hy₁, hv₁, hc₁⟩ ⟨v₂, c₂⟩ ⟨y₂, hy₂, hv₂, hc₂⟩ t₁ t₂ ht₁ ht₂ hsum
    let y : Fin m → ℝ → ℝ := fun j t => t₁ * y₁ j t + t₂ * y₂ j t
    have hy : InHorizon s T' A y := by
      refine ⟨fun j => ((hy₁.1 j).const_mul t₁).add ((hy₂.1 j).const_mul t₂),
        fun j t => add_nonneg (mul_nonneg ht₁ (hy₁.2.1 j t)) (mul_nonneg ht₂ (hy₂.2.1 j t)),
        fun j t ht => by simp [y, hy₁.2.2.1 j t ht, hy₂.2.2.1 j t ht],
        fun j t ht => by simp [y, hy₁.2.2.2.1 j t ht, hy₂.2.2.2.1 j t ht],
        fun j hj t => by simp [y, hy₁.2.2.2.2.1 j hj t, hy₂.2.2.2.2.1 j hj t],
        fun t => ?_⟩
      simp only [y, Finset.sum_add_distrib, ← Finset.mul_sum]
      nlinarith [hy₁.2.2.2.2.2 t, hy₂.2.2.2.2.2 t]
    refine ⟨y, hy, fun j => ?_, ?_⟩
    · have hwy : work y j = t₁ * work y₁ j + t₂ * work y₂ j := by
        show ∫ t in Icc s T', (t₁ * y₁ j.1 t + t₂ * y₂ j.1 t) = _
        rw [integral_add ((inHorizon_integrableOn hy₁ j.1).const_mul t₁)
          ((inHorizon_integrableOn hy₂ j.1).const_mul t₂),
          integral_const_mul, integral_const_mul]
      rw [hwy]
      change t₁ * v₁ j + t₂ * v₂ j < t₁ * work y₁ j + t₂ * work y₂ j
      have h1 := hv₁ j
      have h2 := hv₂ j
      by_cases ht1 : t₁ = 0
      · subst ht1; simp at hsum; subst hsum; simpa using h2
      · have ht1pos : 0 < t₁ := lt_of_le_of_ne ht₁ (Ne.symm ht1)
        nlinarith
    · have hcy : costR y = t₁ * costR y₁ + t₂ * costR y₂ := by
        show ∑ j ∈ A, ∫ t in Icc s T', I.g j t * (t₁ * y₁ j t + t₂ * y₂ j t) = _
        have hstep : ∀ j ∈ A, ∫ t in Icc s T', I.g j t * (t₁ * y₁ j t + t₂ * y₂ j t) =
            t₁ * (∫ t in Icc s T', I.g j t * y₁ j t) +
            t₂ * (∫ t in Icc s T', I.g j t * y₂ j t) := by
          intro j hj
          have heq : (fun t => I.g j t * (t₁ * y₁ j t + t₂ * y₂ j t)) =
              fun t => t₁ * (I.g j t * y₁ j t) + t₂ * (I.g j t * y₂ j t) := by
            funext t; ring
          rw [heq, integral_add ((inHorizon_integrableOn_g I hI hsT' hA hy₁ hj).const_mul t₁)
            ((inHorizon_integrableOn_g I hI hsT' hA hy₂ hj).const_mul t₂),
            integral_const_mul, integral_const_mul]
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [hcy]
      change t₁ * costR y₁ + t₂ * costR y₂ < t₁ * c₁ + t₂ * c₂
      by_cases ht1 : t₁ = 0
      · subst ht1; simp at hsum; subst hsum; simpa using hc₂
      · have ht1pos : 0 < t₁ := lt_of_le_of_ne ht₁ (Ne.symm ht1)
        nlinarith
  let p0 : (↑A → ℝ) × ℝ := (fun j : ↑A => ρ j.1, costR x)
  have hp0 : p0 ∉ U := by
    rintro ⟨y, hy, hwy, hcy⟩
    have hy_feas : IsOffFracSched s A ρ y := by
      refine ⟨hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2, fun j hj => ?_⟩
      rw [inHorizon_lintegral_eq hy j]
      exact ENNReal.ofReal_le_ofReal (hwy ⟨j, hj⟩).le
    have hle := hxopt y hy_feas
    rw [inHorizon_offCost_eq I hI hsT' hA hxY, inHorizon_offCost_eq I hI hsT' hA hy] at hle
    have hcy_nn : 0 ≤ costR y := by
      apply Finset.sum_nonneg
      intro j hj
      exact setIntegral_nonneg measurableSet_Icc (fun t ht =>
        mul_nonneg ((hI j).2.2.1 t ((hA j hj).trans ht.1)) (hy.2.1 j t))
    have := (ENNReal.ofReal_le_ofReal_iff hcy_nn).1 hle
    linarith
  -- Apply geometric Hahn-Banach separation
  obtain ⟨L, hL⟩ := geometric_hahn_banach_point_open hU_conv hU_open hp0
  let α : ↑A → ℝ := fun j => -L (Pi.single j 1, 0)
  let γ : ℝ := L (0, 1)
  have hL_eval : ∀ (v : ↑A → ℝ) (c : ℝ), L (v, c) = -∑ j : ↑A, α j * v j + γ * c := by
    intro v c
    have hv : (v, c) = (∑ j : ↑A, v j • (Pi.single j (1 : ℝ), (0 : ℝ))) + c • ((0 : ↑A → ℝ), (1 : ℝ)) := by
      apply Prod.ext
      · funext k
        simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, smul_zero, add_zero,
          Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      · simp [Prod.snd_sum]
    conv_lhs => rw [hv]
    rw [map_add, map_sum]
    simp only [map_smul, smul_eq_mul]
    have hsum_eq : ∑ j : ↑A, v j * L (Pi.single j 1, 0) = -∑ j : ↑A, α j * v j := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [α]; ring
    rw [hsum_eq]
    dsimp [γ]; ring
  have hL_le : ∀ y, InHorizon s T' A y → ∀ (v : ↑A → ℝ), (∀ j, v j ≤ work y j) →
      ∀ c, costR y ≤ c → L p0 ≤ L (v, c) := by
    intro y hy v hv c hc
    apply le_of_forall_pos_le_add
    intro δ hδ
    set K : ℝ := |∑ j : ↑A, α j| + |γ| + 1
    have hKpos : 0 < K := by positivity
    set ε : ℝ := δ / K
    have hεpos : 0 < ε := div_pos hδ hKpos
    have hmem : (fun j => v j - ε, c + ε) ∈ U :=
      ⟨y, hy, fun j => by linarith [hv j], by linarith⟩
    have hlt := hL _ hmem
    rw [hL_eval (fun j => v j - ε) (c + ε)] at hlt
    rw [hL_eval v c]
    have hexpand : -∑ j : ↑A, α j * (v j - ε) + γ * (c + ε) =
        (-∑ j : ↑A, α j * v j + γ * c) + ε * (∑ j : ↑A, α j + γ) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    rw [hexpand] at hlt
    have hbd : ∑ j : ↑A, α j + γ ≤ K := by
      have h1 : ∑ j : ↑A, α j ≤ |∑ j : ↑A, α j| := le_abs_self _
      have h2 : γ ≤ |γ| := le_abs_self _
      change ∑ j : ↑A, α j + γ ≤ |∑ j : ↑A, α j| + |γ| + 1
      linarith
    have hmul : ε * (∑ j : ↑A, α j + γ) ≤ δ := by
      calc ε * (∑ j : ↑A, α j + γ) ≤ ε * K := mul_le_mul_of_nonneg_left hbd hεpos.le
        _ = δ := div_mul_cancel₀ δ hKpos.ne'
    linarith
  -- Signs: γ ≥ 0, α j ≥ 0, and γ > 0 via Slater point
  have hγ_nn : 0 ≤ γ := by
    have h1 := hL_le x hxY (fun j : ↑A => ρ j.1) (fun j => (hwork_x j).ge) (costR x + 1) (by linarith)
    change L (fun j : ↑A => ρ j.1, costR x) ≤ L (fun j : ↑A => ρ j.1, costR x + 1) at h1
    rw [hL_eval, hL_eval] at h1
    linarith
  have hα_nn : ∀ j : ↑A, 0 ≤ α j := by
    intro j₀
    let v : ↑A → ℝ := fun j => if j = j₀ then ρ j.1 - 1 else ρ j.1
    have hv : ∀ j, v j ≤ work x j := fun j => by
      rw [hwork_x j]; dsimp [v]; split_ifs <;> linarith
    have h1 := hL_le x hxY v hv (costR x) le_rfl
    change L (fun j : ↑A => ρ j.1, costR x) ≤ L (v, costR x) at h1
    rw [hL_eval, hL_eval] at h1
    have hdiff : ∑ j : ↑A, α j * v j = (∑ j : ↑A, α j * ρ j.1) - α j₀ := by
      have : ∀ j : ↑A, α j * v j = α j * ρ j.1 - (if j = j₀ then α j₀ else 0) := by
        intro j; dsimp [v]; split_ifs with h <;> [subst h; skip] <;> ring
      simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [hdiff] at h1
    linarith
  have hγ_pos : 0 < γ := by
    by_contra hle
    have hγ0 : γ = 0 := le_antisymm (not_lt.1 hle) hγ_nn
    set rate : ℝ := 1 / ((A.card : ℝ) + 1)
    have hcard_pos : (0 : ℝ) < (A.card : ℝ) + 1 :=
      add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) one_pos
    have hrate_pos : 0 < rate := div_pos one_pos hcard_pos
    let yS : Fin m → ℝ → ℝ := fun j t =>
      x j t + if j ∈ A then (Ioc T T').indicator (fun _ => rate) t else 0
    have hyS : InHorizon s T' A yS := by
      refine ⟨fun j => ?_, fun j t => ?_, fun j t ht => ?_, fun j t ht => ?_,
        fun j hj t => ?_, fun t => ?_⟩
      · dsimp [yS]
        split_ifs
        · exact hx1 j |>.add (measurable_const.indicator measurableSet_Ioc)
        · exact hx1 j |>.add measurable_const
      · dsimp [yS]
        apply add_nonneg (hxnn j t)
        split_ifs
        · exact indicator_nonneg (fun _ _ => hrate_pos.le) t
        · exact le_rfl
      · dsimp [yS]
        rw [hx3 j t ht, zero_add]
        split_ifs
        · exact indicator_of_notMem (fun h => absurd h.1 (not_lt.2 (le_trans ht.le hsT))) _
        · rfl
      · dsimp [yS]
        rw [hT j t (lt_trans hTT' ht), zero_add]
        split_ifs
        · exact indicator_of_notMem (fun h => absurd h.2 (not_le.2 ht)) _
        · rfl
      · simp [yS, hx4 j hj t, hj]
      · by_cases ht : t ∈ Ioc T T'
        · have hx0 : ∀ j, x j t = 0 := fun j => hT j t ht.1
          have hsum_eq : ∑ j : Fin m, yS j t = ∑ j ∈ A, rate := by
            simp only [yS, hx0, zero_add, indicator_of_mem ht]
            rw [Finset.sum_ite_mem, Finset.univ_inter]
          rw [hsum_eq, Finset.sum_const, nsmul_eq_mul]
          dsimp [rate]
          rw [mul_one_div, div_le_one hcard_pos]
          linarith
        · have hsum_eq : ∑ j : Fin m, yS j t = ∑ j : Fin m, x j t := by
            apply Finset.sum_congr rfl
            intro j _
            dsimp [yS]
            split_ifs
            · rw [indicator_of_notMem ht, add_zero]
            · rw [add_zero]
          rw [hsum_eq]; exact hx5 t
    have hwork_yS : ∀ j : ↑A, work yS j = ρ j.1 + rate := by
      intro j
      show ∫ t in Icc s T', (x j.1 t + if j.1 ∈ A then (Ioc T T').indicator (fun _ => rate) t else 0) = _
      simp only [j.2, ↓reduceIte]
      have hint_ind : IntegrableOn ((Ioc T T').indicator (fun _ => rate)) (Icc s T') :=
        (integrableOn_const (by simp)).indicator measurableSet_Ioc
      rw [integral_add (inHorizon_integrableOn hxY j.1) hint_ind]
      rw [show ∫ t in Icc s T', x j.1 t = ρ j.1 from hwork_x j]
      rw [setIntegral_indicator measurableSet_Ioc]
      have hinter : Icc s T' ∩ Ioc T T' = Ioc T T' :=
        inter_eq_right.2 (fun t ht => ⟨le_trans hsT ht.1.le, ht.2⟩)
      rw [hinter, setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hTT'.le]
      have : T' - T = 1 := by dsimp [T']; ring
      rw [this, one_mul]
    have hmem : (fun j : ↑A => ρ j.1 + rate / 2, costR yS + 1) ∈ U :=
      ⟨yS, hyS, fun j => by rw [hwork_yS j]; linarith, by linarith⟩
    have hlt := hL _ hmem
    change L (fun j : ↑A => ρ j.1, costR x) < L (fun j : ↑A => ρ j.1 + rate / 2, costR yS + 1) at hlt
    rw [hL_eval, hL_eval, hγ0] at hlt
    have hexp : ∑ j : ↑A, α j * (ρ j.1 + rate / 2) =
        (∑ j : ↑A, α j * ρ j.1) + (rate / 2) * ∑ j : ↑A, α j := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1; apply Finset.sum_congr rfl; intro j _; ring
    rw [hexp] at hlt
    have hsum_nn : 0 ≤ ∑ j : ↑A, α j := Finset.sum_nonneg (fun j _ => hα_nn j)
    nlinarith
  -- Normalize a* := α / γ
  let a' : Fin m → ℝ := fun j => if hj : j ∈ A then α ⟨j, hj⟩ / γ else 0
  have ha'_nn : ∀ j ∈ A, 0 ≤ a' j := fun j hj => by
    simp only [a', dif_pos hj]
    exact div_nonneg (hα_nn ⟨j, hj⟩) hγ_pos.le
  have hmain : ∀ y, InHorizon s T' A y →
      costR x ≤ ∑ j ∈ A, a' j * ρ j - ∑ j ∈ A, ∫ t in Icc s T', (a' j - I.g j t) * y j t := by
    intro y hy
    have h1 := hL_le y hy (work y) (fun _ => le_rfl) (costR y) le_rfl
    change L (fun j : ↑A => ρ j.1, costR x) ≤ L (work y, costR y) at h1
    rw [hL_eval, hL_eval] at h1
    have hsum_ρ : ∑ j : ↑A, α j * ρ j.1 = γ * ∑ j ∈ A, a' j * ρ j := by
      rw [Finset.mul_sum, ← Finset.sum_attach A]
      apply Finset.sum_congr rfl
      intro j _
      simp only [a', dif_pos j.2]
      field_simp [hγ_pos.ne']
    have hsum_w : ∑ j : ↑A, α j * work y j = γ * ∑ j ∈ A, a' j * ∫ t in Icc s T', y j t := by
      rw [Finset.mul_sum, ← Finset.sum_attach A]
      apply Finset.sum_congr rfl
      intro j _
      simp only [a', dif_pos j.2]
      change α j * ∫ t in Icc s T', y j.1 t = _
      field_simp [hγ_pos.ne']
    rw [hsum_ρ, hsum_w] at h1
    have hdiv : costR x ≤ ∑ j ∈ A, a' j * ρ j + costR y - ∑ j ∈ A, a' j * ∫ t in Icc s T', y j t := by
      nlinarith
    have hcomb : ∑ j ∈ A, ∫ t in Icc s T', (a' j - I.g j t) * y j t =
        (∑ j ∈ A, a' j * ∫ t in Icc s T', y j t) - costR y := by
      dsimp [costR]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have heq : (fun t => (a' j - I.g j t) * y j t) =
          fun t => a' j * y j t - I.g j t * y j t := by funext t; ring
      rw [heq, integral_sub ((inHorizon_integrableOn hy j).const_mul (a' j))
        (inHorizon_integrableOn_g I hI hsT' hA hy hj), integral_const_mul]
    linarith
  -- Bound a' j ≤ g j T for all j ∈ A
  have ha'_le : ∀ j₀ ∈ A, a' j₀ ≤ I.g j₀ T := by
    intro j₀ hj₀
    have hstep : ∀ ε ∈ Ioc (0 : ℝ) 1, a' j₀ ≤ I.g j₀ (T + ε) := by
      intro ε hε
      let yε : Fin m → ℝ → ℝ := fun j t =>
        x j t + if j = j₀ then (Ioc T (T + ε)).indicator (fun _ => (1 : ℝ)) t else 0
      have hyε : InHorizon s T' A yε := by
        refine ⟨fun j => ?_, fun j t => ?_, fun j t ht => ?_, fun j t ht => ?_,
          fun j hj t => ?_, fun t => ?_⟩
        · dsimp [yε]; split_ifs
          · exact hx1 j |>.add (measurable_const.indicator measurableSet_Ioc)
          · exact hx1 j |>.add measurable_const
        · dsimp [yε]
          apply add_nonneg (hxnn j t)
          split_ifs
          · exact indicator_nonneg (fun _ _ => zero_le_one) t
          · exact le_rfl
        · dsimp [yε]; rw [hx3 j t ht, zero_add]
          split_ifs
          · exact indicator_of_notMem (fun h => absurd h.1 (not_lt.2 (le_trans ht.le hsT))) _
          · rfl
        · dsimp [yε]; rw [hT j t (lt_trans hTT' ht), zero_add]
          split_ifs
          · exact indicator_of_notMem (fun h => by linarith [h.2, hε.2]) _
          · rfl
        · dsimp [yε]; rw [hx4 j hj t, zero_add]
          split_ifs with heq
          · exact absurd (heq ▸ hj₀) hj
          · rfl
        · by_cases ht : t ∈ Ioc T (T + ε)
          · have hx0 : ∀ j, x j t = 0 := fun j => hT j t ht.1
            simp [yε, hx0, indicator_of_mem ht]
          · have hsum_eq : ∑ j : Fin m, yε j t = ∑ j : Fin m, x j t := by
              apply Finset.sum_congr rfl
              intro j _; dsimp [yε]; split_ifs
              · rw [indicator_of_notMem ht, add_zero]
              · rw [add_zero]
            rw [hsum_eq]; exact hx5 t
      have hm := hmain yε hyε
      have hterm : ∀ j ∈ A, ∫ t in Icc s T', (a' j - I.g j t) * yε j t =
          (∫ t in Icc s T', (a' j - I.g j t) * x j t) +
          if j = j₀ then ∫ t in Ioc T (T + ε), (a' j₀ - I.g j₀ t) else 0 := by
        intro j hj
        by_cases heq : j = j₀
        · subst heq
          simp only [↓reduceIte]
          have hsub : Ioc T (T + ε) ⊆ Icc s T' := fun t ht =>
            ⟨le_trans hsT ht.1.le, by linarith [ht.2, hε.2]⟩
          have hf_int : IntegrableOn (fun t => a' j - I.g j t) (Icc s T') :=
            (integrableOn_const (by simp)).sub
              ((g_contOn I j (hI j) (hA j hj)).mono Icc_subset_Ici_self).integrableOn_Icc
          have h1 : (fun t => (a' j - I.g j t) * yε j t) =
              fun t => (a' j - I.g j t) * x j t +
                (Ioc T (T + ε)).indicator (fun t => a' j - I.g j t) t := by
            funext t; dsimp [yε]; simp only [↓reduceIte]
            by_cases ht : t ∈ Ioc T (T + ε)
            · rw [indicator_of_mem ht, indicator_of_mem ht]; ring
            · rw [indicator_of_notMem ht, indicator_of_notMem ht]; ring
          rw [h1, integral_add]
          · rw [setIntegral_indicator measurableSet_Ioc, inter_eq_right.2 hsub]
          · have hfx : (fun t => (a' j - I.g j t) * x j t) =
                fun t => a' j * x j t - I.g j t * x j t := by funext t; ring
            rw [hfx]
            exact ((inHorizon_integrableOn hxY j).const_mul (a' j)).sub
              (inHorizon_integrableOn_g I hI hsT' hA hxY hj)
          · exact hf_int.indicator measurableSet_Ioc
        · simp only [heq, ↓reduceIte, add_zero]
          congr 1; funext t; simp [yε, heq]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
        Finset.sum_ite_eq' A j₀, if_pos hj₀] at hm
      -- Simplify ∑ j ∈ A, ∫ (a' j - g j) * x j = ∑ a' j * ρ j - costR x
      have hx_comb : ∑ j ∈ A, ∫ t in Icc s T', (a' j - I.g j t) * x j t =
          (∑ j ∈ A, a' j * ρ j) - costR x := by
        dsimp [costR]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have heq : (fun t => (a' j - I.g j t) * x j t) =
            fun t => a' j * x j t - I.g j t * x j t := by funext t; ring
        rw [heq, integral_sub ((inHorizon_integrableOn hxY j).const_mul (a' j))
          (inHorizon_integrableOn_g I hI hsT' hA hxY hj), integral_const_mul,
          show ∫ t in Icc s T', x j t = ρ j from hwork_x ⟨j, hj⟩]
      rw [hx_comb] at hm
      have hint_neg : ∫ t in Ioc T (T + ε), (a' j₀ - I.g j₀ t) ≤ 0 := by linarith
      have hg_int : IntegrableOn (I.g j₀) (Ioc T (T + ε)) :=
        ((g_contOn I j₀ (hI j₀) (hA j₀ hj₀)).mono
          (fun t ht => le_trans hsT ht.1)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
      have hge : ∫ t in Ioc T (T + ε), (a' j₀ - I.g j₀ (T + ε)) ≤
          ∫ t in Ioc T (T + ε), (a' j₀ - I.g j₀ t) := by
        apply setIntegral_mono_on (integrableOn_const (by simp))
          ((integrableOn_const (by simp)).sub hg_int) measurableSet_Ioc
        intro t ht
        have := (hI j₀).2.2.2.1 (le_trans (hA j₀ hj₀) (le_trans hsT ht.1.le))
          (le_trans (hA j₀ hj₀) (le_trans hsT (by linarith [hε.1]))) ht.2
        change a' j₀ - I.g j₀ (T + ε) ≤ a' j₀ - I.g j₀ t
        linarith
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le (by linarith [hε.1])] at hge
      have hlen : T + ε - T = ε := by ring
      rw [hlen] at hge
      nlinarith [hε.1]
    have hcont_at : ContinuousWithinAt (I.g j₀) (Ici s) T :=
      g_contOn I j₀ (hI j₀) (hA j₀ hj₀) T hsT
    have htend : Filter.Tendsto (fun ε : ℝ => I.g j₀ (T + ε)) (nhdsWithin 0 (Ioi 0))
        (nhds (I.g j₀ T)) := by
      refine hcont_at.tendsto.comp ?_
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h0 : Filter.Tendsto (fun ε : ℝ => T + ε) (nhds 0) (nhds T) := by
          simpa using (tendsto_const_nhds (x := T)).add (Filter.tendsto_id (x := nhds (0 : ℝ)))
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        exact le_trans hsT (by linarith [mem_Ioi.1 hε])
    have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0), a' j₀ ≤ I.g j₀ (T + ε) := by
      filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
      exact hstep ε hε
    exact ge_of_tendsto htend hev
  -- Define β' := betaMin I.g A a' and check feasibility and objective
  let β' : ℝ → ℝ := betaMin I.g A a'
  have hβ'_zero : ∀ t, T ≤ t → β' t = 0 := fun t ht =>
    betaMin_eq_zero_of_le I.g A a' t (fun j hj =>
      le_trans (ha'_le j hj) ((hI j).2.2.2.1 (le_trans (hA j hj) hsT)
        (le_trans (hA j hj) (le_trans hsT ht)) ht))
  have hβ'_cont : ContinuousOn β' (Ici s) :=
    betaMin_continuousOn I.g A a' (Ici s) (fun j hj => g_contOn I j (hI j) (hA j hj))
  have hβ'_int_Icc : IntegrableOn β' (Icc s T') :=
    (hβ'_cont.mono Icc_subset_Ici_self).integrableOn_Icc
  have hβ'_int_Ioi : IntegrableOn β' (Ioi T') := by
    refine (integrableOn_zero (μ := volume) (s := Ioi T')).congr_fun (fun t ht => ?_) measurableSet_Ioi
    exact (hβ'_zero t (le_trans hTT'.le (mem_Ioi.1 ht).le)).symm
  have hIci_split : Ici s = Icc s T' ∪ Ioi T' := by
    ext t; simp only [mem_Ici, mem_union, mem_Icc, mem_Ioi]
    constructor
    · intro h; rcases le_or_gt t T' with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr h'
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact le_trans hsT' h.le
  have hβ'_int : IntegrableOn β' (Ici s) := by
    rw [hIci_split]
    exact hβ'_int_Icc.union hβ'_int_Ioi
  have hβ'_integral : ∫ t in Ici s, β' t = ∫ t in Icc s T', β' t := by
    have hdisj : Disjoint (Icc s T') (Ioi T') := disjoint_left.2 (fun t h1 h2 => not_lt.2 h1.2 h2)
    rw [hIci_split, setIntegral_union hdisj measurableSet_Ioi hβ'_int_Icc hβ'_int_Ioi]
    have hz : ∫ t in Ioi T', β' t = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero (fun t ht => hβ'_zero t (le_trans hTT'.le (mem_Ioi.1 ht).le))
    rw [hz, add_zero]
  have hβ'_feas : IsOffDualFeas I.g s A a' β' :=
    ⟨hβ'_int, ha'_nn, Filter.Eventually.of_forall (fun t _ => betaMin_nonneg I.g A a' t),
      fun j hj => Filter.Eventually.of_forall (fun t _ => le_betaMin_add I.g A a' hj t)⟩
  -- Construct maximizing schedule y* ∈ InHorizon s T' A using globally continuous extensions
  let gExt : Fin m → ℝ → ℝ := fun j t => I.g j (max t s)
  let βExt : ℝ → ℝ := betaMin gExt A a'
  have hgExt_cont : ∀ j ∈ A, Continuous (gExt j) := fun j hj =>
    (g_contOn I j (hI j) (hA j hj)).comp_continuous (continuous_id.max continuous_const)
      (fun t => le_max_right t s)
  have hβExt_cont : Continuous βExt :=
    continuousOn_univ.1 (betaMin_continuousOn gExt A a' univ (fun j hj => (hgExt_cont j hj).continuousOn))
  let S : Fin m → Set ℝ := fun j =>
    if j ∈ A then
      Icc s T' ∩ {t | 0 < βExt t} ∩ {t | a' j - gExt j t = βExt t} ∩
        ⋂ k ∈ A.filter (· < j), {t | a' k - gExt k t < βExt t}
    else ∅
  have hS_meas : ∀ j, MeasurableSet (S j) := by
    intro j; dsimp [S]
    split_ifs with hj
    · refine ((measurableSet_Icc.inter
        (measurableSet_lt measurable_const hβExt_cont.measurable)).inter
        (measurableSet_eq_fun (measurable_const.sub (hgExt_cont j hj).measurable)
          hβExt_cont.measurable)).inter ?_
      refine MeasurableSet.biInter (Finset.countable_toSet _) (fun k hk => ?_)
      have hkA : k ∈ A := (Finset.mem_filter.1 hk).1
      exact measurableSet_lt (measurable_const.sub (hgExt_cont k hkA).measurable)
        hβExt_cont.measurable
    · exact MeasurableSet.empty
  have hS_disj : ∀ j₁ j₂ t, t ∈ S j₁ → t ∈ S j₂ → j₁ = j₂ := by
    intro j₁ j₂ t h₁ h₂
    by_contra hne
    have hj₁ : j₁ ∈ A := by by_contra hc; simp [S, hc] at h₁
    have hj₂ : j₂ ∈ A := by by_contra hc; simp [S, hc] at h₂
    simp only [S, if_pos hj₁, mem_inter_iff, mem_ofPred_eq, mem_iInter] at h₁
    simp only [S, if_pos hj₂, mem_inter_iff, mem_ofPred_eq, mem_iInter] at h₂
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := h₂.2 j₁ (Finset.mem_filter.2 ⟨hj₁, hlt⟩)
      linarith [h₁.1.2]
    · have := h₁.2 j₂ (Finset.mem_filter.2 ⟨hj₂, hgt⟩)
      linarith [h₂.1.2]
  let yStar : Fin m → ℝ → ℝ := fun j => (S j).indicator (fun _ => (1 : ℝ))
  have hyStar : InHorizon s T' A yStar := by
    refine ⟨fun j => measurable_const.indicator (hS_meas j),
      fun j t => indicator_nonneg (fun _ _ => zero_le_one) t,
      fun j t ht => indicator_of_notMem (fun hmem => by
        by_cases hj : j ∈ A
        · simp only [S, if_pos hj, mem_inter_iff] at hmem
          linarith [hmem.1.1.1.1]
        · simp [S, hj] at hmem) _,
      fun j t ht => indicator_of_notMem (fun hmem => by
        by_cases hj : j ∈ A
        · simp only [S, if_pos hj, mem_inter_iff] at hmem
          linarith [hmem.1.1.1.2]
        · simp [S, hj] at hmem) _,
      fun j hj t => by simp [yStar, S, hj],
      fun t => ?_⟩
    by_cases hex : ∃ j₀, t ∈ S j₀
    · obtain ⟨j₀, hj₀⟩ := hex
      rw [Finset.sum_eq_single j₀]
      · simp [yStar, indicator_of_mem hj₀]
      · intro j _ hne
        exact indicator_of_notMem (fun hj => hne (hS_disj j j₀ t hj hj₀)) _
      · intro h; exact absurd (Finset.mem_univ j₀) h
    · push Not at hex
      have : ∑ j : Fin m, yStar j t = 0 :=
        Finset.sum_eq_zero (fun j _ => indicator_of_notMem (hex j) _)
      linarith
  have hsum_yStar : ∀ t ∈ Icc s T', ∑ j ∈ A, (a' j - I.g j t) * yStar j t = β' t := by
    intro t ht
    have hgExt_eq : ∀ j, gExt j t = I.g j t := fun j => by simp [gExt, max_eq_left ht.1]
    have hβExt_eq : βExt t = β' t := by
      dsimp [βExt, β', betaMin]; simp only [hgExt_eq]
    by_cases hpos : 0 < β' t
    · have hAne : A.Nonempty := by
        by_contra hne
        simp only [β', betaMin, dif_neg hne] at hpos
        exact lt_irrefl _ hpos
      have hsup_eq : A.sup' hAne (fun j => a' j - I.g j t) = β' t := by
        dsimp [β', betaMin] at hpos ⊢
        rw [dif_pos hAne] at hpos ⊢
        rcases le_total (0 : ℝ) (A.sup' hAne (fun j => a' j - I.g j t)) with h | h
        · rw [max_eq_right h]
        · rw [max_eq_left h] at hpos; exact absurd hpos (lt_irrefl _)
      let F : Finset (Fin m) := A.filter (fun j => a' j - I.g j t = β' t)
      have hFne : F.Nonempty := by
        obtain ⟨k, hkA, hk⟩ := Finset.exists_mem_eq_sup' hAne (fun j => a' j - I.g j t)
        exact ⟨k, Finset.mem_filter.2 ⟨hkA, hk.symm.trans hsup_eq⟩⟩
      let j₀ : Fin m := F.min' hFne
      have hj₀F : j₀ ∈ F := Finset.min'_mem F hFne
      have hj₀A : j₀ ∈ A := (Finset.mem_filter.1 hj₀F).1
      have hj₀eq : a' j₀ - I.g j₀ t = β' t := (Finset.mem_filter.1 hj₀F).2
      have htS : t ∈ S j₀ := by
        simp only [S, if_pos hj₀A, mem_inter_iff, mem_ofPred_eq, mem_iInter, hgExt_eq, hβExt_eq]
        refine ⟨⟨⟨ht, hpos⟩, hj₀eq⟩, fun k hk => ?_⟩
        have hkA : k ∈ A := (Finset.mem_filter.1 hk).1
        have hklt : k < j₀ := (Finset.mem_filter.1 hk).2
        have hkle : a' k - I.g k t ≤ β' t := by linarith [le_betaMin_add I.g A a' hkA t]
        have hkne : a' k - I.g k t ≠ β' t := by
          intro heq
          have hkF : k ∈ F := Finset.mem_filter.2 ⟨hkA, heq⟩
          exact not_le.2 hklt (Finset.min'_le F k hkF)
        exact lt_of_le_of_ne hkle hkne
      rw [Finset.sum_eq_single j₀]
      · simp [yStar, indicator_of_mem htS, hj₀eq]
      · intro j _ hne
        have : t ∉ S j := fun hj => hne (hS_disj j j₀ t hj htS)
        simp [yStar, indicator_of_notMem this]
      · intro h; exact absurd hj₀A h
    · have hβ0 : β' t = 0 := le_antisymm (not_lt.1 hpos) (betaMin_nonneg I.g A a' t)
      rw [hβ0]
      apply Finset.sum_eq_zero
      intro j hj
      have : t ∉ S j := by
        simp only [S, if_pos hj, mem_inter_iff, mem_ofPred_eq, hβExt_eq, hβ0]
        intro h; exact lt_irrefl (0 : ℝ) h.1.1.2
      simp [yStar, indicator_of_notMem this]
  have hmain_star := hmain yStar hyStar
  have hint_star : ∑ j ∈ A, ∫ t in Icc s T', (a' j - I.g j t) * yStar j t = ∫ t in Icc s T', β' t := by
    rw [← integral_finsetSum]
    · exact setIntegral_congr_fun measurableSet_Icc hsum_yStar
    · intro j hj
      have heq : (fun t => (a' j - I.g j t) * yStar j t) =
          fun t => a' j * yStar j t - I.g j t * yStar j t := by funext t; ring
      rw [heq]
      exact ((inHorizon_integrableOn hyStar j).const_mul (a' j)).sub
        (inHorizon_integrableOn_g I hI hsT' hA hyStar hj)
  rw [hint_star, ← hβ'_integral] at hmain_star
  exact ⟨a', β', hβ'_feas, by rw [hcost_x]; exact hmain_star⟩

/-! ### 4. Dual reduction to `betaMin` and complementary slackness -/

lemma dual_eq_betaMin_and_cs {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (ρ : Fin m → ℝ) (hA : ∀ j ∈ A, I.r j ≤ s) (hρ : ∀ j ∈ A, 0 < ρ j)
    (x : Fin m → ℝ → ℝ) (hx : IsOptIntegral I.g s A ρ x)
    (a : Fin m → ℝ) (β : ℝ → ℝ) (hab : IsOffOptDual I.g s A ρ a β)
    {T : ℝ} (hsT : s ≤ T) (hT : ∀ j t, T < t → x j t = 0) :
    (∀ᵐ t, s ≤ t → β t = betaMin I.g A a t) ∧
    (∀ᵐ t, s ≤ t → (1 - ∑ j ∈ A, x j t) * betaMin I.g A a t = 0) ∧
    (∀ j ∈ A, ∀ᵐ t, s ≤ t → (betaMin I.g A a t + I.g j t - a j) * x j t = 0) ∧
    (∀ t, T ≤ t → betaMin I.g A a t = 0) := by
  obtain ⟨⟨hβ_int, ha_nn, hβ_nn, hβ_con⟩, hopt⟩ := hab
  obtain ⟨a', β', hfeas', hsd⟩ := strong_duality I hI s A ρ hA hρ x hx
  have hobj_ge : (offCost I.g x).toReal ≤ offDualObj s A ρ a β :=
    le_trans hsd (hopt a' β' hfeas')
  set f : ℝ → ℝ := betaMin I.g A a
  -- Show f ≤ β a.e. on Ici s
  have hf_le_β : ∀ᵐ t ∂volume.restrict (Ici s), f t ≤ β t := by
    have hcon_all : ∀ᵐ t ∂volume.restrict (Ici s), ∀ j ∈ A, a j ≤ β t + I.g j t :=
      (ae_ball_iff (Finset.countable_toSet A)).2 (fun j hj =>
        (ae_restrict_iff' measurableSet_Ici).2 (hβ_con j hj))
    have hnn' : ∀ᵐ t ∂volume.restrict (Ici s), 0 ≤ β t :=
      (ae_restrict_iff' measurableSet_Ici).2 hβ_nn
    filter_upwards [hnn', hcon_all] with t ht_nn ht_con
    exact betaMin_le I.g A a t (β t) ht_nn ht_con
  have hf_cont : ContinuousOn f (Ici s) :=
    betaMin_continuousOn I.g A a (Ici s) (fun j hj => g_contOn I j (hI j) (hA j hj))
  have hf_int : IntegrableOn f (Ici s) := by
    refine Integrable.mono' hβ_int (hf_cont.aestronglyMeasurable measurableSet_Ici) ?_
    filter_upwards [hf_le_β] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (betaMin_nonneg I.g A a t)]
    exact ht
  have hf_feas : IsOffDualFeas I.g s A a f :=
    ⟨hf_int, ha_nn, Filter.Eventually.of_forall (fun t _ => betaMin_nonneg I.g A a t),
      fun j hj => Filter.Eventually.of_forall (fun t _ => le_betaMin_add I.g A a hj t)⟩
  -- Optimality of (a, β) forces ∫_s^∞ (β - f) = 0, hence β = f a.e. on Ici s
  have hβ_le_f_int : ∫ t in Ici s, β t ≤ ∫ t in Ici s, f t := by
    have := hopt a f hf_feas
    unfold offDualObj at this
    linarith
  have hdiff_zero : ∫ t in Ici s, (β t - f t) = 0 := by
    rw [integral_sub hβ_int hf_int]
    have hge : 0 ≤ ∫ t in Ici s, (β t - f t) := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [hf_le_β] with t ht
      change 0 ≤ β t - f t
      linarith
    rw [integral_sub hβ_int hf_int] at hge
    linarith
  have hdiff_ae : (fun t => β t - f t) =ᵐ[volume.restrict (Ici s)] 0 := by
    refine (integral_eq_zero_iff_of_nonneg_ae ?_ (hβ_int.sub hf_int)).1 hdiff_zero
    filter_upwards [hf_le_β] with t ht
    change 0 ≤ β t - f t
    linarith
  have hβ_eq_f : ∀ᵐ t, s ≤ t → β t = f t := by
    refine (ae_restrict_iff' measurableSet_Ici).1 ?_
    filter_upwards [hdiff_ae] with t ht
    change β t - f t = 0 at ht
    linarith
  have hβ_int_eq : ∫ t in Ici s, β t = ∫ t in Ici s, f t := by
    apply setIntegral_congr_ae measurableSet_Ici
    exact hβ_eq_f
  -- Complementary slackness via nonnegative duality gap D(t)
  obtain ⟨⟨hx1, hx2, hx3, hx4, hx5, hx6, _⟩, _⟩ := hx
  have hxnn : ∀ j t, 0 ≤ x j t := fun j t => by rcases hx2 j t with h | h <;> linarith
  have hxY : InHorizon s T A x := ⟨hx1, hxnn, hx3, hT, hx4, hx5⟩
  have hx_int_Ici : ∀ j ∈ A, IntegrableOn (x j) (Ici s) := by
    intro j _
    have hsplit : Ici s = Icc s T ∪ Ioi T := by
      ext t; simp only [mem_Ici, mem_union, mem_Icc, mem_Ioi]
      constructor
      · intro h; rcases le_or_gt t T with h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr h'
      · rintro (⟨h, _⟩ | h); exact h; exact le_trans hsT h.le
    rw [hsplit]
    refine (inHorizon_integrableOn hxY j).union ?_
    exact integrableOn_zero.congr_fun (fun t ht => (hT j t (mem_Ioi.1 ht)).symm) measurableSet_Ioi
  have hx_int_val : ∀ j ∈ A, ∫ t in Ici s, x j t = ρ j := by
    intro j hj
    have hsplit : Ici s = Icc s T ∪ Ioi T := by
      ext t; simp only [mem_Ici, mem_union, mem_Icc, mem_Ioi]
      constructor
      · intro h; rcases le_or_gt t T with h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr h'
      · rintro (⟨h, _⟩ | h); exact h; exact le_trans hsT h.le
    have hIoi0 : ∫ t in Ioi T, x j t = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero (fun t ht => hT j t (mem_Ioi.1 ht))
    have hdisj : Disjoint (Icc s T) (Ioi T) := disjoint_left.2 (fun t h1 h2 => not_lt.2 h1.2 h2)
    rw [hsplit, setIntegral_union hdisj measurableSet_Ioi
      (inHorizon_integrableOn hxY j)
      (integrableOn_zero.congr_fun (fun t ht => (hT j t (mem_Ioi.1 ht)).symm) measurableSet_Ioi),
      hIoi0, add_zero]
    have h1 := hx6 j hj
    rw [inHorizon_lintegral_eq hxY j] at h1
    exact (ENNReal.ofReal_eq_ofReal_iff
      (setIntegral_nonneg measurableSet_Icc (fun t _ => hxnn j t)) (hρ j hj).le).1 h1
  have hgx_int_Ici : ∀ j ∈ A, IntegrableOn (fun t => I.g j t * x j t) (Ici s) := by
    intro j hj
    have hsplit : Ici s = Icc s T ∪ Ioi T := by
      ext t; simp only [mem_Ici, mem_union, mem_Icc, mem_Ioi]
      constructor
      · intro h; rcases le_or_gt t T with h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr h'
      · rintro (⟨h, _⟩ | h); exact h; exact le_trans hsT h.le
    rw [hsplit]
    refine (inHorizon_integrableOn_g I hI hsT hA hxY hj).union ?_
    exact integrableOn_zero.congr_fun
      (fun t ht => by simp [hT j t (mem_Ioi.1 ht)]) measurableSet_Ioi
  have hcost_Ici : (offCost I.g x).toReal = ∑ j ∈ A, ∫ t in Ici s, I.g j t * x j t := by
    have hnn : 0 ≤ ∑ j ∈ A, ∫ t in Icc s T, I.g j t * x j t :=
      Finset.sum_nonneg (fun j hj => setIntegral_nonneg measurableSet_Icc (fun t ht =>
        mul_nonneg ((hI j).2.2.1 t ((hA j hj).trans ht.1)) (hxnn j t)))
    rw [inHorizon_offCost_eq I hI hsT hA hxY, ENNReal.toReal_ofReal hnn]
    apply Finset.sum_congr rfl
    intro j hj
    have hsplit : Ici s = Icc s T ∪ Ioi T := by
      ext t; simp only [mem_Ici, mem_union, mem_Icc, mem_Ioi]
      constructor
      · intro h; rcases le_or_gt t T with h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr h'
      · rintro (⟨h, _⟩ | h); exact h; exact le_trans hsT h.le
    have hIoi0 : ∫ t in Ioi T, I.g j t * x j t = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero (fun t ht => by simp [hT j t (mem_Ioi.1 ht)])
    have hdisj : Disjoint (Icc s T) (Ioi T) := disjoint_left.2 (fun t h1 h2 => not_lt.2 h1.2 h2)
    rw [hsplit, setIntegral_union hdisj measurableSet_Ioi
      (inHorizon_integrableOn_g I hI hsT hA hxY hj)
      (integrableOn_zero.congr_fun (fun t ht => by simp [hT j t (mem_Ioi.1 ht)]) measurableSet_Ioi),
      hIoi0, add_zero]
  let D : ℝ → ℝ := fun t => f t + (∑ j ∈ A, I.g j t * x j t) - ∑ j ∈ A, a j * x j t
  have hD_decomp : ∀ t, D t =
      (1 - ∑ j ∈ A, x j t) * f t + ∑ j ∈ A, (f t + I.g j t - a j) * x j t := by
    intro t
    dsimp [D]
    have h1 : ∑ j ∈ A, (f t + I.g j t - a j) * x j t =
        (∑ j ∈ A, x j t) * f t + (∑ j ∈ A, I.g j t * x j t) - ∑ j ∈ A, a j * x j t := by
      have : ∀ j ∈ A, (f t + I.g j t - a j) * x j t =
          x j t * f t + I.g j t * x j t - a j * x j t := fun j _ => by ring
      rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.sum_mul]
    rw [h1]; ring
  have hD_nn : ∀ t, 0 ≤ D t := by
    intro t
    rw [hD_decomp t]
    have hsum_le : ∑ j ∈ A, x j t ≤ 1 := by
      calc ∑ j ∈ A, x j t ≤ ∑ j : Fin m, x j t :=
            Finset.sum_le_univ_sum_of_nonneg (fun j => hxnn j t)
        _ ≤ 1 := hx5 t
    refine add_nonneg (mul_nonneg (by linarith) (betaMin_nonneg I.g A a t)) ?_
    refine Finset.sum_nonneg (fun j hj => ?_)
    exact mul_nonneg (by linarith [le_betaMin_add I.g A a hj t]) (hxnn j t)
  have hD_int_1 : IntegrableOn (fun t => f t + ∑ j ∈ A, I.g j t * x j t) (Ici s) :=
    hf_int.add (integrable_finsetSum A (fun j hj => hgx_int_Ici j hj))
  have hD_int_2 : IntegrableOn (fun t => ∑ j ∈ A, a j * x j t) (Ici s) :=
    integrable_finsetSum A (fun j hj => (hx_int_Ici j hj).const_mul (a j))
  have hD_int : IntegrableOn D (Ici s) := hD_int_1.sub hD_int_2
  have hD_integral : ∫ t in Ici s, D t =
      (∫ t in Ici s, f t) + (offCost I.g x).toReal - ∑ j ∈ A, a j * ρ j := by
    dsimp [D]
    rw [integral_sub hD_int_1 hD_int_2,
      integral_add hf_int (integrable_finsetSum A (fun j hj => hgx_int_Ici j hj)),
      integral_finsetSum A (fun j hj => hgx_int_Ici j hj),
      integral_finsetSum A (fun j hj => (hx_int_Ici j hj).const_mul (a j)),
      ← hcost_Ici]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_const_mul, hx_int_val j hj]
  have hD_int_zero : ∫ t in Ici s, D t = 0 := by
    apply le_antisymm
    · rw [hD_integral]
      unfold offDualObj at hobj_ge
      rw [hβ_int_eq] at hobj_ge
      linarith
    · exact setIntegral_nonneg measurableSet_Ici (fun t _ => hD_nn t)
  have hD_ae_zero : ∀ᵐ t, s ≤ t → D t = 0 := by
    have h0 : D =ᵐ[volume.restrict (Ici s)] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hD_nn) hD_int).1 hD_int_zero
    exact (ae_restrict_iff' measurableSet_Ici).1 h0
  have hcs_idle : ∀ᵐ t, s ≤ t → (1 - ∑ j ∈ A, x j t) * f t = 0 := by
    filter_upwards [hD_ae_zero] with t ht hs_t
    have hD0 := ht hs_t
    rw [hD_decomp t] at hD0
    have hsum_le : ∑ j ∈ A, x j t ≤ 1 :=
      le_trans (Finset.sum_le_univ_sum_of_nonneg (fun j => hxnn j t)) (hx5 t)
    have h1 : 0 ≤ (1 - ∑ j ∈ A, x j t) * f t :=
      mul_nonneg (by linarith) (betaMin_nonneg I.g A a t)
    have h2 : 0 ≤ ∑ j ∈ A, (f t + I.g j t - a j) * x j t :=
      Finset.sum_nonneg (fun j hj =>
        mul_nonneg (by linarith [le_betaMin_add I.g A a hj t]) (hxnn j t))
    linarith
  have hcs_job : ∀ j ∈ A, ∀ᵐ t, s ≤ t → (f t + I.g j t - a j) * x j t = 0 := by
    intro j hj
    filter_upwards [hD_ae_zero] with t ht hs_t
    have hD0 := ht hs_t
    rw [hD_decomp t] at hD0
    have hsum_le : ∑ k ∈ A, x k t ≤ 1 :=
      le_trans (Finset.sum_le_univ_sum_of_nonneg (fun k => hxnn k t)) (hx5 t)
    have h1 : 0 ≤ (1 - ∑ k ∈ A, x k t) * f t :=
      mul_nonneg (by linarith) (betaMin_nonneg I.g A a t)
    have hterm_nn : ∀ k ∈ A, 0 ≤ (f t + I.g k t - a k) * x k t := fun k hk =>
      mul_nonneg (by linarith [le_betaMin_add I.g A a hk t]) (hxnn k t)
    have h2 : (f t + I.g j t - a j) * x j t ≤ ∑ k ∈ A, (f t + I.g k t - a k) * x k t :=
      Finset.single_le_sum hterm_nn hj
    linarith [hterm_nn j hj]
  have hf_zero_T : ∀ t, T ≤ t → f t = 0 := by
    -- First show f T = 0 by continuity of f on Ici s and f = 0 a.e. on Ioi T
    have hfT0 : f T = 0 := by
      by_contra hne
      have hpos : 0 < f T := lt_of_le_of_ne (betaMin_nonneg I.g A a T) (Ne.symm hne)
      have hcontT : ContinuousWithinAt f (Ici s) T := hf_cont T hsT
      have hev : {t | f T / 2 < f t} ∈ nhdsWithin T (Ici s) :=
        hcontT (Ioi_mem_nhds (by linarith))
      obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhdsWithin_iff.1 hev
      have hae_Ioo : ∀ᵐ t ∂volume.restrict (Ioo T (T + δ)), f t = 0 := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        filter_upwards [hcs_idle] with t ht htIoo
        have hst : s ≤ t := le_trans hsT htIoo.1.le
        have hsum0 : ∑ j ∈ A, x j t = 0 :=
          Finset.sum_eq_zero (fun j _ => hT j t htIoo.1)
        have := ht hst
        rw [hsum0, sub_zero, one_mul] at this
        exact this
      have hae_pos : ∀ᵐ t ∂volume.restrict (Ioo T (T + δ)), f T / 2 < f t := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall (fun t htIoo => ?_)
        have hdist : dist t T < δ := by
          rw [Real.dist_eq, abs_of_pos (by linarith [htIoo.1])]
          linarith [htIoo.2]
        exact hδ ⟨hdist, le_trans hsT htIoo.1.le⟩
      have hbot : ∀ᵐ t ∂volume.restrict (Ioo T (T + δ)), False := by
        filter_upwards [hae_Ioo, hae_pos] with t h0 h1
        linarith
      have hbot' : ∀ᵐ t, t ∉ Ioo T (T + δ) := by
        rw [ae_restrict_iff' measurableSet_Ioo] at hbot
        filter_upwards [hbot] with t ht hmem
        exact ht hmem
      have hvol0 : volume (Ioo T (T + δ)) = 0 := by
        rw [ae_iff] at hbot'
        have heq : {a : ℝ | ¬ a ∉ Ioo T (T + δ)} = Ioo T (T + δ) := by ext a; simp
        rwa [heq] at hbot'
      rw [Real.volume_Ioo] at hvol0
      have : (0 : ℝ≥0∞) < ENNReal.ofReal (T + δ - T) := by
        rw [ENNReal.ofReal_pos]; linarith
      rw [hvol0] at this
      exact lt_irrefl _ this
    intro t ht
    apply le_antisymm _ (betaMin_nonneg I.g A a t)
    have hanti := betaMin_antitoneOn I.g A a (Ici s)
      (fun j hj => (hI j).2.2.2.1.mono (Ici_subset_Ici.2 (hA j hj)))
    calc f t ≤ f T := hanti hsT (le_trans hsT ht) ht
      _ = 0 := hfT0
  exact ⟨hβ_eq_f, hcs_idle, hcs_job, hf_zero_T⟩

/-! ### 5. Differentiating `G + betaMin` via Stieltjes measure -/

lemma betaMin_le_betaHat {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (ρ : Fin m → ℝ) (hA : ∀ j ∈ A, I.r j ≤ s)
    (x : Fin m → ℝ → ℝ) (hx : IsOffIntSched s A ρ x)
    (a : Fin m → ℝ) {T : ℝ} (hsT : s ≤ T) (hT : ∀ j t, T < t → x j t = 0)
    (hcs_idle : ∀ᵐ t, s ≤ t → (1 - ∑ j ∈ A, x j t) * betaMin I.g A a t = 0)
    (hcs_job : ∀ j ∈ A, ∀ᵐ t, s ≤ t → (betaMin I.g A a t + I.g j t - a j) * x j t = 0)
    (hf_zero_T : ∀ t, T ≤ t → betaMin I.g A a t = 0) :
    ∀ t, s ≤ t → betaMin I.g A a t ≤ betaHat I.g' x t := by
  obtain ⟨hx1, hx2, hx3, hx4, hx5, _, _⟩ := hx
  set f : ℝ → ℝ := betaMin I.g A a
  have hxnn : ∀ j τ, 0 ≤ x j τ := fun j τ => by rcases hx2 j τ with h | h <;> linarith
  have hxle1 : ∀ j τ, x j τ ≤ 1 := fun j τ => by rcases hx2 j τ with h | h <;> linarith
  have hgp_x_nn : ∀ ℓ τ, 0 ≤ I.g' ℓ τ * x ℓ τ := by
    intro ℓ τ
    rcases hx2 ℓ τ with h | h
    · simp [h]
    · rw [h, mul_one]
      have hℓA : ℓ ∈ A := by
        by_contra hc; rw [hx4 ℓ hc τ] at h; exact zero_ne_one h
      have hsτ : s ≤ τ := by
        by_contra hc; rw [hx3 ℓ τ (lt_of_not_ge hc)] at h; exact zero_ne_one h
      exact gp_nonneg I ℓ (hI ℓ) τ ((hA ℓ hℓA).trans hsτ)
  -- Define globally monotone, continuous function H(τ) = ∑_{j ∈ A} g_j(max τ s) + f(max τ s)
  let H : ℝ → ℝ := fun τ => (∑ j ∈ A, I.g j (max τ s)) + f (max τ s)
  have hH_mono : Monotone H := by
    intro u v huv
    have hu : s ≤ max u s := le_max_right u s
    have hv : s ≤ max v s := le_max_right v s
    have hle : max u s ≤ max v s := max_le_max_right s huv
    have hsub := betaMin_sub_le_sum I.g A a (Ici s)
      (fun j hj => (hI j).2.2.2.1.mono (Ici_subset_Ici.2 (hA j hj))) hu hv hle
    dsimp [H]
    rw [Finset.sum_sub_distrib] at hsub
    linarith
  have hH_cont : Continuous H := by
    have hGcont : ContinuousOn (fun τ => ∑ j ∈ A, I.g j τ) (Ici s) :=
      continuousOn_finsetSum A (fun j hj => g_contOn I j (hI j) (hA j hj))
    have hfcont : ContinuousOn f (Ici s) :=
      betaMin_continuousOn I.g A a (Ici s) (fun j hj => g_contOn I j (hI j) (hA j hj))
    exact (hGcont.add hfcont).comp_continuous (continuous_id.max continuous_const)
      (fun τ => le_max_right τ s)
  have hH_stieltjes : ∀ z, hH_mono.stieltjesFunction z = H z := by
    intro z
    rw [hH_mono.stieltjesFunction_eq]
    have hcz := hH_mono.continuousAt_iff_leftLim_eq_rightLim.1 (hH_cont.continuousAt (x := z))
    apply le_antisymm _ (hH_mono.le_rightLim le_rfl)
    rw [← hcz]
    exact hH_mono.leftLim_le le_rfl
  let μ : Measure ℝ := hH_mono.stieltjesFunction.measure
  -- Main case split on t ≥ T vs s ≤ t < T
  intro t ht
  by_cases htT : T ≤ t
  · rw [hf_zero_T t htT]
    unfold betaHat
    exact Finset.sum_nonneg (fun ℓ _ => setIntegral_nonneg measurableSet_Ioi (fun τ _ => hgp_x_nn ℓ τ))
  push Not at htT
  -- Identify μ.rnDeriv volume a.e. on Ioo t T
  have hae_cs_job : ∀ᵐ τ, ∀ j ∈ A, s ≤ τ → (f τ + I.g j τ - a j) * x j τ = 0 :=
    (ae_ball_iff (Finset.countable_toSet A)).2 hcs_job
  have hrn_eq : ∀ᵐ τ ∂volume.restrict (Ioo t T),
      μ.rnDeriv volume τ = ENNReal.ofReal ((∑ j ∈ A, I.g' j τ) - ∑ j ∈ A, I.g' j τ * x j τ) := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hH_mono.ae_hasDerivAt, μ.rnDeriv_ne_top volume, hcs_idle, hae_cs_job]
      with τ hHderiv hne_top hidle hjob hτ
    have hsτ : s < τ := lt_of_le_of_lt ht hτ.1
    -- H agrees with (∑ g_j) + f on the open neighborhood Ioi s of τ
    have hH_ev : (fun u => (∑ j ∈ A, I.g j u) + f u) =ᶠ[nhds τ] H := by
      filter_upwards [Ioi_mem_nhds hsτ] with u hu
      dsimp [H]
      rw [max_eq_left (mem_Ioi.1 hu).le]
    have hGf_deriv : HasDerivAt (fun u => (∑ j ∈ A, I.g j u) + f u)
        ((μ.rnDeriv volume τ).toReal) τ :=
      hHderiv.congr_of_eventuallyEq hH_ev
    have hg_deriv : ∀ j ∈ A, HasDerivAt (I.g j) (I.g' j τ) τ := fun j hj =>
      ((hI j).2.2.2.2.2 τ (le_trans (hA j hj) hsτ.le)).hasDerivAt
        (Ici_mem_nhds (lt_of_le_of_lt (hA j hj) hsτ))
    have hG_deriv : HasDerivAt (fun u => ∑ j ∈ A, I.g j u) (∑ j ∈ A, I.g' j τ) τ :=
      HasDerivAt.fun_sum hg_deriv
    have hf_deriv : HasDerivAt f ((μ.rnDeriv volume τ).toReal - ∑ j ∈ A, I.g' j τ) τ :=
      (hGf_deriv.sub hG_deriv).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun u => by dsimp only [Pi.sub_apply]; ring))
    set f' : ℝ := (μ.rnDeriv volume τ).toReal - ∑ j ∈ A, I.g' j τ
    have hf'_eq : f' = -∑ j ∈ A, I.g' j τ * x j τ := by
      by_cases hex : ∃ j ∈ A, x j τ = 1
      · obtain ⟨j, hjA, hj1⟩ := hex
        -- Every other k ∈ A has x k τ = 0
        have hk0 : ∀ k ∈ A, k ≠ j → x k τ = 0 := by
          intro k _ hkj
          rcases hx2 k τ with h0 | h1
          · exact h0
          · exfalso
            have hle : x j τ + x k τ ≤ ∑ i : Fin m, x i τ := by
              have hpair : ({j, k} : Finset (Fin m)) ⊆ Finset.univ := Finset.subset_univ _
              calc x j τ + x k τ = ∑ i ∈ ({j, k} : Finset (Fin m)), x i τ := by
                    rw [Finset.sum_pair hkj.symm]
                _ ≤ ∑ i : Fin m, x i τ :=
                    Finset.sum_le_sum_of_subset_of_nonneg hpair (fun i _ _ => hxnn i τ)
            linarith [hx5 τ]
        have hsum_gpx : ∑ k ∈ A, I.g' k τ * x k τ = I.g' j τ := by
          rw [Finset.sum_eq_single j]
          · rw [hj1, mul_one]
          · intro k hk hkj; rw [hk0 k hk hkj, mul_zero]
          · intro h; exact absurd hjA h
        rw [hsum_gpx]
        -- Complementary slackness gives f τ + g j τ - a j = 0, a global minimum!
        have hcs := hjob j hjA hsτ.le
        rw [hj1, mul_one] at hcs
        have hmin : IsLocalMin (fun u => f u + I.g j u - a j) τ :=
          Filter.Eventually.of_forall (fun u => by
            dsimp only
            rw [hcs]
            linarith [le_betaMin_add I.g A a hjA u])
        have hφ_deriv : HasDerivAt (fun u => f u + I.g j u - a j) (f' + I.g' j τ) τ := by
          simpa using (hf_deriv.add (hg_deriv j hjA)).sub_const (a j)
        have h0 := hmin.hasDerivAt_eq_zero hφ_deriv
        linarith
      · push Not at hex
        have hx0 : ∀ k ∈ A, x k τ = 0 := fun k hk => by
          rcases hx2 k τ with h0 | h1
          · exact h0
          · exact absurd h1 (hex k hk)
        have hsum_gpx : ∑ k ∈ A, I.g' k τ * x k τ = 0 :=
          Finset.sum_eq_zero (fun k hk => by rw [hx0 k hk, mul_zero])
        rw [hsum_gpx, neg_zero]
        have hsum_x0 : ∑ k ∈ A, x k τ = 0 := Finset.sum_eq_zero hx0
        have hf0 : f τ = 0 := by
          have := hidle hsτ.le
          rw [hsum_x0, sub_zero, one_mul] at this
          exact this
        have hmin : IsLocalMin f τ :=
          Filter.Eventually.of_forall (fun u => by rw [hf0]; exact betaMin_nonneg I.g A a u)
        exact hmin.hasDerivAt_eq_zero hf_deriv
    have htoReal : (μ.rnDeriv volume τ).toReal =
        (∑ j ∈ A, I.g' j τ) - ∑ j ∈ A, I.g' j τ * x j τ := by
      dsimp [f'] at hf'_eq
      linarith
    rw [← htoReal, ENNReal.ofReal_toReal hne_top]
  -- Integrate rnDeriv over Ioc t T and apply setLIntegral_rnDeriv_le
  have hle_lint : ∫⁻ τ in Ioc t T,
      ENNReal.ofReal ((∑ j ∈ A, I.g' j τ) - ∑ j ∈ A, I.g' j τ * x j τ) ≤
      ENNReal.ofReal (H T - H t) := by
    calc ∫⁻ τ in Ioc t T,
          ENNReal.ofReal ((∑ j ∈ A, I.g' j τ) - ∑ j ∈ A, I.g' j τ * x j τ)
        = ∫⁻ τ in Ioo t T,
          ENNReal.ofReal ((∑ j ∈ A, I.g' j τ) - ∑ j ∈ A, I.g' j τ * x j τ) :=
          setLIntegral_congr Ioo_ae_eq_Ioc.symm
      _ = ∫⁻ τ in Ioo t T, μ.rnDeriv volume τ :=
          (lintegral_congr_ae hrn_eq).symm
      _ = ∫⁻ τ in Ioc t T, μ.rnDeriv volume τ :=
          setLIntegral_congr Ioo_ae_eq_Ioc
      _ ≤ μ (Ioc t T) := Measure.setLIntegral_rnDeriv_le (Ioc t T)
      _ = ENNReal.ofReal (H T - H t) := by
          dsimp [μ]
          rw [StieltjesFunction.measure_Ioc, hH_stieltjes, hH_stieltjes]
  -- Integrability and nonnegativity of the integrand on Ioc t T
  have hgp_int_Ioc : ∀ j ∈ A, IntegrableOn (I.g' j) (Ioc t T) := fun j hj =>
    (gp_int I j (hI j) s T (hA j hj)).mono_set (fun τ hτ => ⟨le_trans ht hτ.1.le, hτ.2⟩)
  have hgpx_int_Ioc : ∀ j ∈ A, IntegrableOn (fun τ => I.g' j τ * x j τ) (Ioc t T) := by
    intro j hj
    refine (hgp_int_Ioc j hj).mul_bdd (c := 1) (hx1 j).aestronglyMeasurable ?_
    filter_upwards with τ
    rw [Real.norm_eq_abs, abs_of_nonneg (hxnn j τ)]
    exact hxle1 j τ
  have hsub_int : IntegrableOn (fun τ => (∑ j ∈ A, I.g' j τ) - ∑ j ∈ A, I.g' j τ * x j τ)
      (Ioc t T) :=
    (integrable_finsetSum A hgp_int_Ioc).sub (integrable_finsetSum A hgpx_int_Ioc)
  have hsub_nn : ∀ τ ∈ Ioc t T, 0 ≤ (∑ j ∈ A, I.g' j τ) - ∑ j ∈ A, I.g' j τ * x j τ := by
    intro τ hτ
    rw [sub_nonneg]
    apply Finset.sum_le_sum
    intro j hj
    have hgnn : 0 ≤ I.g' j τ := gp_nonneg I j (hI j) τ (le_trans (hA j hj) (le_trans ht hτ.1.le))
    nlinarith [hxle1 j τ]
  rw [← ofReal_integral_eq_lintegral_ofReal hsub_int
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hsub_nn))] at hle_lint
  have hreal_le : ∫ τ in Ioc t T, ((∑ j ∈ A, I.g' j τ) - ∑ j ∈ A, I.g' j τ * x j τ) ≤
      H T - H t :=
    (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.2 (hH_mono htT.le))).1 hle_lint
  rw [integral_sub (integrable_finsetSum A hgp_int_Ioc) (integrable_finsetSum A hgpx_int_Ioc),
    integral_finsetSum A hgp_int_Ioc, integral_finsetSum A hgpx_int_Ioc] at hreal_le
  have hftc_sum : ∑ j ∈ A, ∫ τ in Ioc t T, I.g' j τ = ∑ j ∈ A, (I.g j T - I.g j t) :=
    Finset.sum_congr rfl (fun j hj => g_ftc I j (hI j) (le_trans (hA j hj) ht) htT.le)
  have hHT_sub : H T - H t = (∑ j ∈ A, (I.g j T - I.g j t)) - f t := by
    dsimp [H]
    rw [max_eq_left hsT, max_eq_left ht, hf_zero_T T le_rfl, add_zero, Finset.sum_sub_distrib]
    ring
  rw [hftc_sum, hHT_sub] at hreal_le
  have hf_le_sum : f t ≤ ∑ j ∈ A, ∫ τ in Ioc t T, I.g' j τ * x j τ := by linarith
  -- Identify ∑ j ∈ A, ∫_{Ioc t T} g'_j x_j with betaHat I.g' x t
  have hbh_eq : betaHat I.g' x t = ∑ j ∈ A, ∫ τ in Ioc t T, I.g' j τ * x j τ := by
    unfold betaHat
    have hsumA : ∑ ℓ : Fin m, ∫ τ in Ioi t, I.g' ℓ τ * x ℓ τ =
        ∑ ℓ ∈ A, ∫ τ in Ioi t, I.g' ℓ τ * x ℓ τ := by
      symm
      apply Finset.sum_subset (Finset.subset_univ A)
      intro ℓ _ hℓA
      exact setIntegral_eq_zero_of_forall_eq_zero (fun τ _ => by simp [hx4 ℓ hℓA τ])
    rw [hsumA]
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    have hsplit : Ioi t = Ioc t T ∪ Ioi T := by
      ext τ; simp only [mem_Ioi, mem_union, mem_Ioc]
      constructor
      · intro h; rcases le_or_gt τ T with h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr h'
      · rintro (⟨h, _⟩ | h); exact h; exact lt_trans htT h
    have hIoi_int : IntegrableOn (fun τ => I.g' ℓ τ * x ℓ τ) (Ioi T) :=
      integrableOn_zero.congr_fun (fun τ hτ => by simp [hT ℓ τ (mem_Ioi.1 hτ)]) measurableSet_Ioi
    have hIoi_zero : ∫ τ in Ioi T, I.g' ℓ τ * x ℓ τ = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero (fun τ hτ => by simp [hT ℓ τ (mem_Ioi.1 hτ)])
    rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi_same) measurableSet_Ioi
      (hgpx_int_Ioc ℓ hℓ) hIoi_int, hIoi_zero, add_zero]
  rw [hbh_eq]
  exact hf_le_sum

end GFCSEq20Aux

open GenCostSched.GFCS GFCSEq20Aux in
theorem solution {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (ρ : Fin m → ℝ) (hA : ∀ j ∈ A, I.r j ≤ s) (hρ : ∀ j ∈ A, 0 < ρ j)
    (x : Fin m → ℝ → ℝ) (hx : IsOptIntegral I.g s A ρ x)
    (a : Fin m → ℝ) (β : ℝ → ℝ) (hab : IsOffOptDual I.g s A ρ a β) :
    ∀ᵐ t, s ≤ t → β t ≤ betaHat I.g' x t := by
  obtain ⟨T0, hT0⟩ := hx.1.2.2.2.2.2.2
  set T : ℝ := max T0 s
  have hsT : s ≤ T := le_max_right _ _
  have hT : ∀ j t, T < t → x j t = 0 := fun j t ht =>
    hT0 j t (lt_of_le_of_lt (le_max_left _ _) ht)
  obtain ⟨hβ_eq, hcs_idle, hcs_job, hf_zero⟩ :=
    dual_eq_betaMin_and_cs I hI s A ρ hA hρ x hx a β hab hsT hT
  have hle := betaMin_le_betaHat I hI s A ρ hA x hx.1 a hsT hT hcs_idle hcs_job hf_zero
  filter_upwards [hβ_eq] with t ht hst
  rw [ht hst]
  exact hle t hst

