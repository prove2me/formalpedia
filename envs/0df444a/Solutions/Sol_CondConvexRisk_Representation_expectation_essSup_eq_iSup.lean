-- Prove2me | solution 1 for CondConvexRisk.Representation.expectation_essSup_eq_iSup
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:30:53.742181+00:00
-- url     : https://prove2.me/submissions/896a878b-3cb7-4030-aabf-c9c1a16295b0

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

/-- A bounded strictly increasing map `EReal → [0,1] ⊆ ℝ≥0∞`. -/
noncomputable def aux_ees_g (x : EReal) : ENNReal :=
  (ENNReal.orderIsoIicOneBirational (EReal.expOrderIso x) : ENNReal)

lemma aux_ees_g_strictMono : StrictMono aux_ees_g := by
  intro a b h
  unfold aux_ees_g
  exact ENNReal.orderIsoIicOneBirational.strictMono (EReal.expOrderIso.strictMono h)

lemma aux_ees_g_le_one (x : EReal) : aux_ees_g x ≤ 1 :=
  (ENNReal.orderIsoIicOneBirational (EReal.expOrderIso x)).2

lemma aux_ees_g_measurable : Measurable aux_ees_g :=
  aux_ees_g_strictMono.monotone.measurable

lemma aux_ees_pos_mono {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {X Y : Ω → EReal}
    (h : X ≤ᵐ[P] Y) : posExpectation P X ≤ posExpectation P Y :=
  lintegral_mono_ae (h.mono fun _ hω => EReal.toENNReal_le_toENNReal hω)

lemma aux_ees_neg_anti {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {X Y : Ω → EReal}
    (h : X ≤ᵐ[P] Y) : negExpectation P Y ≤ negExpectation P X :=
  lintegral_mono_ae (h.mono fun _ hω => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr hω))

lemma aux_ees_exp_mono {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {X Y : Ω → EReal}
    (h : X ≤ᵐ[P] Y) : expectation P X ≤ expectation P Y := by
  unfold expectation
  exact EReal.sub_le_sub (by exact_mod_cast aux_ees_pos_mono P h)
    (by exact_mod_cast aux_ees_neg_anti P h)

lemma aux_ees_seq {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : ι → Ω → EReal) (hF : ∀ i, AEMeasurable (F i) P)
    (hdir : IsUpwardDirected P F) (i₀ : ι) (Z : Ω → EReal) (hZ : IsEssSup P F Z) :
    ∃ k : ℕ → ι, F i₀ ≤ᵐ[P] F (k 0) ∧ (∀ n, F (k n) ≤ᵐ[P] F (k (n + 1))) ∧
      Z =ᵐ[P] fun ω => ⨆ n, F (k n) ω := by
  classical
  choose d hd1 hd2 using hdir
  set S : Set ENNReal := Set.range (fun i => ∫⁻ ω, aux_ees_g (F i ω) ∂P) with hS
  obtain ⟨u, -, hu_tend, hu_mem⟩ :=
    exists_seq_tendsto_sSup (S := S) ⟨_, i₀, rfl⟩ (OrderTop.bddAbove S)
  choose j hj using hu_mem
  let k : ℕ → ι := fun n => Nat.rec (d i₀ (j 0)) (fun m km => d km (j (m + 1))) n
  have hk0 : k 0 = d i₀ (j 0) := rfl
  have hks : ∀ n, k (n + 1) = d (k n) (j (n + 1)) := fun n => rfl
  have hkj : ∀ n, F (j n) ≤ᵐ[P] F (k n) := by
    intro n
    cases n with
    | zero => rw [hk0]; exact hd2 _ _
    | succ m => rw [hks]; exact hd2 _ _
  have hkmono : ∀ n, F (k n) ≤ᵐ[P] F (k (n + 1)) := fun n => by rw [hks]; exact hd1 _ _
  have hmono_ae : ∀ᵐ ω ∂P, Monotone (fun n => F (k n) ω) := by
    have := ae_all_iff.2 hkmono
    filter_upwards [this] with ω hω
    exact monotone_nat_of_le_succ hω
  set W : Ω → EReal := fun ω => ⨆ n, F (k n) ω with hW
  have hWm : AEMeasurable W P := AEMeasurable.iSup (fun n => hF (k n))
  have hFW : ∀ i, F i ≤ᵐ[P] W := by
    intro i
    set V : Ω → ENNReal := fun ω => ⨆ n, aux_ees_g (F (k n) ω) with hV
    set U : Ω → ENNReal := fun ω => ⨆ n, aux_ees_g (max (F i ω) (F (k n) ω)) with hU
    have hVU : V ≤ᵐ[P] U := ae_of_all _ fun ω =>
      iSup_mono fun n => aux_ees_g_strictMono.monotone (le_max_right _ _)
    have hVfin : ∫⁻ ω, V ω ∂P ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ∫⁻ _, (1 : ENNReal) ∂P) ?_
        (lintegral_mono fun ω => iSup_le fun n => aux_ees_g_le_one _)
      simp
    have hUm : AEMeasurable U P := AEMeasurable.iSup fun n =>
      aux_ees_g_measurable.comp_aemeasurable ((hF i).max (hF (k n)))
    have hc_le_V : sSup S ≤ ∫⁻ ω, V ω ∂P := by
      refine le_of_tendsto' hu_tend fun n => ?_
      rw [← hj n]
      refine lintegral_mono_ae ?_
      filter_upwards [hkj n] with ω hω
      exact (aux_ees_g_strictMono.monotone hω).trans
        (le_iSup (fun n => aux_ees_g (F (k n) ω)) n)
    have hU_le_c : ∫⁻ ω, U ω ∂P ≤ sSup S := by
      rw [hU, lintegral_iSup']
      · refine iSup_le fun n => ?_
        refine le_trans ?_ (le_sSup ⟨d i (k n), rfl⟩)
        refine lintegral_mono_ae ?_
        filter_upwards [hd1 i (k n), hd2 i (k n)] with ω h1 h2
        exact aux_ees_g_strictMono.monotone (max_le h1 h2)
      · exact fun n => aux_ees_g_measurable.comp_aemeasurable ((hF i).max (hF (k n)))
      · filter_upwards [hmono_ae] with ω hω
        intro a b hab
        exact aux_ees_g_strictMono.monotone (max_le_max le_rfl (hω hab))
    have hUV : V =ᵐ[P] U :=
      ae_eq_of_ae_le_of_lintegral_le hVU hVfin hUm (hU_le_c.trans hc_le_V)
    filter_upwards [hUV] with ω hω
    by_contra hlt
    rw [not_le] at hlt
    have h1 : ∀ n, max (F i ω) (F (k n) ω) = F i ω := fun n =>
      max_eq_left ((le_iSup (fun n => F (k n) ω) n).trans hlt.le)
    have hUω : U ω = aux_ees_g (F i ω) := by simp only [hU, h1, iSup_const]
    have hVω : V ω ≤ aux_ees_g (W ω) := iSup_le fun n =>
      aux_ees_g_strictMono.monotone (le_iSup (fun n => F (k n) ω) n)
    have := aux_ees_g_strictMono hlt
    rw [← hUω, ← hω] at this
    exact absurd (hVω.trans_lt this) (lt_irrefl _)
  refine ⟨k, ?_, hkmono, ?_⟩
  · rw [hk0]; exact hd1 _ _
  · have h1 : Z ≤ᵐ[P] W := hZ.2.2 W hWm hFW
    have h2 : W ≤ᵐ[P] Z := by
      have := ae_all_iff.2 (fun n => hZ.2.1 (k n))
      filter_upwards [this] with ω hω
      exact iSup_le hω
    exact h1.antisymm h2

end CondConvexRisk.Representation

open CondConvexRisk.Representation

theorem solution {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : ι → Ω → EReal) (hF : ∀ i, AEMeasurable (F i) P)
    (hdir : IsUpwardDirected P F) (hexp : ∀ i, HasExpectation P (F i))
    (i₀ : ι) (hi₀ : negExpectation P (F i₀) ≠ ⊤)
    (Z : Ω → EReal) (hZ : IsEssSup P F Z) :
    HasExpectation P Z ∧ expectation P Z = ⨆ i, expectation P (F i) := by
  obtain ⟨k, hk0, hkmono, hZW⟩ := aux_ees_seq P F hF hdir i₀ Z hZ
  have hmono_ae : ∀ᵐ ω ∂P, Monotone (fun n => F (k n) ω) := by
    have := ae_all_iff.2 hkmono
    filter_upwards [this] with ω hω
    exact monotone_nat_of_le_succ hω
  have hq0 : negExpectation P (F (k 0)) ≠ ⊤ := ne_top_of_le_ne_top hi₀ (aux_ees_neg_anti P hk0)
  have hpos : posExpectation P Z = ⨆ n, posExpectation P (F (k n)) := by
    unfold posExpectation
    rw [← lintegral_iSup']
    · apply lintegral_congr_ae
      filter_upwards [hZW] with ω hω
      rw [hω]
      exact Monotone.map_iSup_of_continuousAt EReal.continuous_toENNReal.continuousAt
        (fun a b h => EReal.toENNReal_le_toENNReal h) (by simp)
    · exact fun n => (hF (k n)).ereal_toENNReal
    · filter_upwards [hmono_ae] with ω hω
      exact fun a b h => EReal.toENNReal_le_toENNReal (hω h)
  have hneg : negExpectation P Z = ⨅ n, negExpectation P (F (k n)) := by
    unfold negExpectation
    rw [← lintegral_iInf']
    · apply lintegral_congr_ae
      filter_upwards [hZW] with ω hω
      rw [hω]
      exact Antitone.map_iSup_of_continuousAt (f := fun x : EReal => (-x).toENNReal)
        (EReal.continuous_toENNReal.comp continuous_neg).continuousAt
        (fun a b h => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr h)) (by simp)
    · exact fun n => (hF (k n)).neg.ereal_toENNReal
    · filter_upwards [hmono_ae] with ω hω
      exact fun a b h => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hω h))
    · exact hq0
  have hnegZ : negExpectation P Z ≠ ⊤ := by
    rw [hneg]; exact ne_top_of_le_ne_top hq0 (iInf_le _ 0)
  refine ⟨Or.inr hnegZ, le_antisymm ?_ ?_⟩
  · set p := fun n => posExpectation P (F (k n)) with hp
    set q := fun n => negExpectation P (F (k n)) with hq
    have hpm : Monotone p := monotone_nat_of_le_succ fun n => aux_ees_pos_mono P (hkmono n)
    have hqa : Antitone q := antitone_nat_of_succ_le fun n => aux_ees_neg_anti P (hkmono n)
    have hpt : Tendsto p atTop (𝓝 (posExpectation P Z)) := hpos ▸ tendsto_atTop_iSup hpm
    have hqt : Tendsto q atTop (𝓝 (negExpectation P Z)) := hneg ▸ tendsto_atTop_iInf hqa
    have hp' : Tendsto (fun n => (p n : EReal)) atTop (𝓝 (posExpectation P Z : EReal)) :=
      continuous_coe_ennreal_ereal.continuousAt.tendsto.comp hpt
    have hq' : Tendsto (fun n => (q n : EReal)) atTop (𝓝 (negExpectation P Z : EReal)) :=
      continuous_coe_ennreal_ereal.continuousAt.tendsto.comp hqt
    have hc := EReal.continuousAt_add
      (p := ((posExpectation P Z : EReal), -(negExpectation P Z : EReal)))
      (Or.inr ?_) (Or.inl ?_)
    · have ht : Tendsto (fun n => expectation P (F (k n))) atTop (𝓝 (expectation P Z)) := by
        unfold expectation
        simp only [sub_eq_add_neg]
        exact hc.tendsto.comp (hp'.prodMk_nhds hq'.neg)
      exact le_of_tendsto' ht fun n => le_iSup (fun i => expectation P (F i)) (k n)
    · simp only [ne_eq, EReal.neg_eq_bot_iff, EReal.coe_ennreal_eq_top_iff]
      exact hnegZ
    · exact ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (EReal.coe_ennreal_nonneg _))
  · exact iSup_le fun i => aux_ees_exp_mono P (hZ.2.1 i)
