-- Prove2me | solution 1 for CondConvexRisk.Representation.expectation_minimalPenalty_eq
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:18:53.895671+00:00
-- url     : https://prove2.me/submissions/c6e30cdc-75b7-4054-a410-f578fa54ebb1

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup
import Definitions.Def_CondConvexRisk_Representation_CondConvexRiskMeasure
import Definitions.Def_CondConvexRisk_Representation_Representable
import Definitions.Def_CondConvexRisk_Representation_UncondConvexRisk

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

/-- For an a.e. upward directed family of `[0,∞]`-valued functions with finite supremum of
integrals, there is an a.e. upper bound whose integral is at most that supremum. -/
theorem aux_emp_countable_sup {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [Nonempty ι]
    (f : ι → Ω → ENNReal) (hf : ∀ i, AEMeasurable (f i) P)
    (hdir : ∀ i j, ∃ k, f i ≤ᵐ[P] f k ∧ f j ≤ᵐ[P] f k)
    (hT : (⨆ i, ∫⁻ ω, f i ω ∂P) ≠ ⊤) :
    ∃ W : Ω → ENNReal, AEMeasurable W P ∧ (∀ i, f i ≤ᵐ[P] W) ∧
      ∫⁻ ω, W ω ∂P ≤ ⨆ i, ∫⁻ ω, f i ω ∂P := by
  choose d hd1 hd2 using hdir
  obtain ⟨u, -, hu_tend, hu_mem⟩ :=
    exists_seq_tendsto_sSup (S := Set.range (fun i => ∫⁻ ω, f i ω ∂P))
      (Set.range_nonempty _) (OrderTop.bddAbove _)
  choose V hV using hu_mem
  let U : ℕ → ι := fun n => Nat.rec (V 0) (fun k Uk => d Uk (V (k+1))) n
  have hU0 : U 0 = V 0 := rfl
  have hUs : ∀ n, U (n+1) = d (U n) (V (n+1)) := fun n => rfl
  have hmono : ∀ n, f (U n) ≤ᵐ[P] f (U (n+1)) := fun n => by rw [hUs]; exact hd1 _ _
  have hVU : ∀ n, f (V n) ≤ᵐ[P] f (U n) := by
    intro n
    cases n with
    | zero => rw [hU0]
    | succ n => rw [hUs]; exact hd2 _ _
  have hmono_ae : ∀ᵐ ω ∂P, Monotone (fun n => f (U n) ω) := by
    have := ae_all_iff.2 hmono
    filter_upwards [this] with ω hω
    exact monotone_nat_of_le_succ hω
  let W : Ω → ENNReal := fun ω => ⨆ n, f (U n) ω
  have hWm : AEMeasurable W P := AEMeasurable.iSup (fun n => hf (U n))
  have hWint : ∫⁻ ω, W ω ∂P = ⨆ n, ∫⁻ ω, f (U n) ω ∂P :=
    lintegral_iSup' (fun n => hf (U n)) hmono_ae
  have hWle : ∫⁻ ω, W ω ∂P ≤ ⨆ i, ∫⁻ ω, f i ω ∂P := by
    rw [hWint]; exact iSup_le fun n => le_iSup (fun i => ∫⁻ ω, f i ω ∂P) (U n)
  have hTle : (⨆ i, ∫⁻ ω, f i ω ∂P) ≤ ∫⁻ ω, W ω ∂P := by
    have hsSup : sSup (Set.range (fun i => ∫⁻ ω, f i ω ∂P)) = ⨆ i, ∫⁻ ω, f i ω ∂P := sSup_range
    rw [← hsSup]
    refine le_of_tendsto' hu_tend fun n => ?_
    rw [← hV n, hWint]
    exact (lintegral_mono_ae (hVU n)).trans (le_iSup (fun n => ∫⁻ ω, f (U n) ω ∂P) n)
  refine ⟨W, hWm, fun i => ?_, hWle⟩
  have hmax_le : ∫⁻ ω, max (f i ω) (W ω) ∂P ≤ ∫⁻ ω, W ω ∂P := by
    have h1 : (fun ω => max (f i ω) (W ω)) = fun ω => ⨆ n, max (f i ω) (f (U n) ω) := by
      funext ω; exact sup_iSup
    rw [h1, lintegral_iSup' (fun n => (hf i).max (hf (U n)))]
    · refine iSup_le fun n => ?_
      refine le_trans ?_ hTle
      refine le_trans ?_ (le_iSup (fun i => ∫⁻ ω, f i ω ∂P) (d i (U n)))
      apply lintegral_mono_ae
      filter_upwards [hd1 i (U n), hd2 i (U n)] with ω h1 h2
      exact max_le h1 h2
    · filter_upwards [hmono_ae] with ω hω
      intro a b hab
      exact max_le_max le_rfl (hω hab)
  have hne : ∫⁻ ω, W ω ∂P ≠ ⊤ := ne_top_of_le_ne_top hT hWle
  have := ae_eq_of_ae_le_of_lintegral_le
    (Eventually.of_forall fun ω => le_max_right (f i ω) (W ω)) hne ((hf i).max hWm) hmax_le
  filter_upwards [this] with ω hω
  rw [hω]; exact le_max_left _ _

end CondConvexRisk.Representation

open CondConvexRisk.Representation
open MeasureTheory Filter Topology

theorem solution {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (ρ : (Ω → ℝ) → Ω → ℝ) (hρ : IsCondConvexRiskMeasure m P ρ) (Q : PG m P)
    (Z : Ω → EReal) (hZ : IsEssSup P (penaltyFamily m P ρ Q) Z) :
    HasExpectation P Z ∧
      expectation P Z = minPenalty₀ P (fun X => ∫ ω, ρ X ω ∂P) Q.1 := by
  set Qm : Measure Ω := Q.1 with hQm
  have hQprob : IsProbabilityMeasure Qm := Q.2.1
  have hQac : Qm ≪ P := Q.2.2.1
  have hQeq : ∀ A, MeasurableSet[m] A → Qm A = P A := Q.2.2.2
  obtain ⟨b, hb⟩ : ∃ b : LInf P → Ω → ℝ, b = fun X ω => -(Qm[X.1 | m]) ω - ρ X.1 ω := ⟨_, rfl⟩
  have hpf : ∀ X ω, penaltyFamily m P ρ Q X ω = (b X ω : EReal) := by
    intro X ω; rw [hb]; rfl
  clear_value Qm
  have htrim : P.trim hm = Qm.trim hm := by
    refine @Measure.ext Ω m _ _ (fun s hs => ?_)
    rw [trim_measurableSet_eq hm hs, trim_measurableSet_eq hm hs, hQeq s hs]
  have hintQ : ∀ X : Ω → ℝ, MemLp X ⊤ P → Integrable X Qm := by
    intro X hX
    have : MemLp X ⊤ Qm := by
      refine ⟨hX.1.mono_ac hQac, ?_⟩
      rw [eLpNorm_exponent_top]
      refine (eLpNormEssSup_mono_measure _ hQac).trans_lt ?_
      rw [← eLpNorm_exponent_top]; exact hX.2
    exact this.integrable le_top
  have hsm : ∀ X : LInf P, StronglyMeasurable[m] (b X) := by
    intro X; rw [hb]
    exact stronglyMeasurable_condExp.neg.sub (hρ.stronglyMeasurable X.1 X.2)
  have hce_int : ∀ X : LInf P, Integrable (Qm[X.1 | m]) P := by
    intro X
    refine integrable_of_integrable_trim hm ?_
    rw [htrim]
    exact integrable_condExp.trim hm stronglyMeasurable_condExp
  have hce_integral : ∀ X : LInf P, ∫ ω, (Qm[X.1 | m]) ω ∂P = ∫ ω, X.1 ω ∂Qm := by
    intro X
    rw [integral_trim hm stronglyMeasurable_condExp, htrim,
      ← integral_trim hm stronglyMeasurable_condExp, integral_condExp hm]
  have hintb : ∀ X : LInf P, Integrable (b X) P := by
    intro X; rw [hb]
    exact (hce_int X).neg.sub ((hρ.memLp X.1 X.2).integrable le_top)
  have hintb_eq : ∀ X : LInf P,
      ∫ ω, b X ω ∂P = -(∫ ω, X.1 ω ∂Qm) - ∫ ω, ρ X.1 ω ∂P := by
    intro X; rw [hb]
    simp only
    rw [integral_sub (f := fun ω => -(Qm[X.1 | m]) ω) (hce_int X).neg ((hρ.memLp X.1 X.2).integrable le_top), integral_neg,
      hce_integral X]
  let X0 : LInf P := ⟨0, MemLp.zero⟩
  have hb0 : b X0 =ᵐ[P] 0 := by
    filter_upwards [hρ.map_zero] with ω hω
    rw [hb]
    simp only [X0, condExp_zero, Pi.zero_apply, neg_zero, zero_sub, neg_eq_zero]
    simpa using hω
  have hdir : ∀ X Y : LInf P, ∃ V : LInf P, b X ≤ᵐ[P] b V ∧ b Y ≤ᵐ[P] b V := by
    intro X Y
    set A : Set Ω := {ω | b Y ω ≤ b X ω} with hAdef
    have hA : MeasurableSet[m] A := (hsm Y).measurableSet_le (hsm X)
    have hA' : MeasurableSet A := hm A hA
    set Λ : Ω → ℝ := A.indicator (fun _ => (1:ℝ)) with hΛ
    have hΛm : StronglyMeasurable[m] Λ := stronglyMeasurable_const.indicator hA
    set Vf : Ω → ℝ := Λ * X.1 + (1 - Λ) * Y.1 with hVf
    have hVf_eq : Vf = A.indicator X.1 + Aᶜ.indicator Y.1 := by
      funext ω
      by_cases hω : ω ∈ A
      · simp [hVf, hΛ, hω]
      · simp [hVf, hΛ, hω]
    have hVmem : MemLp Vf ⊤ P := by
      rw [hVf_eq]; exact (X.2.indicator hA').add (Y.2.indicator hA'.compl)
    have hconv := hρ.convex X.1 Y.1 Λ X.2 Y.2 hΛm (Eventually.of_forall fun ω => by
      by_cases hω : ω ∈ A <;> simp [hΛ, hω])
    have hce : Qm[Vf | m] =ᵐ[P] A.indicator (Qm[X.1 | m]) + Aᶜ.indicator (Qm[Y.1 | m]) := by
      have hQ : Qm[Vf | m] =ᵐ[Qm] A.indicator (Qm[X.1 | m]) + Aᶜ.indicator (Qm[Y.1 | m]) := by
        rw [hVf_eq]
        refine (condExp_add ((hintQ _ X.2).indicator hA')
          ((hintQ _ Y.2).indicator hA'.compl) m).trans ?_
        exact (condExp_indicator (hintQ _ X.2) hA).add (condExp_indicator (hintQ _ Y.2) hA.compl)
      have h1 : StronglyMeasurable[m] (Qm[Vf | m]) := stronglyMeasurable_condExp
      have h2 : StronglyMeasurable[m] (A.indicator (Qm[X.1 | m]) + Aᶜ.indicator (Qm[Y.1 | m])) :=
        (stronglyMeasurable_condExp.indicator hA).add
          (stronglyMeasurable_condExp.indicator hA.compl)
      rw [← StronglyMeasurable.ae_eq_trim_iff hm h1 h2, htrim,
        StronglyMeasurable.ae_eq_trim_iff hm h1 h2]
      exact hQ
    have hmax : ∀ᵐ ω ∂P, max (b X ω) (b Y ω) ≤ b ⟨Vf, hVmem⟩ ω := by
      filter_upwards [hce, hconv] with ω h1 h2
      have hbV : b ⟨Vf, hVmem⟩ ω = -(Qm[Vf | m] ω) - ρ Vf ω := by rw [hb]
      have hbX : b X ω = -(Qm[X.1 | m] ω) - ρ X.1 ω := by rw [hb]
      have hbY : b Y ω = -(Qm[Y.1 | m] ω) - ρ Y.1 ω := by rw [hb]
      rw [hbV, h1]
      simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.one_apply] at h2 ⊢
      by_cases hω : ω ∈ A
      · have hle : b Y ω ≤ b X ω := hω
        have hΛω : Λ ω = 1 := by simp [hΛ, hω]
        rw [hΛω] at h2
        rw [max_eq_left hle, Set.indicator_of_mem hω,
          Set.indicator_of_notMem (Set.notMem_compl_iff.2 hω), hbX]
        linarith
      · have hle : b X ω < b Y ω := lt_of_not_ge hω
        have hΛω : Λ ω = 0 := by simp [hΛ, hω]
        rw [hΛω] at h2
        rw [max_eq_right hle.le, Set.indicator_of_notMem hω,
          Set.indicator_of_mem (Set.mem_compl hω), hbY]
        linarith
    refine ⟨⟨Vf, hVmem⟩, ?_, ?_⟩
    · filter_upwards [hmax] with ω hω using (le_max_left _ _).trans hω
    · filter_upwards [hmax] with ω hω using (le_max_right _ _).trans hω
  have hZ0 : ∀ᵐ ω ∂P, 0 ≤ Z ω := by
    filter_upwards [hZ.2.1 X0, hb0] with ω h1 h2
    rw [hpf, h2] at h1
    simpa using h1
  have hneg : negExpectation P Z = 0 := by
    unfold negExpectation
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [hZ0] with ω hω
    exact EReal.toENNReal_of_nonpos (EReal.neg_le.2 (by simpa using hω))
  set S := minPenalty₀ P (fun X => ∫ ω, ρ X ω ∂P) Qm with hS
  have hterm : ∀ V : LInf P, ((∫ ω, b V ω ∂P : ℝ) : EReal) ≤ S := by
    intro V
    rw [hS, minPenalty₀, hintb_eq V]
    exact le_iSup (fun X : LInf P => ((-(∫ ω, X.1 ω ∂Qm) - ∫ ω, ρ X.1 ω ∂P : ℝ) : EReal)) V
  have hS0 : 0 ≤ S := by
    have := hterm X0
    rw [integral_congr_ae hb0] at this
    simpa only [Pi.zero_apply, integral_zero, EReal.coe_zero] using this
  have hcof : ∀ X : LInf P, ∃ V : LInf P, b X ≤ᵐ[P] b V ∧ 0 ≤ᵐ[P] b V := by
    intro X
    obtain ⟨V, h1, h2⟩ := hdir X X0
    refine ⟨V, h1, ?_⟩
    filter_upwards [h2, hb0] with ω h2 h0
    have h0' : b X0 ω = 0 := h0
    rw [h0'] at h2; exact h2
  have hle_pos : S ≤ (posExpectation P Z : EReal) := by
    rw [hS, minPenalty₀]
    refine iSup_le fun X => ?_
    rw [← hintb_eq X]
    obtain ⟨V, hXV, hV0⟩ := hcof X
    have h1 : ∫ ω, b X ω ∂P ≤ ∫ ω, b V ω ∂P := integral_mono_ae (hintb X) (hintb V) hXV
    have h2 : ENNReal.ofReal (∫ ω, b V ω ∂P) = ∫⁻ ω, ENNReal.ofReal (b V ω) ∂P :=
      ofReal_integral_eq_lintegral_ofReal (hintb V) hV0
    have h3 : ∫⁻ ω, ENNReal.ofReal (b V ω) ∂P ≤ posExpectation P Z := by
      unfold posExpectation
      apply lintegral_mono_ae
      filter_upwards [hZ.2.1 V] with ω hω
      rw [hpf] at hω
      have := EReal.toENNReal_le_toENNReal hω
      simpa using this
    have hnn : 0 ≤ ∫ ω, b V ω ∂P := integral_nonneg_of_ae hV0
    calc ((∫ ω, b X ω ∂P : ℝ) : EReal) ≤ ((∫ ω, b V ω ∂P : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.2 h1
      _ = (ENNReal.ofReal (∫ ω, b V ω ∂P) : EReal) := by
          rw [EReal.coe_ennreal_ofReal, max_eq_left hnn]
      _ ≤ (posExpectation P Z : EReal) := EReal.coe_ennreal_le_coe_ennreal_iff.2 (h2 ▸ h3)
  have hT : (⨆ X : LInf P, ∫⁻ ω, ENNReal.ofReal (b X ω) ∂P) ≤ S.toENNReal := by
    refine iSup_le fun X => ?_
    obtain ⟨V, hXV, hV0⟩ := hcof X
    calc ∫⁻ ω, ENNReal.ofReal (b X ω) ∂P ≤ ∫⁻ ω, ENNReal.ofReal (b V ω) ∂P := by
          apply lintegral_mono_ae
          filter_upwards [hXV] with ω hω
          exact ENNReal.ofReal_le_ofReal hω
      _ = ENNReal.ofReal (∫ ω, b V ω ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal (hintb V) hV0).symm
      _ = ((∫ ω, b V ω ∂P : ℝ) : EReal).toENNReal := (EReal.real_coe_toENNReal _).symm
      _ ≤ S.toENNReal := EReal.toENNReal_le_toENNReal (hterm V)
  have hpos_le : posExpectation P Z ≤ S.toENNReal := by
    refine le_trans ?_ hT
    by_cases hTop : (⨆ X : LInf P, ∫⁻ ω, ENNReal.ofReal (b X ω) ∂P) = ⊤
    · rw [hTop]; exact le_top
    have : Nonempty (LInf P) := ⟨X0⟩
    obtain ⟨W, hWm, hWX, hWle⟩ := aux_emp_countable_sup P (fun X ω => ENNReal.ofReal (b X ω))
      (fun X => ENNReal.measurable_ofReal.comp_aemeasurable (hintb X).aemeasurable)
      (fun X Y => by
        obtain ⟨V, h1, h2⟩ := hdir X Y
        refine ⟨V, ?_, ?_⟩
        · filter_upwards [h1] with ω hω using ENNReal.ofReal_le_ofReal hω
        · filter_upwards [h2] with ω hω using ENNReal.ofReal_le_ofReal hω) hTop
    have hZW : Z ≤ᵐ[P] fun ω => (W ω : EReal) := by
      refine hZ.2.2 _ (measurable_coe_ennreal_ereal.comp_aemeasurable hWm) fun X => ?_
      filter_upwards [hWX X] with ω hω
      rw [hpf]
      calc (b X ω : EReal) ≤ (ENNReal.ofReal (b X ω) : EReal) := by
            rw [EReal.coe_ennreal_ofReal]; exact EReal.coe_le_coe_iff.2 (le_max_left _ _)
        _ ≤ (W ω : EReal) := EReal.coe_ennreal_le_coe_ennreal_iff.2 hω
    refine le_trans ?_ hWle
    unfold posExpectation
    apply lintegral_mono_ae
    filter_upwards [hZW] with ω hω
    have := EReal.toENNReal_le_toENNReal hω
    rwa [EReal.toENNReal_coe] at this
  refine ⟨Or.inr (by rw [hneg]; exact ENNReal.zero_ne_top), ?_⟩
  unfold expectation
  rw [hneg, EReal.coe_ennreal_zero, sub_zero]
  refine le_antisymm ?_ hle_pos
  calc (posExpectation P Z : EReal) ≤ (S.toENNReal : EReal) :=
        EReal.coe_ennreal_le_coe_ennreal_iff.2 hpos_le
    _ = S := EReal.coe_toENNReal hS0
