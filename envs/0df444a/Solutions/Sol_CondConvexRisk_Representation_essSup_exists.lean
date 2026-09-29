-- Prove2me | solution 1 for CondConvexRisk.Representation.essSup_exists
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:20:47.411441+00:00
-- url     : https://prove2.me/submissions/51359085-583b-4968-88f0-4ebc3b559052

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

/-- A strictly monotone map `EReal → [0,1] ⊆ ℝ≥0∞`. -/
noncomputable def aux_essx_phi (x : EReal) : ENNReal :=
  (ENNReal.orderIsoIicOneBirational (EReal.exp x) : ENNReal)

lemma aux_essx_phi_strictMono : StrictMono aux_essx_phi :=
  (Subtype.strictMono_coe _).comp
    (ENNReal.orderIsoIicOneBirational.strictMono.comp EReal.exp_strictMono)

lemma aux_essx_phi_le_one (x : EReal) : aux_essx_phi x ≤ 1 :=
  (ENNReal.orderIsoIicOneBirational (EReal.exp x)).2

lemma aux_essx_phi_measurable : Measurable aux_essx_phi :=
  aux_essx_phi_strictMono.monotone.measurable

lemma aux_essx_countable {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] [Nonempty ι] (F : ι → Ω → EReal)
    (hF : ∀ i, AEMeasurable (F i) P) :
    ∃ t : ℕ → ι, ∀ i, F i ≤ᵐ[P] fun ω => ⨆ n, F (t n) ω := by
  classical
  set v : (ℕ → ι) → ENNReal := fun t => ∫⁻ ω, aux_essx_phi (⨆ n, F (t n) ω) ∂P with hv
  have hmeas : ∀ t : ℕ → ι, AEMeasurable (fun ω => ⨆ n, F (t n) ω) P :=
    fun t => AEMeasurable.iSup (fun n => hF (t n))
  have hvle : ∀ t, v t ≤ 1 := by
    intro t
    calc v t ≤ ∫⁻ _ω, 1 ∂P := lintegral_mono (fun ω => aux_essx_phi_le_one _)
      _ = 1 := by simp
  have hvmono : ∀ t t' : ℕ → ι, (∀ ω, (⨆ n, F (t n) ω) ≤ ⨆ n, F (t' n) ω) → v t ≤ v t' := by
    intro t t' h
    exact lintegral_mono (fun ω => aux_essx_phi_strictMono.monotone (h ω))
  obtain ⟨u, -, hu_tend, hu_mem⟩ := exists_seq_tendsto_sSup (S := Set.range v)
    (Set.range_nonempty v) (OrderTop.bddAbove _)
  choose T hT using hu_mem
  let t : ℕ → ι := fun m => T m.unpair.1 m.unpair.2
  have ht_ge : ∀ k ω, (⨆ n, F (T k n) ω) ≤ ⨆ m, F (t m) ω := by
    intro k ω
    refine iSup_le fun n => ?_
    refine le_iSup_of_le (Nat.pair k n) ?_
    simp [t, Nat.unpair_pair]
  have hvt : sSup (Set.range v) ≤ v t := by
    refine le_of_tendsto' hu_tend fun k => ?_
    rw [← hT k]
    exact hvmono _ _ (ht_ge k)
  refine ⟨t, fun i => ?_⟩
  let t' : ℕ → ι := fun n => Nat.casesOn n i t
  have hsup' : ∀ ω, (⨆ n, F (t' n) ω) = F i ω ⊔ ⨆ n, F (t n) ω := by
    intro ω
    rw [← sup_iSup_nat_succ]
    rfl
  have hle : v t' ≤ v t := (le_sSup (Set.mem_range_self t')).trans hvt
  have hae : (fun ω => aux_essx_phi (⨆ n, F (t n) ω)) =ᵐ[P]
      (fun ω => aux_essx_phi (⨆ n, F (t' n) ω)) := by
    refine ae_eq_of_ae_le_of_lintegral_le ?_ ?_ ?_ hle
    · refine Eventually.of_forall fun ω => ?_
      refine aux_essx_phi_strictMono.monotone ?_
      rw [hsup']
      exact le_sup_right
    · exact ne_top_of_le_ne_top ENNReal.one_ne_top (hvle t)
    · exact aux_essx_phi_measurable.comp_aemeasurable (hmeas t')
  filter_upwards [hae] with ω hω
  have h := aux_essx_phi_strictMono.injective hω
  rw [h, hsup']
  exact le_sup_left

end CondConvexRisk.Representation

open CondConvexRisk.Representation
open MeasureTheory Filter Topology

theorem solution {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : ι → Ω → EReal) (hF : ∀ i, AEMeasurable (F i) P) :
    (∃ Z : Ω → EReal, IsEssSup P F Z) ∧
    (∀ Z Z' : Ω → EReal, IsEssSup P F Z → IsEssSup P F Z' → Z =ᵐ[P] Z') ∧
    (Nonempty ι → IsUpwardDirected P F → ∀ Z : Ω → EReal, IsEssSup P F Z →
      ∃ s : ℕ → ι, ∀ᵐ ω ∂P, Monotone (fun n => F (s n) ω) ∧
        Tendsto (fun n => F (s n) ω) atTop (𝓝 (Z ω))) := by
  have key : ∀ t : ℕ → ι, (∀ i, F i ≤ᵐ[P] fun ω => ⨆ n, F (t n) ω) →
      IsEssSup P F (fun ω => ⨆ n, F (t n) ω) := by
    intro t ht
    refine ⟨AEMeasurable.iSup (fun n => hF (t n)), ht, fun W _ hFW => ?_⟩
    filter_upwards [ae_all_iff.2 (fun n => hFW (t n))] with ω hω
    exact iSup_le hω
  have uniq : ∀ Z Z' : Ω → EReal, IsEssSup P F Z → IsEssSup P F Z' → Z =ᵐ[P] Z' := by
    intro Z Z' hZ hZ'
    exact (hZ.2.2 Z' hZ'.1 hZ'.2.1).antisymm (hZ'.2.2 Z hZ.1 hZ.2.1)
  refine ⟨?_, uniq, ?_⟩
  · rcases isEmpty_or_nonempty ι with hι | hι
    · refine ⟨fun _ => ⊥, aemeasurable_const, fun i => isEmptyElim i, fun W _ _ => ?_⟩
      exact Eventually.of_forall (fun ω => bot_le)
    · obtain ⟨t, ht⟩ := aux_essx_countable P F hF
      exact ⟨_, key t ht⟩
  · intro hι hdir Z hZ
    obtain ⟨t, ht⟩ := aux_essx_countable P F hF
    have hZeq := uniq _ _ (key t ht) hZ
    choose k hk1 hk2 using hdir
    let s : ℕ → ι := fun n => Nat.rec (t 0) (fun m sm => k sm (t (m + 1))) n
    have hs_succ : ∀ n, s (n + 1) = k (s n) (t (n + 1)) := fun n => rfl
    have h1 : ∀ᵐ ω ∂P, ∀ n, F (s n) ω ≤ F (s (n + 1)) ω := by
      rw [ae_all_iff]
      intro n
      rw [hs_succ]
      exact hk1 _ _
    have h2 : ∀ᵐ ω ∂P, ∀ n, F (t n) ω ≤ F (s n) ω := by
      rw [ae_all_iff]
      intro n
      cases n with
      | zero => exact Eventually.of_forall (fun ω => le_rfl)
      | succ m =>
        rw [hs_succ]
        exact hk2 _ _
    have h3 : ∀ᵐ ω ∂P, ∀ n, F (s n) ω ≤ Z ω := ae_all_iff.2 (fun n => hZ.2.1 (s n))
    refine ⟨s, ?_⟩
    filter_upwards [h1, h2, h3, hZeq] with ω h1 h2 h3 hZω
    have hmono : Monotone (fun n => F (s n) ω) := monotone_nat_of_le_succ h1
    refine ⟨hmono, ?_⟩
    have hsup : (⨆ n, F (s n) ω) = Z ω := by
      apply le_antisymm (iSup_le h3)
      rw [← hZω]
      exact iSup_mono h2
    rw [← hsup]
    exact tendsto_atTop_iSup hmono
