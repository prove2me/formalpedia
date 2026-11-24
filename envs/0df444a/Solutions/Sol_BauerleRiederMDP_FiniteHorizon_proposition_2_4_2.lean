-- Prove2me | solution 1 for BauerleRiederMDP.FiniteHorizon.proposition_2_4_2
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-24T20:49:29.240138+00:00
-- url     : https://prove2.me/submissions/90366afb-515f-4125-8216-d7b69d9e0fcd

import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_Policy
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_stepKernel
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_pathKernel
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_pathReward
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_markovRule
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_deltaN
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_IntegrabilityAssumption
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_IsUpperBoundingFunction

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel Hist histState measurable_histState)

set_option linter.unusedSectionVars false

universe u

namespace Prop242Sol

open BauerleRiederMDP.FiniteHorizon

variable {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

lemma pathReward_split (r : ℕ → E × A → ℝ) (g : E → ℝ) (n₀ j₀ k : ℕ) (h : Hist E A (j₀ + k)) :
    pathReward r g n₀ j₀ k h = pathReward r (fun _ => 0) n₀ j₀ k h + g (histState (j₀ + k) h) := by
  cases k with
  | zero => simp [pathReward]
  | succ k =>
    obtain ⟨h1, a, x⟩ := h
    simp [pathReward, histState]

lemma pathReward_nonneg (r : ℕ → E × A → ℝ) (hr : ∀ i xa, 0 ≤ r i xa) (n₀ j₀ k : ℕ)
    (h : Hist E A (j₀ + k)) : 0 ≤ pathReward r (fun _ => 0) n₀ j₀ k h := by
  induction k with
  | zero => simp [pathReward]
  | succ k ih =>
    obtain ⟨h1, a, x⟩ := h
    simp only [pathReward]
    have := ih h1
    have := hr (n₀ + k) (histState (j₀ + k) h1, a)
    linarith

lemma measurable_pathReward (r : ℕ → E × A → ℝ) (g : E → ℝ) (n₀ j₀ k : ℕ)
    (hr : ∀ i < k, Measurable (r (n₀ + i))) (hg : Measurable g) :
    Measurable (pathReward r g n₀ j₀ k) := by
  induction k generalizing g with
  | zero => exact hg.comp (measurable_histState _)
  | succ k ih =>
    have h1 := ih (fun _ => 0) (fun i hi => hr i (by omega)) measurable_const
    have h2 := hr k (by omega)
    change Measurable (fun p : Hist E A (j₀ + k) × A × E =>
      pathReward r (fun _ => 0) n₀ j₀ k p.1 + r (n₀ + k) (histState (j₀ + k) p.1, p.2.1) + g p.2.2)
    exact ((h1.comp measurable_fst).add (h2.comp
      (((measurable_histState _).comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd)))).add (hg.comp (measurable_snd.comp measurable_snd))

lemma lintegral_stepKernel (M : MarkovDecisionModel E A N) (m j : ℕ) (hm : m < N)
    (f : Hist E A j → A) (hf : Measurable f) (F : Hist E A (j + 1) → ENNReal) (hF : Measurable F)
    (h : Hist E A j) :
    ∫⁻ y, F y ∂(stepKernel M m j f hf h) =
      ∫⁻ x', F ((h, f h, x') : Hist E A j × A × E) ∂(M.Q m (histState j h, f h)) := by
  have : IsMarkovKernel (M.Q m) := ⟨fun xa => M.hQ_prob m hm xa⟩
  have hmap : Measurable (fun p : Hist E A j × E => ((p.1, f p.1, p.2) : Hist E A (j + 1))) :=
    measurable_fst.prodMk ((hf.comp measurable_fst).prodMk measurable_snd)
  exact (Kernel.lintegral_map _ hmap _ hF).trans (Kernel.lintegral_id_prod (hF.comp hmap) _ _)

/-- The bounding constants of the induction. -/
noncomputable def C (cr αb : ℝ) : ℕ → ℝ → ℝ
  | 0, c => c
  | k + 1, c => C cr αb k (cr + c * αb)

lemma C_nonneg {cr αb : ℝ} (hcr : 0 ≤ cr) (hα : 0 ≤ αb) :
    ∀ k c, 0 ≤ c → 0 ≤ C cr αb k c := by
  intro k
  induction k with
  | zero => intro c hc; exact hc
  | succ k ih => intro c hc; exact ih _ (by positivity)

lemma main_bound (M : MarkovDecisionModel E A N) (b : E → ℝ) (hbm : Measurable b)
    (hb0 : ∀ x, 0 ≤ b x) (cr αb : ℝ) (hcr : 0 ≤ cr) (hα : 0 ≤ αb)
    (hr : ∀ n < N, ∀ xa ∈ M.D n, max (M.r n xa) 0 ≤ cr * b xa.1)
    (hQ : ∀ n < N, ∀ xa ∈ M.D n,
      ∫⁻ x', ENNReal.ofReal (b x') ∂(M.Q n xa) ≤ ENNReal.ofReal (αb * b xa.1))
    (n₀ j₀ : ℕ) (rule : (i : ℕ) → n₀ + i < N → {f : Hist E A (j₀ + i) → A // Measurable f})
    (hrule : ∀ i hi h, (histState (j₀ + i) h, (rule i hi).1 h) ∈ M.D (n₀ + i)) :
    ∀ k, n₀ + k ≤ N → ∀ c, 0 ≤ c → ∀ h₀ : Hist E A j₀,
      ∫⁻ h, (ENNReal.ofReal (pathReward (fun k xa => max (M.r k xa) 0) (fun _ => 0) n₀ j₀ k h)
          + ENNReal.ofReal (c * b (histState (j₀ + k) h))) ∂(pathKernel M n₀ j₀ rule k h₀)
        ≤ ENNReal.ofReal (C cr αb k c * b (histState j₀ h₀)) := by
  have hrm : ∀ i, n₀ + i < N → Measurable (fun xa => max (M.r (n₀ + i) xa) 0) :=
    fun i hi => (M.hr_meas _ hi).max measurable_const
  intro k
  induction k with
  | zero =>
    intro _ c hc h₀
    have hmeas : Measurable (fun h : Hist E A j₀ =>
        ENNReal.ofReal (pathReward (fun k xa => max (M.r k xa) 0) (fun _ => 0) n₀ j₀ 0 h)
          + ENNReal.ofReal (c * b (histState (j₀ + 0) h))) :=
      (ENNReal.measurable_ofReal.comp (measurable_pathReward _ _ _ _ _
        (fun i hi => absurd hi (Nat.not_lt_zero _)) measurable_const)).add
        (ENNReal.measurable_ofReal.comp (measurable_const.mul (hbm.comp (measurable_histState _))))
    rw [show pathKernel M n₀ j₀ rule 0 = Kernel.id from rfl, Kernel.id_apply]
    refine (le_of_eq (lintegral_dirac' h₀ hmeas)).trans ?_
    simp [pathReward, C]
  | succ k ih =>
    intro hk c hc h₀
    have hk' : n₀ + k < N := by omega
    have : IsMarkovKernel (M.Q (n₀ + k)) := ⟨fun xa => M.hQ_prob _ hk' xa⟩
    have hmeas : Measurable (fun h : Hist E A (j₀ + (k + 1)) =>
        ENNReal.ofReal (pathReward (fun k xa => max (M.r k xa) 0) (fun _ => 0) n₀ j₀ (k + 1) h)
          + ENNReal.ofReal (c * b (histState (j₀ + (k + 1)) h))) :=
      (ENNReal.measurable_ofReal.comp (measurable_pathReward _ _ _ _ _
        (fun i hi => hrm i (by omega)) measurable_const)).add
        (ENNReal.measurable_ofReal.comp (measurable_const.mul (hbm.comp (measurable_histState _))))
    rw [show pathKernel M n₀ j₀ rule (k + 1) =
        stepKernel M (n₀ + k) (j₀ + k) (rule k hk').1 (rule k hk').2 ∘ₖ pathKernel M n₀ j₀ rule k
        from dif_pos hk', Kernel.lintegral_comp _ _ _ hmeas]
    refine le_trans (lintegral_mono fun h => ?_) (ih (by omega) (cr + c * αb) (by positivity) h₀)
    refine (le_of_eq (lintegral_stepKernel M (n₀ + k) (j₀ + k) hk' _ _ _ hmeas h)).trans ?_
    set s := histState (j₀ + k) h
    set a := (rule k hk').1 h
    set P := pathReward (fun k xa => max (M.r k xa) 0) (fun _ => 0) n₀ j₀ k h
    have hP : 0 ≤ P := pathReward_nonneg _ (fun _ _ => le_max_right _ _) _ _ _ _
    have hD := hrule k hk' h
    have hr1 : max (M.r (n₀ + k) (s, a)) 0 ≤ cr * b s := hr _ hk' _ hD
    have hQ1 : ∫⁻ x', ENNReal.ofReal (b x') ∂(M.Q (n₀ + k) (s, a)) ≤ ENNReal.ofReal (αb * b s) :=
      hQ _ hk' _ hD
    have hbs := hb0 s
    change ∫⁻ x', (ENNReal.ofReal (P + max (M.r (n₀ + k) (s, a)) 0 + 0)
        + ENNReal.ofReal (c * b x')) ∂(M.Q (n₀ + k) (s, a)) ≤ _
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    simp_rw [ENNReal.ofReal_mul hc]
    rw [lintegral_const_mul _ (show Measurable fun x => ENNReal.ofReal (b x) from
      ENNReal.measurable_ofReal.comp hbm), add_zero,
      ENNReal.ofReal_add hP (le_max_right _ _), add_assoc]
    gcongr
    calc ENNReal.ofReal (max (M.r (n₀ + k) (s, a)) 0)
          + ENNReal.ofReal c * ∫⁻ x', ENNReal.ofReal (b x') ∂(M.Q (n₀ + k) (s, a))
        ≤ ENNReal.ofReal (cr * b s) + ENNReal.ofReal c * ENNReal.ofReal (αb * b s) := by
          gcongr
      _ = ENNReal.ofReal ((cr + c * αb) * b s) := by
          rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf

end Prop242Sol

open BauerleRiederMDP.FiniteHorizon in
theorem solution {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (hb : IsUpperBoundingFunction M b) :
    (∀ n ≤ N, ∃ c : ℝ, 0 ≤ c ∧ ∀ x, deltaN M n x ≤ ENNReal.ofReal (c * b x)) ∧
    IntegrabilityAssumption M := by
  obtain ⟨hbm, hb0, cr, cg, αb, hcr, hcg, hα, hr, hg, hQ⟩ := hb
  have key : ∀ n ≤ N, ∀ x, deltaN M n x ≤ ENNReal.ofReal (Prop242Sol.C cr αb (N - n) cg * b x) := by
    intro n hn x
    unfold deltaN
    refine iSup_le fun π => ?_
    have hmain := Prop242Sol.main_bound M b hbm hb0 cr αb hcr hα hr hQ n 0 (markovRule π n)
      (fun i hi h => (π.2 ⟨n + i, hi⟩).2 (histState (0 + i) h)) (N - n) (by omega) cg hcg x
    refine le_trans (lintegral_mono fun h => ?_) hmain
    rw [Prop242Sol.pathReward_split]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal (hg _)))
  exact ⟨fun n hn => ⟨_, Prop242Sol.C_nonneg hcr hα _ _ hcg, key n hn⟩,
    fun n hn x => (key n hn x).trans_lt ENNReal.ofReal_lt_top⟩
