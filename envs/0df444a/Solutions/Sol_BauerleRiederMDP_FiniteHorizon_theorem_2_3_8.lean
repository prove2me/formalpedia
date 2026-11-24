-- Prove2me | solution 1 for BauerleRiederMDP.FiniteHorizon.theorem_2_3_8
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-24T21:13:03.094825+00:00
-- url     : https://prove2.me/submissions/4f7c0b47-8834-494b-8049-7f622aa552bc

import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_Policy
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_stepKernel
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_pathKernel
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_pathReward
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_markovRule
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_Vpi
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_V
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_deltaN
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_IntegrabilityAssumption
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_IsOptimal
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_TWellDefined
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_StructureAssumption
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_TChain
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.MeasurableLIntegral

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel IsMaximizer erealIntegral Hist histState
  measurable_histState Tf T L IM IsDecisionRule)

set_option linter.unusedSectionVars false

universe u

namespace Thm238Sol

open BauerleRiederMDP.FiniteHorizon

variable {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

lemma pathReward_split (r : ℕ → E × A → ℝ) (g : E → ℝ) (n₀ j₀ k : ℕ) (h : Hist E A (j₀ + k)) :
    pathReward r g n₀ j₀ k h = pathReward r (fun _ => 0) n₀ j₀ k h + g (histState (j₀ + k) h) := by
  cases k with
  | zero => simp [pathReward]
  | succ k =>
    obtain ⟨h1, a, x⟩ := h
    simp [pathReward, histState]

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


/-! ### Generic facts about `erealIntegral` -/

lemma measurable_ereal_neg : Measurable (fun x : EReal => -x) := continuous_neg.measurable

lemma pos_toENNReal (e : EReal) : (e ⊔ 0).toENNReal = e.toENNReal := by
  rcases le_total e 0 with h | h
  · rw [sup_eq_right.2 h, EReal.toENNReal_of_nonpos h]; simp
  · rw [sup_eq_left.2 h]

lemma erealIntegral_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (v : α → EReal) :
    erealIntegral μ v = ((∫⁻ x, (v x).toENNReal ∂μ : ENNReal) : EReal) +
      -((∫⁻ x, (-v x).toENNReal ∂μ : ENNReal) : EReal) := by
  simp only [erealIntegral, pos_toENNReal]

lemma nn_coe (a : NNReal) : ((a : ENNReal) : EReal) = ((a : ℝ) : EReal) := rfl

lemma ereal_split (e : EReal) : ((e.toENNReal : ENNReal) : EReal) + -(((-e).toENNReal : ENNReal) : EReal) = e := by
  induction e using EReal.rec with
  | bot => simp
  | top => simp
  | coe x =>
    rw [← EReal.coe_neg, EReal.real_coe_toENNReal, EReal.real_coe_toENNReal,
      EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal, ← EReal.coe_neg, ← EReal.coe_add]
    congr 1
    rcases le_total x 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring

lemma erealIntegral_mono {α : Type*} [MeasurableSpace α] (μ : Measure α) {v w : α → EReal}
    (h : ∀ x, v x ≤ w x) : erealIntegral μ v ≤ erealIntegral μ w := by
  rw [erealIntegral_eq, erealIntegral_eq]
  refine add_le_add (EReal.coe_ennreal_le_coe_ennreal_iff.2
    (lintegral_mono fun x => EReal.toENNReal_le_toENNReal (h x))) ?_
  exact EReal.neg_le_neg_iff.2 (EReal.coe_ennreal_le_coe_ennreal_iff.2
    (lintegral_mono fun x => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (h x))))

lemma erealIntegral_toENNReal_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (v : α → EReal) :
    (erealIntegral μ v).toENNReal ≤ ∫⁻ x, (v x).toENNReal ∂μ := by
  rw [erealIntegral_eq]
  refine (EReal.toENNReal_le_toENNReal (add_le_of_nonpos_right ?_)).trans (le_of_eq EReal.toENNReal_coe)
  exact (EReal.neg_le_neg_iff.2 (EReal.coe_ennreal_nonneg _)).trans (by simp)

lemma erealIntegral_dirac {α : Type*} [MeasurableSpace α] (F : α → EReal) (hF : Measurable F)
    (a : α) : erealIntegral (Measure.dirac a) F = F a := by
  rw [erealIntegral_eq, lintegral_dirac' a hF.ereal_toENNReal,
    lintegral_dirac' a (show Measurable fun x => (-F x).toENNReal from
      (measurable_ereal_neg.comp hF).ereal_toENNReal)]
  exact ereal_split _

/-- abstract inequality behind the composition lemma -/
lemma key_ineq {x y z w : ENNReal} (h : x + y = z + w) (hxw : x ≤ w) (hzy : z ≤ y) :
    (w : EReal) + -(y : EReal) ≤ (x : EReal) + -(z : EReal) ∧
      (w < ⊤ → (w : EReal) + -(y : EReal) = (x : EReal) + -(z : EReal)) := by
  by_cases hy : y = ⊤
  · subst hy
    refine ⟨by simp, fun hw => ?_⟩
    have hx : x < ⊤ := lt_of_le_of_lt hxw hw
    have hz : z = ⊤ := by
      by_contra hz
      have : z + w < ⊤ := ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hz, hw⟩
      rw [← h] at this; simp at this
    subst hz; simp
  · have hz : z ≠ ⊤ := ne_top_of_le_ne_top hy hzy
    by_cases hw : w = ⊤
    · subst hw
      have hx : x = ⊤ := by
        by_contra hx
        have : x + y < ⊤ := ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hx, lt_top_iff_ne_top.2 hy⟩
        rw [h] at this; simp at this
      subst hx
      lift y to NNReal using hy
      lift z to NNReal using hz
      simp [nn_coe, ← EReal.coe_neg]
    · have hx : x ≠ ⊤ := ne_top_of_le_ne_top hw hxw
      lift x to NNReal using hx
      lift y to NNReal using hy
      lift z to NNReal using hz
      lift w to NNReal using hw
      rw [nn_coe, nn_coe, nn_coe, nn_coe, ← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_neg,
        ← EReal.coe_add]
      have h' : (x : ℝ) + y = z + w := by exact_mod_cast h
      have : (w : ℝ) + -y = x + -z := by linarith
      rw [this]; exact ⟨le_rfl, fun _ => rfl⟩

lemma pointwise_G (a b : ENNReal) :
    ((a : EReal) + -(b : EReal)).toENNReal + b = (-((a : EReal) + -(b : EReal))).toENNReal + a ∧
    ((a : EReal) + -(b : EReal)).toENNReal ≤ a ∧ (-((a : EReal) + -(b : EReal))).toENNReal ≤ b := by
  induction a using ENNReal.recTopCoe with
  | top =>
    induction b using ENNReal.recTopCoe with
    | top => simp
    | coe b => simp [nn_coe, ← EReal.coe_neg]
  | coe a =>
    induction b using ENNReal.recTopCoe with
    | top => simp
    | coe b =>
      rw [nn_coe, nn_coe, ← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_neg,
        EReal.real_coe_toENNReal, EReal.real_coe_toENNReal,
        ← ENNReal.ofReal_coe_nnreal (p := a), ← ENNReal.ofReal_coe_nnreal (p := b)]
      have ha := a.coe_nonneg; have hb := b.coe_nonneg
      rcases le_total (a : ℝ) b with h | h
      · rw [ENNReal.ofReal_of_nonpos (by linarith), zero_add]
        refine ⟨?_, bot_le, ENNReal.ofReal_le_ofReal (by linarith)⟩
        conv_lhs => rw [show (b:ℝ) = -((a:ℝ) + -b) + a by ring]
        exact ENNReal.ofReal_add (by linarith) ha
      · rw [ENNReal.ofReal_of_nonpos (show -((a:ℝ) + -b) ≤ 0 by linarith), zero_add]
        refine ⟨?_, ENNReal.ofReal_le_ofReal (by linarith), bot_le⟩
        conv_rhs => rw [show (a:ℝ) = ((a:ℝ) + -b) + b by ring]
        exact (ENNReal.ofReal_add (by linarith) hb).symm

lemma erealIntegral_comp {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (κ : Kernel β γ) (η : Kernel α β) (F : γ → EReal) (hF : Measurable F)
    (a : α) :
    erealIntegral ((κ ∘ₖ η) a) F ≤ erealIntegral (η a) (fun b => erealIntegral (κ b) F) ∧
    (∫⁻ c, (F c).toENNReal ∂((κ ∘ₖ η) a) < ⊤ →
      erealIntegral ((κ ∘ₖ η) a) F = erealIntegral (η a) (fun b => erealIntegral (κ b) F)) ∧
    ∫⁻ b, (erealIntegral (κ b) F).toENNReal ∂(η a) ≤ ∫⁻ c, (F c).toENNReal ∂((κ ∘ₖ η) a) := by
  have hp : Measurable fun c => (F c).toENNReal := hF.ereal_toENNReal
  have hn : Measurable fun c => (-F c).toENNReal := (measurable_ereal_neg.comp hF).ereal_toENNReal
  have hpk : Measurable fun b => ∫⁻ c, (F c).toENNReal ∂(κ b) := hp.lintegral_kernel
  have hnk : Measurable fun b => ∫⁻ c, (-F c).toENNReal ∂(κ b) := hn.lintegral_kernel
  have hGp : ∫⁻ b, (erealIntegral (κ b) F).toENNReal ∂(η a) ≤ ∫⁻ c, (F c).toENNReal ∂((κ ∘ₖ η) a) := by
    rw [Kernel.lintegral_comp _ _ _ hp]
    exact lintegral_mono fun b => by
      rw [erealIntegral_eq]; exact (pointwise_G _ _).2.1
  refine ⟨?_, ?_, hGp⟩ <;> [skip; intro hfin] <;>
  · simp only [erealIntegral_eq (μ := (κ ∘ₖ η) a), Kernel.lintegral_comp _ _ _ hp,
      Kernel.lintegral_comp _ _ _ hn]
    rw [erealIntegral_eq (μ := η a)]
    simp only [erealIntegral_eq (μ := κ _)]
    have hid := lintegral_congr (μ := η a) fun b => (pointwise_G (∫⁻ c, (F c).toENNReal ∂(κ b))
      (∫⁻ c, (-F c).toENNReal ∂(κ b))).1
    rw [lintegral_add_right _ hnk, lintegral_add_right _ hpk] at hid
    have h1 := lintegral_mono (μ := η a) fun b => (pointwise_G (∫⁻ c, (F c).toENNReal ∂(κ b))
      (∫⁻ c, (-F c).toENNReal ∂(κ b))).2.1
    have h2 := lintegral_mono (μ := η a) fun b => (pointwise_G (∫⁻ c, (F c).toENNReal ∂(κ b))
      (∫⁻ c, (-F c).toENNReal ∂(κ b))).2.2
    first
    | exact (key_ineq hid h1 h2).1
    | exact (key_ineq hid h1 h2).2 (by rwa [Kernel.lintegral_comp _ _ _ hp] at hfin)


lemma shift_abs {P Nn p q s t : ENNReal} (hs : s ≠ ⊤) (ht : t ≠ ⊤)
    (h : P + (s + q) = Nn + (t + p)) (h1 : P ≤ t + p) (h2 : p ≤ P + s) (h3 : Nn ≤ s + q)
    (h4 : q ≤ Nn + t) :
    (P : EReal) + -(Nn : EReal) = ((t.toReal - s.toReal : ℝ) : EReal) + ((p : EReal) + -(q : EReal)) := by
  by_cases hq : q = ⊤
  · subst hq
    have hN : Nn = ⊤ := by
      by_contra hN
      have : Nn + t < ⊤ := ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hN, lt_top_iff_ne_top.2 ht⟩
      exact absurd (lt_of_le_of_lt h4 this) (by simp)
    subst hN; simp
  · have hN : Nn ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hs, hq⟩) h3
    by_cases hp : p = ⊤
    · subst hp
      have hP : P = ⊤ := by
        by_contra hP
        have : P + s < ⊤ := ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hP, lt_top_iff_ne_top.2 hs⟩
        exact absurd (lt_of_le_of_lt h2 this) (by simp)
      subst hP
      lift Nn to NNReal using hN
      lift q to NNReal using hq
      simp [nn_coe, ← EReal.coe_neg]
      rw [← EReal.coe_sub, EReal.coe_add_top]
    · have hP : P ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ht, hp⟩) h1
      lift P to NNReal using hP
      lift Nn to NNReal using hN
      lift p to NNReal using hp
      lift q to NNReal using hq
      lift s to NNReal using hs
      lift t to NNReal using ht
      simp only [nn_coe, ENNReal.coe_toReal]
      rw [← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_add]
      have h' : (P : ℝ) + (s + q) = Nn + (t + p) := by exact_mod_cast h
      congr 1; linarith

lemma pw_shift (c : ℝ) (e : EReal) :
    (↑c + e).toENNReal + (ENNReal.ofReal (-c) + (-e).toENNReal) =
      (-(↑c + e)).toENNReal + (ENNReal.ofReal c + e.toENNReal) ∧
    (↑c + e).toENNReal ≤ ENNReal.ofReal c + e.toENNReal ∧
    e.toENNReal ≤ (↑c + e).toENNReal + ENNReal.ofReal (-c) ∧
    (-(↑c + e)).toENNReal ≤ ENNReal.ofReal (-c) + (-e).toENNReal ∧
    (-e).toENNReal ≤ (-(↑c + e)).toENNReal + ENNReal.ofReal c := by
  induction e using EReal.rec with
  | bot => simp
  | top => simp
  | coe y =>
    rw [← EReal.coe_add, ← EReal.coe_neg, ← EReal.coe_neg]
    simp only [EReal.real_coe_toENNReal]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)]
      simp only [ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2
        ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩), ENNReal.toReal_add ENNReal.ofReal_ne_top
        ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal']
      rcases le_total c 0 with h1 | h1 <;> rcases le_total y 0 with h2 | h2 <;>
        rcases le_total (c + y) 0 with h3 | h3 <;>
        simp only [max_eq_left, max_eq_right, h1, h2, h3, neg_nonneg, neg_nonpos] <;>
        linarith
    · exact ENNReal.ofReal_add_le
    · calc ENNReal.ofReal y = ENNReal.ofReal ((c + y) + -c) := by ring_nf
        _ ≤ _ := ENNReal.ofReal_add_le
    · calc ENNReal.ofReal (-(c + y)) = ENNReal.ofReal (-c + -y) := by ring_nf
        _ ≤ _ := ENNReal.ofReal_add_le
    · calc ENNReal.ofReal (-y) = ENNReal.ofReal (-(c + y) + c) := by ring_nf
        _ ≤ _ := ENNReal.ofReal_add_le

lemma lintegral_const_add' {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (s : ENNReal) {Y : α → ENNReal} (_hY : Measurable Y) :
    ∫⁻ x, s + Y x ∂μ = s + ∫⁻ x, Y x ∂μ := by
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]

lemma lintegral_add_const' {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (s : ENNReal) {Y : α → ENNReal} (_hY : Measurable Y) :
    ∫⁻ x, Y x + s ∂μ = ∫⁻ x, Y x ∂μ + s := by
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

lemma erealIntegral_shift {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (c : ℝ) (f : α → EReal) (hf : Measurable f) :
    erealIntegral μ (fun x => (c : EReal) + f x) = (c : EReal) + erealIntegral μ f := by
  have hX : Measurable fun x => ((c : EReal) + f x).toENNReal :=
    (measurable_const.add hf).ereal_toENNReal
  have hX' : Measurable fun x => (-((c : EReal) + f x)).toENNReal :=
    (measurable_ereal_neg.comp (measurable_const.add hf)).ereal_toENNReal
  have hY : Measurable fun x => (f x).toENNReal := hf.ereal_toENNReal
  have hY' : Measurable fun x => (-f x).toENNReal := (measurable_ereal_neg.comp hf).ereal_toENNReal
  have hc : (ENNReal.ofReal c).toReal - (ENNReal.ofReal (-c)).toReal = c := by
    rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
    rcases le_total c 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  rw [erealIntegral_eq, erealIntegral_eq]
  conv_rhs => rw [← hc]
  refine shift_abs ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ?_ ?_ ?_ ?_ ?_
  · have := lintegral_congr (μ := μ) fun x => (pw_shift c (f x)).1
    rwa [lintegral_add_left hX, lintegral_add_left hX', lintegral_const_add' _ _ hY',
      lintegral_const_add' _ _ hY] at this
  · exact (lintegral_mono fun x => (pw_shift c (f x)).2.1).trans
      (le_of_eq (lintegral_const_add' _ _ hY))
  · exact (lintegral_mono fun x => (pw_shift c (f x)).2.2.1).trans
      (le_of_eq (lintegral_add_const' _ _ hX))
  · exact (lintegral_mono fun x => (pw_shift c (f x)).2.2.2.1).trans
      (le_of_eq (lintegral_const_add' _ _ hY'))
  · exact (lintegral_mono fun x => (pw_shift c (f x)).2.2.2.2).trans
      (le_of_eq (lintegral_add_const' _ _ hX'))

/-! ### Reward iteration for Markov policies -/

/-- `T_m^{f_m}` if `m < N`, identity otherwise. -/
noncomputable def Tfo (M : MarkovDecisionModel E A N) (π : Policy M) (m : ℕ) (u : E → EReal) :
    E → EReal :=
  if h : m < N then Tf M m u (π.1 ⟨m, h⟩) else u

/-- `T_{n₀}^{f} ⋯ T_{n₀+k-1}^{f} u`, defined by peeling the *last* operator. -/
noncomputable def BC (M : MarkovDecisionModel E A N) (π : Policy M) (n₀ : ℕ) :
    ℕ → (E → EReal) → (E → EReal)
  | 0, u => u
  | k + 1, u => BC M π n₀ k (Tfo M π (n₀ + k) u)

lemma BC_succ (M : MarkovDecisionModel E A N) (π : Policy M) :
    ∀ (k m : ℕ) (u : E → EReal), BC M π m (k + 1) u = Tfo M π m (BC M π (m + 1) k u) := by
  intro k
  induction k with
  | zero => intro m u; simp [BC]
  | succ k ih =>
    intro m u
    rw [BC, ih, BC, show m + 1 + k = m + (k + 1) by omega]

lemma measurable_Tf (M : MarkovDecisionModel E A N) {m : ℕ} (hm : m < N) {u : E → EReal}
    (hu : Measurable u) {f : E → A} (hf : Measurable f) : Measurable (Tf M m u f) := by
  have hxf : Measurable fun x => (x, f x) := measurable_id.prodMk hf
  have hp : Measurable fun x' => (u x' ⊔ 0).toENNReal := (hu.max measurable_const).ereal_toENNReal
  have hn : Measurable fun x' => ((-u x') ⊔ 0).toENNReal :=
    ((measurable_ereal_neg.comp hu).max measurable_const).ereal_toENNReal
  unfold Tf L erealIntegral
  refine (measurable_coe_real_ereal.comp ((M.hr_meas m hm).comp hxf)).add
    ((measurable_coe_ennreal_ereal.comp ((hp.lintegral_kernel (κ := M.Q m)).comp hxf)).add
      (measurable_ereal_neg.comp
        (measurable_coe_ennreal_ereal.comp ((hn.lintegral_kernel (κ := M.Q m)).comp hxf))))

lemma S (M : MarkovDecisionModel E A N) (π : Policy M) (n₀ : ℕ) :
    ∀ k, n₀ + k ≤ N → ∀ u : E → EReal, Measurable u → ∀ h₀ : Hist E A 0,
      ∫⁻ h, ((pathReward M.r (fun _ => 0) n₀ 0 k h : EReal) + u (histState (0 + k) h)).toENNReal
        ∂(pathKernel M n₀ 0 (markovRule π n₀) k h₀) < ⊤ →
      erealIntegral (pathKernel M n₀ 0 (markovRule π n₀) k h₀)
        (fun h => (pathReward M.r (fun _ => 0) n₀ 0 k h : EReal) + u (histState (0 + k) h)) =
        BC M π n₀ k u (histState 0 h₀) := by
  intro k
  induction k with
  | zero =>
    intro _ u hu h₀ _
    rw [show pathKernel M n₀ 0 (markovRule π n₀) 0 = Kernel.id from rfl, Kernel.id_apply,
      erealIntegral_dirac]
    · simp [pathReward, BC]
    · exact (measurable_coe_real_ereal.comp (measurable_pathReward _ _ _ _ _
        (fun i hi => absurd hi (Nat.not_lt_zero _)) measurable_const)).add
        (hu.comp (measurable_histState _))
  | succ k ih =>
    intro hk u hu h₀ hint
    have hk' : n₀ + k < N := by omega
    have : IsMarkovKernel (M.Q (n₀ + k)) := ⟨fun xa => M.hQ_prob _ hk' xa⟩
    set f := π.1 ⟨n₀ + k, hk'⟩ with hf_def
    have hfm : Measurable f := (π.2 ⟨n₀ + k, hk'⟩).1
    have hF : Measurable (fun h : Hist E A (0 + (k + 1)) =>
        (pathReward M.r (fun _ => 0) n₀ 0 (k + 1) h : EReal) + u (histState (0 + (k + 1)) h)) :=
      (measurable_coe_real_ereal.comp (measurable_pathReward _ _ _ _ _
        (fun i hi => M.hr_meas _ (by omega)) measurable_const)).add
        (hu.comp (measurable_histState _))
    rw [show pathKernel M n₀ 0 (markovRule π n₀) (k + 1) =
        stepKernel M (n₀ + k) (0 + k) (markovRule π n₀ k hk').1 (markovRule π n₀ k hk').2 ∘ₖ
          pathKernel M n₀ 0 (markovRule π n₀) k from dif_pos hk'] at hint ⊢
    obtain ⟨-, heq, hGp⟩ := erealIntegral_comp (stepKernel M (n₀ + k) (0 + k)
      (markovRule π n₀ k hk').1 (markovRule π n₀ k hk').2)
      (pathKernel M n₀ 0 (markovRule π n₀) k) _ hF h₀
    rw [heq hint]
    -- identify the inner integral
    have hinner : (fun h => erealIntegral (stepKernel M (n₀ + k) (0 + k)
        (markovRule π n₀ k hk').1 (markovRule π n₀ k hk').2 h)
        (fun h => (pathReward M.r (fun _ => 0) n₀ 0 (k + 1) h : EReal) +
          u (histState (0 + (k + 1)) h))) =
        fun h => (pathReward M.r (fun _ => 0) n₀ 0 k h : EReal) +
          Tf M (n₀ + k) u f (histState (0 + k) h) := by
      funext h
      have hp := hF.ereal_toENNReal
      have hn := (measurable_ereal_neg.comp hF).ereal_toENNReal
      rw [erealIntegral_eq]
      erw [lintegral_stepKernel M (n₀ + k) (0 + k) hk' _ _ _ hp,
        lintegral_stepKernel M (n₀ + k) (0 + k) hk' _ _ _ hn]
      have key : erealIntegral (M.Q (n₀ + k) (histState (0 + k) h, f (histState (0 + k) h)))
          (fun x' => (((pathReward M.r (fun _ => 0) n₀ 0 k h +
            M.r (n₀ + k) (histState (0 + k) h, f (histState (0 + k) h)) + 0 : ℝ)) : EReal) + u x') =
          (pathReward M.r (fun _ => 0) n₀ 0 k h : EReal) + Tf M (n₀ + k) u f (histState (0 + k) h) := by
        rw [erealIntegral_shift _ _ _ hu]
        simp only [Tf, L, add_zero, EReal.coe_add, add_assoc]
      rw [erealIntegral_eq] at key
      exact key
    have hinner' := congrFun hinner
    refine Eq.trans (congrArg (erealIntegral (pathKernel M n₀ 0 (markovRule π n₀) k h₀)) hinner) ?_
    have hTfo : Tfo M π (n₀ + k) u = Tf M (n₀ + k) u f := by simp [Tfo, hk', hf_def]
    rw [BC, hTfo]
    refine ih (by omega) _ (measurable_Tf M hk' hu hfm) h₀ (lt_of_le_of_lt (le_trans
      (le_of_eq (lintegral_congr fun h => congrArg EReal.toENNReal (hinner' h).symm)) hGp) hint)

lemma pathReward_le (r r' : ℕ → E × A → ℝ) (hr : ∀ i xa, r i xa ≤ r' i xa) (n₀ j₀ : ℕ) :
    ∀ k (g g' : E → ℝ), (∀ y, g y ≤ g' y) → ∀ h : Hist E A (j₀ + k),
      pathReward r g n₀ j₀ k h ≤ pathReward r' g' n₀ j₀ k h := by
  intro k
  induction k with
  | zero => intro g g' hg h; exact hg _
  | succ k ih =>
    intro g g' hg h
    obtain ⟨h1, a, x⟩ := h
    simp only [pathReward]
    have := ih (fun _ => 0) (fun _ => 0) (fun _ => le_rfl) h1
    have := hr (n₀ + k) (histState (j₀ + k) h1, a)
    have := hg x
    linarith

lemma Vpi_eq_BC (M : MarkovDecisionModel E A N) (hAN : IntegrabilityAssumption M) (π : Policy M)
    (n : ℕ) (hn : n ≤ N) : Vpi M π n = BC M π n (N - n) (fun x => (M.g x : EReal)) := by
  funext x
  have hfun : (fun h => (pathReward M.r M.g n 0 (N - n) h : EReal)) =
      fun h => (pathReward M.r (fun _ => 0) n 0 (N - n) h : EReal) +
        (fun x => (M.g x : EReal)) (histState (0 + (N - n)) h) := by
    funext h; rw [pathReward_split]; simp
  unfold Vpi
  rw [hfun]
  refine S M π n (N - n) (by omega) _ (measurable_coe_real_ereal.comp M.hg_meas) x ?_
  refine lt_of_le_of_lt ?_ (hAN n hn x)
  refine le_trans ?_ (le_iSup (fun π : Policy M => ∫⁻ h, ENNReal.ofReal
    (pathReward (fun k xa => max (M.r k xa) 0) (fun y => max (M.g y) 0) n 0 (N - n) h)
    ∂(pathKernel M n 0 (markovRule π n) (N - n) x)) π)
  refine lintegral_mono fun h => ?_
  simp only [Function.comp_apply]
  rw [← EReal.coe_add, ← pathReward_split, EReal.real_coe_toENNReal]
  exact ENNReal.ofReal_le_ofReal (pathReward_le _ _ (fun _ _ => le_max_left _ _) _ _ _ _ _
    (fun _ => le_max_left _ _) _)

lemma reward_iter (M : MarkovDecisionModel E A N) (hAN : IntegrabilityAssumption M) (π : Policy M)
    (n : ℕ) (hn : n < N) : Vpi M π n = Tf M n (Vpi M π (n + 1)) (π.1 ⟨n, hn⟩) := by
  rw [Vpi_eq_BC M hAN π n hn.le, Vpi_eq_BC M hAN π (n + 1) hn,
    show N - n = (N - (n + 1)) + 1 by omega, BC_succ]
  simp [Tfo, hn]

lemma Vpi_N (M : MarkovDecisionModel E A N) (hAN : IntegrabilityAssumption M) (π : Policy M) :
    Vpi M π N = fun x => (M.g x : EReal) := by
  rw [Vpi_eq_BC M hAN π N le_rfl, Nat.sub_self]; rfl

lemma Tf_mono (M : MarkovDecisionModel E A N) (n : ℕ) {v w : E → EReal} (h : ∀ x, v x ≤ w x)
    (f : E → A) (x : E) : Tf M n v f x ≤ Tf M n w f x := by
  unfold Tf L
  exact add_le_add_right (erealIntegral_mono _ h) _

lemma Tf_le_T (M : MarkovDecisionModel E A N) (n : ℕ) (v : E → EReal) (f : E → A) (x : E)
    (hx : (x, f x) ∈ M.D n) : Tf M n v f x ≤ T M n v x :=
  le_iSup₂ (f := fun a (_ : a ∈ M.Dx n x) => L M n v (x, a)) (f x) hx

end Thm238Sol

open Thm238Sol BauerleRiederMDP.FiniteHorizon in
theorem solution {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (hAN : IntegrabilityAssumption M)
    (IMs : ℕ → Set (E → EReal)) (Deltas : ℕ → Set (E → A))
    (hSAN : StructureAssumption M IMs Deltas) :
    (∀ n ≤ N, V M n ∈ IMs n) ∧
    (∀ x, V M N x = (M.g x : EReal)) ∧
    (∀ n < N, ∀ x, V M n x =
      ⨆ a ∈ M.Dx n x, ((M.r n (x, a) : EReal) + erealIntegral (M.Q n (x, a)) (V M (n + 1)))) ∧
    (∀ n ≤ N, V M n = TChain M (N - n) n (fun x => (M.g x : EReal))) ∧
    (∀ n < N, ∃ f ∈ Deltas n, IsMaximizer M n (V M (n + 1)) f) ∧
    (∀ π : Policy M, (∀ n : Fin N, IsMaximizer M n (V M (n + 1)) (π.1 n)) → IsOptimal M π) := by
  obtain ⟨-, -, hg, hT, hmax⟩ := hSAN
  set g' : E → EReal := fun x => (M.g x : EReal) with hg'
  let w : ℕ → E → EReal := fun n => TChain M (N - n) n g'
  have w_N : w N = g' := by simp [w, TChain]
  have w_succ : ∀ n < N, w n = T M n (w (n + 1)) := by
    intro n hn
    simp only [w]
    rw [show N - n = (N - (n + 1)) + 1 by omega]
    rfl
  -- downward induction principle
  have down : ∀ P : ℕ → Prop, P N → (∀ n < N, P (n + 1) → P n) → ∀ n ≤ N, P n := by
    intro P hN hstep
    have : ∀ d n, n + d = N → P n := by
      intro d
      induction d with
      | zero => intro n hn; simp at hn; subst hn; exact hN
      | succ d ih => intro n hn; exact hstep n (by omega) (ih (n + 1) (by omega))
    intro n hn; exact this (N - n) n (by omega)
  have w_mem : ∀ n ≤ N, w n ∈ IMs n :=
    down _ (by rw [w_N]; exact hg) fun n hn ih => by
      rw [w_succ n hn]; exact (hT n hn _ ih).2
  have upper : ∀ π : Policy M, ∀ n ≤ N, ∀ x, Vpi M π n x ≤ w n x := by
    intro π
    refine down _ (fun x => by rw [Vpi_N M hAN π, w_N]) fun n hn ih x => ?_
    rw [reward_iter M hAN π n hn, w_succ n hn]
    exact (Tf_mono M n ih _ x).trans (Tf_le_T M n _ _ x ((π.2 ⟨n, hn⟩).2 x))
  have exact_ : ∀ π : Policy M, (∀ n : Fin N, IsMaximizer M n (w (n + 1)) (π.1 n)) →
      ∀ n ≤ N, Vpi M π n = w n := by
    intro π hπ
    refine down _ (by rw [Vpi_N M hAN π, w_N]) fun n hn ih => ?_
    rw [reward_iter M hAN π n hn, ih, w_succ n hn]
    exact (hπ ⟨n, hn⟩).2
  have hsel : ∀ n : Fin N, ∃ f ∈ Deltas n, IsMaximizer M n (w (n + 1)) f :=
    fun n => hmax n n.2 _ (w_mem (n + 1) (by omega))
  choose f _ hfM using hsel
  let πs : Policy M := ⟨f, fun n => (hfM n).1⟩
  have V_eq : ∀ n ≤ N, V M n = w n := by
    intro n hn
    funext x
    refine le_antisymm (iSup_le fun π => upper π n hn x) ?_
    rw [← exact_ πs hfM n hn]
    exact le_iSup (fun π : Policy M => Vpi M π n x) πs
  refine ⟨fun n hn => V_eq n hn ▸ w_mem n hn, fun x => by rw [V_eq N le_rfl, w_N], ?_,
    fun n hn => V_eq n hn, ?_, ?_⟩
  · intro n hn x
    rw [V_eq n hn.le, V_eq (n + 1) hn, w_succ n hn]
    rfl
  · intro n hn
    rw [V_eq (n + 1) hn]
    exact hmax n hn _ (w_mem (n + 1) hn)
  · intro π hπ x
    have hπ' : ∀ n : Fin N, IsMaximizer M n (w (n + 1)) (π.1 n) := fun n => by
      rw [← V_eq (n + 1) n.2]; exact hπ n
    rw [exact_ π hπ' 0 (Nat.zero_le _), V_eq 0 (Nat.zero_le _)]
