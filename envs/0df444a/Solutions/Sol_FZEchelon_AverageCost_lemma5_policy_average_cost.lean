-- Prove2me | solution 1 for FZEchelon.AverageCost.lemma5_policy_average_cost
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T07:38:43.237682+00:00
-- url     : https://prove2.me/submissions/83f91175-d6f3-449e-b259-2faffcf92ebe

import Mathlib
import Definitions.Def_FZEchelon_AverageCost_Policies
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_FZEchelon_AverageCost_Model
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open MeasureTheory Filter

namespace FZEchelon.AverageCost

namespace Policy

variable {S A : Type*}

lemma action_measurable [MeasurableSpace S] [MeasurableSpace A]
    (π : Policy S A) (hπ : π.IsMeasurable) (s : S) (n : ℕ) :
    Measurable (fun ω : ℕ → ℝ => π.action s ω n) := by
  exact (hπ n).comp (measurable_const.prodMk
    (measurable_pi_lambda _ (fun j => measurable_pi_apply (j : ℕ))))

lemma path_measurable [MeasurableSpace S] [MeasurableSpace A]
    (f : S → A → ℝ → S)
    (hf : Measurable (fun q : S × A × ℝ => f q.1 q.2.1 q.2.2))
    (π : Policy S A) (hπ : π.IsMeasurable) (s : S) (n : ℕ) :
    Measurable (fun ω : ℕ → ℝ => Policy.path f π s ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact hf.comp (ih.prodMk ((action_measurable π hπ s n).prodMk (measurable_pi_apply n)))

lemma path_ofStationary (f : S → A → ℝ → S) (σ : S → A) (s : S)
    (ω : ℕ → ℝ) (n : ℕ) :
    path f (ofStationary f σ) s ω n = stationaryState f σ s n (fun j => ω j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change f (path f (ofStationary f σ) s ω n)
      (σ (stationaryState f σ s n (fun j => ω j))) (ω n) =
      f (stationaryState f σ s n (fun j => ω j))
        (σ (stationaryState f σ s n (fun j => ω j))) (ω n)
    rw [ih]

lemma action_ofStationary (f : S → A → ℝ → S) (σ : S → A) (s : S)
    (ω : ℕ → ℝ) (n : ℕ) :
    (ofStationary f σ).action s ω n = σ (path f (ofStationary f σ) s ω n) := by
  rw [path_ofStationary]
  rfl

lemma stationaryState_measurable [MeasurableSpace S] [MeasurableSpace A]
    (f : S → A → ℝ → S) (σ : S → A)
    (hf : Measurable (fun q : S × A × ℝ => f q.1 q.2.1 q.2.2))
    (hσ : Measurable σ) (n : ℕ) :
    Measurable (fun q : S × (Fin n → ℝ) => stationaryState f σ q.1 n q.2) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    have hi : Measurable (fun q : S × (Fin (n + 1) → ℝ) => (q.1, Fin.init q.2)) :=
      measurable_fst.prodMk (measurable_pi_lambda _ (fun j =>
        (measurable_pi_apply j.castSucc).comp measurable_snd))
    have hs := ih.comp hi
    exact hf.comp (hs.prodMk ((hσ.comp hs).prodMk
      ((measurable_pi_apply (Fin.last n)).comp measurable_snd)))

lemma ofStationary_measurable [MeasurableSpace S] [MeasurableSpace A]
    (f : S → A → ℝ → S) (σ : S → A)
    (hf : Measurable (fun q : S × A × ℝ => f q.1 q.2.1 q.2.2))
    (hσ : Measurable σ) : IsMeasurable (ofStationary f σ) := by
  intro n
  exact hσ.comp (stationaryState_measurable f σ hf hσ n)

end Policy

namespace Analysis

variable (m : Model)

lemma piStar_action (σ : DepotState m.L → ℝ) (a : ℝ)
    (s : SysState m.L) (ω : ℕ → ℝ) (n : ℕ) :
    (m.piStar σ a).action s ω n =
      m.sigmaStar σ a (Policy.path m.sysNext (m.piStar σ a) s ω n) := by
  unfold Model.piStar
  exact Policy.action_ofStationary _ _ _ _ _

lemma depotStationary_action (σ : DepotState m.L → ℝ)
    (p : DepotState m.L) (ω : ℕ → ℝ) (n : ℕ) :
    (m.depotStationary σ).action p ω n =
      σ (Policy.path m.depotNext (m.depotStationary σ) p ω n) := by
  unfold Model.depotStationary
  exact Policy.action_ofStationary _ _ _ _ _

lemma arrival_nonneg {L : ℕ} (yh : Fin L → ℝ) (y : ℝ)
    (hh : ∀ k, 0 ≤ yh k) (hy : 0 ≤ y) : 0 ≤ arrival yh y := by
  unfold arrival
  split
  · exact hh _
  · exact hy

lemma shift_nonneg {L : ℕ} (yh : Fin L → ℝ) (y : ℝ)
    (hh : ∀ k, 0 ≤ yh k) (hy : 0 ≤ y) : ∀ k, 0 ≤ shift yh y k := by
  intro k
  unfold shift
  split
  · exact hy
  · exact hh _

lemma domain_next (s : SysState m.L) (a : ℝ × ℝ) (u : ℝ)
    (hs : InDomain s) (ha : m.SysFeasible s a) : InDomain (m.sysNext s a u) := by
  exact ⟨shift_nonneg s.1 a.1 hs.1 ha.1, sub_le_sub_right ha.2.2 u⟩

lemma admissible_path_domain (π : Policy (SysState m.L) (ℝ × ℝ))
    (s : SysState m.L) (hs : InDomain s) (hπ : m.SysAdmissible π s)
    (ω : ℕ → ℝ) (n : ℕ) : InDomain (Policy.path m.sysNext π s ω n) := by
  induction n with
  | zero => exact hs
  | succ n ih => exact domain_next m _ _ _ ih (hπ.2 ω n)

lemma sigmaStar_feasible (σ : DepotState m.L → ℝ) (a : ℝ)
    (hσ : ∀ p, 0 ≤ σ p) (s : SysState m.L) (hs : InDomain s) :
    m.SysFeasible s (m.sigmaStar σ a s) := by
  have ha := arrival_nonneg s.1 (σ (s.1, s.2.1)) hs.1 (hσ _)
  change 0 ≤ σ (s.1, s.2.1) ∧
    0 ≤ max 0 (min a (s.2.1 + arrival s.1 (σ (s.1, s.2.1))) - s.2.2) ∧
    s.2.2 + max 0 (min a (s.2.1 + arrival s.1 (σ (s.1, s.2.1))) - s.2.2) ≤
      s.2.1 + arrival s.1 (σ (s.1, s.2.1))
  refine ⟨hσ _, le_max_left _ _, ?_⟩
  rw [add_max]
  apply max_le
  · linarith [hs.2]
  · linarith [min_le_right a (s.2.1 + arrival s.1 (σ (s.1, s.2.1)))]

lemma arrival_measurable {L : ℕ} :
    Measurable (fun p : (Fin L → ℝ) × ℝ => arrival p.1 p.2) := by
  unfold arrival
  split
  · exact (measurable_pi_apply _).comp measurable_fst
  · exact measurable_snd

lemma shift_measurable {L : ℕ} :
    Measurable (fun p : (Fin L → ℝ) × ℝ => shift p.1 p.2) := by
  apply measurable_pi_lambda
  intro k
  unfold shift
  split
  · exact measurable_snd
  · exact (measurable_pi_apply _).comp measurable_fst

lemma sigmaStar_measurable (σ : DepotState m.L → ℝ) (a : ℝ)
    (hσ : Measurable σ) : Measurable (m.sigmaStar σ a) := by
  have hp : Measurable (fun s : SysState m.L => (s.1, s.2.1)) :=
    measurable_fst.prodMk measurable_snd.fst
  have hy := hσ.comp hp
  have ha : Measurable (fun s : SysState m.L => arrival s.1 (σ (s.1, s.2.1))) :=
    arrival_measurable.comp (measurable_fst.prodMk hy)
  exact hy.prodMk (measurable_const.max
    ((measurable_const.min (measurable_snd.fst.add ha)).sub measurable_snd.snd))

lemma sysNext_measurable : Measurable (fun q : SysState m.L × (ℝ × ℝ) × ℝ =>
    m.sysNext q.1 q.2.1 q.2.2) := by
  have hshift : Measurable (fun q : SysState m.L × (ℝ × ℝ) × ℝ =>
      shift q.1.1 q.2.1.1) :=
    shift_measurable.comp (measurable_fst.fst.prodMk measurable_snd.fst.fst)
  have harrival : Measurable (fun q : SysState m.L × (ℝ × ℝ) × ℝ =>
      arrival q.1.1 q.2.1.1) :=
    arrival_measurable.comp (measurable_fst.fst.prodMk measurable_snd.fst.fst)
  exact hshift.prodMk
    (((measurable_fst.snd.fst.add harrival).sub measurable_snd.snd).prodMk
      ((measurable_fst.snd.snd.add measurable_snd.fst.snd).sub measurable_snd.snd))

lemma depotNext_measurable : Measurable (fun q : DepotState m.L × ℝ × ℝ =>
    m.depotNext q.1 q.2.1 q.2.2) := by
  have hshift : Measurable (fun q : DepotState m.L × ℝ × ℝ => shift q.1.1 q.2.1) :=
    shift_measurable.comp (measurable_fst.fst.prodMk measurable_snd.fst)
  have harrival : Measurable (fun q : DepotState m.L × ℝ × ℝ => arrival q.1.1 q.2.1) :=
    arrival_measurable.comp (measurable_fst.fst.prodMk measurable_snd.fst)
  exact hshift.prodMk ((measurable_fst.snd.add harrival).sub measurable_snd.snd)

lemma piStar_domain (σ : DepotState m.L → ℝ) (a : ℝ) (hσ : ∀ p, 0 ≤ σ p)
    (s : SysState m.L) (hs : InDomain s) (ω : ℕ → ℝ) (n : ℕ) :
    InDomain (Policy.path m.sysNext (m.piStar σ a) s ω n) := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    change InDomain (m.sysNext _ ((m.piStar σ a).action s ω n) (ω n))
    rw [piStar_action]
    exact domain_next m _ _ _ ih (sigmaStar_feasible m σ a hσ _ ih)

lemma piStar_admissible (σ : DepotState m.L → ℝ) (a : ℝ)
    (hσm : Measurable σ) (hσ : ∀ p, 0 ≤ σ p) (s : SysState m.L) (hs : InDomain s) :
    m.SysAdmissible (m.piStar σ a) s := by
  refine ⟨Policy.ofStationary_measurable _ _ (sysNext_measurable m)
    (sigmaStar_measurable m σ a hσm), ?_⟩
  intro ω n
  rw [piStar_action]
  exact sigmaStar_feasible m σ a hσ _ (piStar_domain m σ a hσ s hs ω n)

lemma depotStationary_admissible (σ : DepotState m.L → ℝ)
    (hσm : Measurable σ) (hσ : ∀ p, 0 ≤ σ p) (p : DepotState m.L) :
    m.DepotAdmissible (m.depotStationary σ) p := by
  refine ⟨Policy.ofStationary_measurable _ _ (depotNext_measurable m) hσm, ?_⟩
  intro ω n
  change 0 ≤ (m.depotStationary σ).action p ω n
  rw [Model.depotStationary, Policy.action_ofStationary]
  exact hσ _

/-- Forget the shipment action while retaining the original initial outlet inventory. -/
def projectOrders (x : ℝ) (π : Policy (SysState m.L) (ℝ × ℝ)) :
    Policy (DepotState m.L) ℝ :=
  fun k q => (π k ((q.1.1, q.1.2, x), q.2)).1

lemma projectOrders_measurable (x : ℝ) (π : Policy (SysState m.L) (ℝ × ℝ))
    (hπ : π.IsMeasurable) : (projectOrders m x π).IsMeasurable := by
  intro n
  exact (hπ n).fst.comp
    ((measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_const)).prodMk
      measurable_snd)

lemma projectOrders_action (π : Policy (SysState m.L) (ℝ × ℝ))
    (s : SysState m.L) (ω : ℕ → ℝ) (n : ℕ) :
    (projectOrders m s.2.2 π).action (s.1, s.2.1) ω n = (π.action s ω n).1 := by
  rfl

lemma projectOrders_path (π : Policy (SysState m.L) (ℝ × ℝ))
    (s : SysState m.L) (ω : ℕ → ℝ) (n : ℕ) :
    Policy.path m.depotNext (projectOrders m s.2.2 π) (s.1, s.2.1) ω n =
      ((Policy.path m.sysNext π s ω n).1, (Policy.path m.sysNext π s ω n).2.1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Policy.path, projectOrders_action, ih, Model.depotNext, Model.sysNext]

lemma projectOrders_admissible (π : Policy (SysState m.L) (ℝ × ℝ))
    (s : SysState m.L) (hπ : m.SysAdmissible π s) :
    m.DepotAdmissible (projectOrders m s.2.2 π) (s.1, s.2.1) := by
  refine ⟨projectOrders_measurable m _ π hπ.1, ?_⟩
  intro ω n
  exact (hπ.2 ω n).1

lemma shipStar_post (a : ℝ) (s : SysState m.L) (y : ℝ) :
    s.2.2 + m.shipStar a s y = max s.2.2 (min a (s.2.1 + arrival s.1 y)) := by
  unfold Model.shipStar
  rw [add_max]
  congr 1 <;> ring

lemma post_le_critical_or_initial (a x w : ℝ) :
    max x (min a w) ≤ max a x := by
  exact max_le (le_max_right _ _) ((min_le_left _ _).trans (le_max_left _ _))

lemma transient_step (a x b w u : ℝ) (hu : 0 ≤ u) (hx : x ≤ max a b) :
    max x (min a w) - u ≤ max a (b - u) := by
  have hmax : max x (min a w) ≤ max a b :=
    (post_le_critical_or_initial a x w).trans (max_le (le_max_left _ _) hx)
  calc
    max x (min a w) - u ≤ max a b - u := sub_le_sub_right hmax u
    _ = max (a - u) (b - u) := (max_sub_sub_right a b u).symm
    _ ≤ max a (b - u) := max_le_max (sub_le_self _ hu) le_rfl

lemma piStar_outlet_bound (σ : DepotState m.L → ℝ) (a : ℝ)
    (s : SysState m.L) (ω : ℕ → ℝ) (hω : ∀ k, 0 ≤ ω k) (n : ℕ) :
    (Policy.path m.sysNext (m.piStar σ a) s ω n).2.2 ≤
      max a (s.2.2 - ∑ k ∈ Finset.range n, ω k) := by
  induction n with
  | zero => simpa [Policy.path] using le_max_right a s.2.2
  | succ n ih =>
    change (Policy.path m.sysNext (m.piStar σ a) s ω n).2.2 +
      ((m.piStar σ a).action s ω n).2 - ω n ≤ _
    rw [piStar_action]
    change (Policy.path m.sysNext (m.piStar σ a) s ω n).2.2 +
      m.shipStar a _ (σ _) - ω n ≤ _
    rw [shipStar_post, Finset.sum_range_succ]
    simpa only [sub_add_eq_sub_sub] using transient_step a _ _ _ (ω n) (hω n) ih

end Analysis
end FZEchelon.AverageCost

open MeasureTheory

namespace FZEchelon.AverageCost.Analysis

lemma convex_affine (a b : ℝ) : ConvexOn ℝ Set.univ (fun x : ℝ => a * x + b) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy c d hc hd hcd
  simp only [smul_eq_mul]
  have hb := congrArg (fun z : ℝ => z * b) hcd
  nlinarith

lemma convex_integral {ν : Measure ℝ} (f : ℝ → ℝ → ℝ)
    (hi : ∀ x, Integrable (f x) ν) (hc : ∀ t, ConvexOn ℝ Set.univ (fun x => f x t)) :
    ConvexOn ℝ Set.univ (fun x => ∫ t, f x t ∂ν) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have h := integral_mono (hi (a * x + b * y))
    (((hi x).const_mul a).add ((hi y).const_mul b))
    (fun t => (hc t).2 hx hy ha hb hab)
  simpa only [Pi.add_apply, integral_add ((hi x).const_mul a) ((hi y).const_mul b),
    integral_const_mul, smul_eq_mul] using h

lemma hinge_integrable {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : Integrable id ν) (x : ℝ) :
    Integrable (fun t => max (t - x) 0) ν ∧
      Integrable (fun t => max (x - t) 0) ν := by
  exact ⟨(hν.sub (integrable_const x)).sup (integrable_const 0),
    ((integrable_const x).sub hν).sup (integrable_const 0)⟩

lemma hinge_integral_convex {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : Integrable id ν) :
    ConvexOn ℝ Set.univ (fun x => ∫ t, max (t - x) 0 ∂ν) ∧
      ConvexOn ℝ Set.univ (fun x => ∫ t, max (x - t) 0 ∂ν) := by
  constructor
  · apply convex_integral _ (fun x => (hinge_integrable hν x).1)
    intro t
    have heq : (fun x : ℝ => max (t - x) 0) =
        (fun x => (-1 : ℝ) * x + t) ⊔ (fun _ => 0) := by
      funext x
      change max (t - x) 0 = max (-1 * x + t) 0
      congr 1
      ring
    rw [heq]
    exact (convex_affine (-1) t).sup (convexOn_const 0 convex_univ)
  · apply convex_integral _ (fun x => (hinge_integrable hν x).2)
    intro t
    have heq : (fun x : ℝ => max (x - t) 0) =
        (fun x => (1 : ℝ) * x + (-t)) ⊔ (fun _ => 0) := by
      funext x
      change max (x - t) 0 = max (1 * x + (-t)) 0
      congr 1
      ring
    rw [heq]
    exact (convex_affine 1 (-t)).sup (convexOn_const 0 convex_univ)

lemma hinge_integral_lipschitz {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : Integrable id ν) (x y : ℝ) :
    |(∫ t, max (t - x) 0 ∂ν) - ∫ t, max (t - y) 0 ∂ν| ≤ |x - y| ∧
      |(∫ t, max (x - t) 0 ∂ν) - ∫ t, max (y - t) 0 ∂ν| ≤ |x - y| := by
  constructor
  · rw [← integral_sub (hinge_integrable hν x).1 (hinge_integrable hν y).1]
    have h := norm_integral_le_of_norm_le_const (μ := ν)
      (f := fun t => max (t - x) 0 - max (t - y) 0)
      (C := |x - y|) (Filter.Eventually.of_forall (fun t => by
        simpa only [Real.norm_eq_abs, sub_sub_sub_cancel_left, abs_sub_comm] using
          abs_max_sub_max_le_abs (t - x) (t - y) 0))
    simpa using h
  · rw [← integral_sub (hinge_integrable hν x).2 (hinge_integrable hν y).2]
    have h := norm_integral_le_of_norm_le_const (μ := ν)
      (f := fun t => max (x - t) 0 - max (y - t) 0)
      (C := |x - y|) (Filter.Eventually.of_forall (fun t => by
        simpa only [Real.norm_eq_abs, sub_sub_sub_cancel_right] using
          abs_max_sub_max_le_abs (x - t) (y - t) 0))
    simpa using h

variable (m : Model)

lemma demandLaw_probability [IsProbabilityMeasure m.ν] (n : ℕ) :
    IsProbabilityMeasure (m.demandLaw n) := by
  apply Measure.isProbabilityMeasure_map
  exact (show Measurable (fun t : Fin n → ℝ => ∑ j, t j) from by fun_prop).aemeasurable

lemma demandLaw_integrable [IsProbabilityMeasure m.ν]
    (hν : Integrable id m.ν) (n : ℕ) : Integrable id (m.demandLaw n) := by
  have hm : Measurable (fun t : Fin n → ℝ => ∑ j, t j) := by fun_prop
  apply (integrable_map_measure aestronglyMeasurable_id hm.aemeasurable).2
  have hs : Integrable (fun t : Fin n → ℝ => ∑ j, t j)
      (Measure.pi (fun _ : Fin n => m.ν)) :=
    integrable_finsetSum Finset.univ (fun j _ =>
      integrable_eval (i := j) (μ := fun _ : Fin n => m.ν) hν)
  exact hs

lemma demandLaw_nonneg [IsProbabilityMeasure m.ν]
    (hν0 : m.ν (Set.Iio 0) = 0) (n : ℕ) : ∀ᵐ t ∂m.demandLaw n, 0 ≤ t := by
  have hν : ∀ᵐ t ∂m.ν, 0 ≤ t := by simpa only [ae_iff, not_le, Set.Iio] using hν0
  have hcoords : ∀ᵐ t ∂Measure.pi (fun _ : Fin n => m.ν), ∀ j, 0 ≤ t j := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval (fun _ : Fin n => m.ν) j).quasiMeasurePreserving.tendsto_ae hν
  apply (ae_map_iff (show AEMeasurable (fun t : Fin n → ℝ => ∑ j, t j)
    (Measure.pi (fun _ : Fin n => m.ν)) from (by fun_prop)) measurableSet_Ici).2
  filter_upwards [hcoords] with t ht
  exact Finset.sum_nonneg (fun j _ => ht j)

lemma R_of_nonpos (hα : m.α = 1) [IsProbabilityMeasure m.ν]
    (hν0 : m.ν (Set.Iio 0) = 0) (hνint : Integrable id m.ν)
    (x : ℝ) (hx : x ≤ 0) : m.R x = m.R 0 - (m.hd + m.pr) * x := by
  letI := demandLaw_probability m (m.l + 1)
  have hi := demandLaw_integrable m hνint (m.l + 1)
  have hn := demandLaw_nonneg m hν0 (m.l + 1)
  have hminus (y : ℝ) (hy : y ≤ 0) :
      (∫ t, max (t - y) 0 ∂m.demandLaw (m.l + 1)) =
        (∫ t, t ∂m.demandLaw (m.l + 1)) - y := by
    calc
      _ = ∫ t, t - y ∂m.demandLaw (m.l + 1) := by
        apply integral_congr_ae
        filter_upwards [hn] with t ht
        exact max_eq_left (by linarith)
      _ = _ := by
        have hit : Integrable (fun t : ℝ => t) (m.demandLaw (m.l + 1)) := hi
        rw [integral_sub hit (integrable_const y)]
        simp
  have hplus (y : ℝ) (hy : y ≤ 0) :
      (∫ t, max (y - t) 0 ∂m.demandLaw (m.l + 1)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hn] with t ht
    exact max_eq_right (by linarith)
  simp only [Model.R, hα, one_pow, one_mul, hminus x hx, hminus 0 le_rfl,
    hplus x hx, hplus 0 le_rfl]
  ring

lemma minimizer_nonneg (hα : m.α = 1) (hrate : 0 < m.hd + m.pr)
    [IsProbabilityMeasure m.ν] (hν0 : m.ν (Set.Iio 0) = 0)
    (hνint : Integrable id m.ν) (a : ℝ) (ha : ∀ x, m.R a ≤ m.R x) : 0 ≤ a := by
  by_contra h
  have han : a < 0 := lt_of_not_ge h
  have hmin := ha 0
  rw [R_of_nonpos m hα hν0 hνint a han.le] at hmin
  nlinarith

lemma R_convex (hα : m.α = 1) (hpr : 0 ≤ m.pr) (hhold : 0 ≤ m.hd + m.hr)
    [IsProbabilityMeasure m.ν] (hν : Integrable id m.ν) : ConvexOn ℝ Set.univ m.R := by
  letI := demandLaw_probability m (m.l + 1)
  have h := hinge_integral_convex (demandLaw_integrable m hν (m.l + 1))
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hm := h.1.2 hx hy ha hb hab
  have hp := h.2.2 hx hy ha hb hab
  have hl := (convex_affine (-m.hd) (m.hd * (m.l : ℝ) * m.μ)).2 hx hy ha hb hab
  simp only [smul_eq_mul] at hm hp hl
  have ht := add_le_add (add_le_add hl (mul_le_mul_of_nonneg_left hm hpr))
    (mul_le_mul_of_nonneg_left hp hhold)
  convert ht using 1 <;> simp only [Model.R, hα, one_pow, one_mul, smul_eq_mul] <;> ring

lemma R_abs_sub_le (hα : m.α = 1) (hhd : 0 ≤ m.hd) (hpr : 0 ≤ m.pr)
    (hhold : 0 ≤ m.hd + m.hr) [IsProbabilityMeasure m.ν]
    (hν : Integrable id m.ν) (x y : ℝ) :
    |m.R x - m.R y| ≤ (m.hd + m.pr + (m.hd + m.hr)) * |x - y| := by
  letI := demandLaw_probability m (m.l + 1)
  have h := hinge_integral_lipschitz (demandLaw_integrable m hν (m.l + 1)) x y
  let A := (∫ t, max (t - x) 0 ∂m.demandLaw (m.l + 1)) -
    ∫ t, max (t - y) 0 ∂m.demandLaw (m.l + 1)
  let B := (∫ t, max (x - t) 0 ∂m.demandLaw (m.l + 1)) -
    ∫ t, max (y - t) 0 ∂m.demandLaw (m.l + 1)
  have heq : m.R x - m.R y = -m.hd * (x - y) + m.pr * A + (m.hd + m.hr) * B := by
    simp only [Model.R, hα, one_pow, one_mul, A, B]
    ring
  rw [heq]
  calc
    |(-m.hd * (x - y) + m.pr * A) + (m.hd + m.hr) * B| ≤
        |-m.hd * (x - y)| + |m.pr * A| + |(m.hd + m.hr) * B| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = m.hd * |x - y| + m.pr * |A| + (m.hd + m.hr) * |B| := by
      rw [abs_mul, abs_neg, abs_of_nonneg hhd, abs_mul, abs_of_nonneg hpr,
        abs_mul, abs_of_nonneg hhold]
    _ ≤ m.hd * |x - y| + m.pr * |x - y| + (m.hd + m.hr) * |x - y| := by
      exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left h.1 hpr))
        (mul_le_mul_of_nonneg_left h.2 hhold)
    _ = (m.hd + m.pr + (m.hd + m.hr)) * |x - y| := by ring

lemma R_antitone_left (hR : ConvexOn ℝ Set.univ m.R) (a : ℝ)
    (ha : ∀ x, m.R a ≤ m.R x) : AntitoneOn m.R (Set.Iic a) := by
  intro x hx y hy hxy
  have h := hR.le_max_of_mem_Icc (show x ∈ Set.univ from trivial)
    (show a ∈ Set.univ from trivial) (show y ∈ Set.Icc x a from ⟨hxy, hy⟩)
  rwa [max_eq_left (ha x)] at h

lemma R_continuous (hα : m.α = 1) (hhd : 0 ≤ m.hd) (hpr : 0 ≤ m.pr)
    (hhold : 0 ≤ m.hd + m.hr) [IsProbabilityMeasure m.ν]
    (hν : Integrable id m.ν) : Continuous m.R := by
  have hC : 0 ≤ m.hd + m.pr + (m.hd + m.hr) := add_nonneg (add_nonneg hhd hpr) hhold
  have h : LipschitzWith ⟨m.hd + m.pr + (m.hd + m.hr), hC⟩ m.R := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |m.R x - m.R y| ≤ (m.hd + m.pr + (m.hd + m.hr)) * |x - y|
    exact R_abs_sub_le m hα hhd hpr hhold hν x y
  exact h.continuous

lemma R_min_eq (hα : m.α = 1) (a w : ℝ) : m.R (min a w) = m.R a + m.P a w := by
  by_cases h : a ≤ w
  · simp [Model.P, h, min_eq_left h]
  · simp [Model.P, hα, h, min_eq_right (le_of_not_ge h)]

lemma stage_lower (hα : m.α = 1) (hcr : m.cr = 0)
    (hR : ConvexOn ℝ Set.univ m.R) (a : ℝ) (ha : ∀ x, m.R a ≤ m.R x)
    (s : SysState m.L) (act : ℝ × ℝ) (hf : m.SysFeasible s act) :
    m.depotCost a (s.1, s.2.1) act.1 + m.R a ≤ m.sysCost s act := by
  have hlow : m.R (min a (s.2.1 + arrival s.1 act.1)) ≤ m.R (s.2.2 + act.2) := by
    by_cases h : a ≤ s.2.1 + arrival s.1 act.1
    · rw [min_eq_left h]
      exact ha _
    · rw [min_eq_right (le_of_not_ge h)]
      exact R_antitone_left m hR a ha
        (hf.2.2.trans (le_of_not_ge h)) (le_of_not_ge h) hf.2.2
  rw [R_min_eq m hα] at hlow
  simp only [Model.depotCost, Model.sysCost, hcr, zero_mul, add_zero]
  linarith

lemma μ_nonneg (hν : m.ν (Set.Iio 0) = 0) : 0 ≤ m.μ := by
  change 0 ≤ ∫ t, t ∂m.ν
  apply integral_nonneg_of_ae
  change ∀ᵐ t ∂m.ν, 0 ≤ t
  simpa only [ae_iff, not_le, Set.Iio] using hν

lemma cost_nonneg_core (hα : m.α = 1) (hhd : 0 ≤ m.hd) (hpr : 0 ≤ m.pr)
    (hhold : 0 ≤ m.hd + m.hr) (hμ : 0 ≤ m.μ) (w b : ℝ) (hbw : b ≤ w) :
    0 ≤ m.D w + m.R b := by
  have h1 : 0 ≤ ∫ t, max (t - b) 0 ∂m.demandLaw (m.l + 1) :=
    integral_nonneg (fun t => le_max_right _ _)
  have h2 : 0 ≤ ∫ t, max (b - t) 0 ∂m.demandLaw (m.l + 1) :=
    integral_nonneg (fun t => le_max_right _ _)
  have h3 : 0 ≤ m.hd * (w - b) := mul_nonneg hhd (sub_nonneg.mpr hbw)
  have h4 : 0 ≤ m.hd * (m.l : ℝ) * m.μ :=
    mul_nonneg (mul_nonneg hhd (Nat.cast_nonneg _)) hμ
  simp only [Model.D, Model.R, hα, one_pow, one_mul]
  nlinarith [mul_nonneg hpr h1, mul_nonneg hhold h2]

lemma orderCost_nonneg (hK : 0 ≤ m.K) (hcd : m.cd = 0) (y : ℝ) :
    0 ≤ m.orderCost y := by
  simp only [Model.orderCost, hcd, zero_mul, add_zero]
  split <;> positivity

lemma sysCost_nonneg (hα : m.α = 1) (hK : 0 ≤ m.K) (hcd : m.cd = 0)
    (hcr : m.cr = 0) (hhd : 0 ≤ m.hd) (hpr : 0 ≤ m.pr)
    (hhold : 0 ≤ m.hd + m.hr) (hμ : 0 ≤ m.μ)
    (s : SysState m.L) (act : ℝ × ℝ) (hf : m.SysFeasible s act) :
    0 ≤ m.sysCost s act := by
  have h := cost_nonneg_core m hα hhd hpr hhold hμ _ _ hf.2.2
  have ho := orderCost_nonneg m hK hcd act.1
  simp only [Model.sysCost, hcr, zero_mul, add_zero]
  linarith

lemma shifted_depotCost_nonneg (hα : m.α = 1) (hK : 0 ≤ m.K) (hcd : m.cd = 0)
    (hhd : 0 ≤ m.hd) (hpr : 0 ≤ m.pr) (hhold : 0 ≤ m.hd + m.hr) (hμ : 0 ≤ m.μ)
    (a : ℝ) (p : DepotState m.L) (y : ℝ) : 0 ≤ m.depotCost a p y + m.R a := by
  have h := cost_nonneg_core m hα hhd hpr hhold hμ
    (p.2 + arrival p.1 y) (min a (p.2 + arrival p.1 y)) (min_le_right _ _)
  rw [R_min_eq m hα] at h
  have ho := orderCost_nonneg m hK hcd y
  simp only [Model.depotCost]
  linarith

lemma depotCost_nonneg (hα : m.α = 1) (hK : 0 ≤ m.K) (hcd : m.cd = 0)
    (hhd : 0 ≤ m.hd) (hpr : 0 ≤ m.pr) (hrate : 0 < m.hd + m.pr)
    [IsProbabilityMeasure m.ν] (hν0 : m.ν (Set.Iio 0) = 0) (hνint : Integrable id m.ν)
    (a : ℝ) (ha : ∀ x, m.R a ≤ m.R x) (p : DepotState m.L) (y : ℝ) :
    0 ≤ m.depotCost a p y := by
  have ho := orderCost_nonneg m hK hcd y
  have ha0 := minimizer_nonneg m hα hrate hν0 hνint a ha
  let w := p.2 + arrival p.1 y
  have hg : 0 ≤ m.D w + m.P a w := by
    by_cases hw : 0 ≤ w
    · have hp : 0 ≤ m.P a w := by
        unfold Model.P
        split
        · exact le_rfl
        · simpa only [hα, sub_self, zero_mul, zero_add] using sub_nonneg.mpr (ha w)
      exact add_nonneg (mul_nonneg hhd hw) hp
    · have hw0 : w < 0 := lt_of_not_ge hw
      have haw : ¬a ≤ w := by linarith
      have hmin := ha 0
      simp only [Model.D, Model.P, if_neg haw, hα, sub_self, zero_mul, zero_add]
      rw [R_of_nonpos m hα hν0 hνint w hw0.le]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hpr hw0.le]
  change 0 ≤ m.orderCost y + m.D w + m.P a w
  linarith

end FZEchelon.AverageCost.Analysis

open MeasureTheory Filter

namespace FZEchelon.AverageCost.Analysis

variable (m : Model)

noncomputable def outletExcess (a x : ℝ) : ℝ :=
  if a ≤ x then m.R x - m.R a else 0

lemma outletExcess_nonneg (a : ℝ) (ha : ∀ x, m.R a ≤ m.R x) (x : ℝ) :
    0 ≤ outletExcess m a x := by
  unfold outletExcess
  split
  · exact sub_nonneg.mpr (ha x)
  · exact le_rfl

lemma outletExcess_bound (a C : ℝ) (hC : 0 ≤ C)
    (hR : ∀ x y, |m.R x - m.R y| ≤ C * |x - y|) (x : ℝ) :
    outletExcess m a x ≤ C * max 0 (x - a) := by
  unfold outletExcess
  by_cases h : a ≤ x
  · rw [if_pos h, max_eq_right (sub_nonneg.mpr h)]
    simpa only [abs_of_nonneg (sub_nonneg.mpr h)] using
      (le_abs_self (m.R x - m.R a)).trans (hR x a)
  · rw [if_neg h]
    exact mul_nonneg hC (le_max_left _ _)

lemma candidate_gap (hα : m.α = 1) (a x w : ℝ) (hxw : x ≤ w) :
    m.R (x + max 0 (min a w - x)) - m.R a - m.P a w = outletExcess m a x := by
  unfold outletExcess Model.P
  by_cases hx : a ≤ x
  · have hw : a ≤ w := hx.trans hxw
    have hm : min a w - x ≤ 0 := by linarith [min_le_left a w]
    simp only [if_pos hx, if_pos hw, max_eq_left hm, add_zero, sub_zero]
  · have hm : 0 ≤ min a w - x := sub_nonneg.mpr (le_min (le_of_not_ge hx) hxw)
    rw [max_eq_right hm]
    have heq : x + (min a w - x) = min a w := by ring
    rw [heq]
    simp only [if_neg hx, hα, sub_self, zero_mul, zero_add]
    by_cases hw : a ≤ w
    · simp [hw, min_eq_left hw]
    · simp [hw, min_eq_right (le_of_not_ge hw)]

lemma sigmaStar_cost (hα : m.α = 1) (hcr : m.cr = 0)
    (σ : DepotState m.L → ℝ) (a : ℝ) (hσ : ∀ p, 0 ≤ σ p)
    (s : SysState m.L) (hs : InDomain s) :
    m.sysCost s (m.sigmaStar σ a s) =
      m.depotCost a (s.1, s.2.1) (σ (s.1, s.2.1)) + m.R a + outletExcess m a s.2.2 := by
  have har := arrival_nonneg s.1 (σ (s.1, s.2.1)) hs.1 (hσ _)
  have hxw : s.2.2 ≤ s.2.1 + arrival s.1 (σ (s.1, s.2.1)) := by linarith [hs.2]
  have heq := candidate_gap m hα a s.2.2 _ hxw
  simp only [Model.sysCost, Model.sigmaStar, Model.shipStar, Model.depotCost, hcr,
    zero_mul, add_zero]
  linarith

lemma stationaryState_depot (σ : DepotState m.L → ℝ) (a : ℝ)
    (s : SysState m.L) (n : ℕ) (h : Fin n → ℝ) :
    ((Policy.stationaryState m.sysNext (m.sigmaStar σ a) s n h).1,
      (Policy.stationaryState m.sysNext (m.sigmaStar σ a) s n h).2.1) =
      Policy.stationaryState m.depotNext σ (s.1, s.2.1) n h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change m.depotNext
      ((Policy.stationaryState m.sysNext (m.sigmaStar σ a) s n (Fin.init h)).1,
        (Policy.stationaryState m.sysNext (m.sigmaStar σ a) s n (Fin.init h)).2.1)
      (σ ((Policy.stationaryState m.sysNext (m.sigmaStar σ a) s n (Fin.init h)).1,
        (Policy.stationaryState m.sysNext (m.sigmaStar σ a) s n (Fin.init h)).2.1))
      (h (Fin.last n)) = _
    rw [ih]
    rfl

lemma piStar_path_depot (σ : DepotState m.L → ℝ) (a : ℝ)
    (s : SysState m.L) (ω : ℕ → ℝ) (n : ℕ) :
    ((Policy.path m.sysNext (m.piStar σ a) s ω n).1,
      (Policy.path m.sysNext (m.piStar σ a) s ω n).2.1) =
      Policy.path m.depotNext (m.depotStationary σ) (s.1, s.2.1) ω n := by
  simp only [Model.piStar, Model.depotStationary, Policy.path_ofStationary]
  exact stationaryState_depot m σ a s n _

lemma piStar_stage_cost (hα : m.α = 1) (hcr : m.cr = 0)
    (σ : DepotState m.L → ℝ) (a : ℝ) (hσ : ∀ p, 0 ≤ σ p)
    (s : SysState m.L) (hs : InDomain s) (ω : ℕ → ℝ) (n : ℕ) :
    m.sysCost (Policy.path m.sysNext (m.piStar σ a) s ω n)
        ((m.piStar σ a).action s ω n) =
      m.depotCost a (Policy.path m.depotNext (m.depotStationary σ) (s.1, s.2.1) ω n)
        ((m.depotStationary σ).action (s.1, s.2.1) ω n) + m.R a +
      outletExcess m a (Policy.path m.sysNext (m.piStar σ a) s ω n).2.2 := by
  rw [piStar_action, depotStationary_action]
  rw [sigmaStar_cost m hα hcr σ a hσ _ (piStar_domain m σ a hσ s hs ω n)]
  rw [piStar_path_depot]

lemma piStar_excess_bound (σ : DepotState m.L → ℝ) (a C : ℝ) (hC : 0 ≤ C)
    (hR : ∀ x y, |m.R x - m.R y| ≤ C * |x - y|)
    (s : SysState m.L) (ω : ℕ → ℝ) (hω : ∀ k, 0 ≤ ω k) (n : ℕ) :
    outletExcess m a (Policy.path m.sysNext (m.piStar σ a) s ω n).2.2 ≤
      C * max 0 (s.2.2 - a - ∑ k ∈ Finset.range n, ω k) := by
  apply (outletExcess_bound m a C hC hR _).trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply max_le (le_max_left _ _)
  have hb := piStar_outlet_bound m σ a s ω hω n
  have hmax : max a (s.2.2 - ∑ k ∈ Finset.range n, ω k) - a =
      max 0 (s.2.2 - a - ∑ k ∈ Finset.range n, ω k) := by
    rw [← max_sub_sub_right]
    congr 1 <;> ring
  rw [← hmax]
  exact sub_le_sub_right hb a

end FZEchelon.AverageCost.Analysis

open MeasureTheory ProbabilityTheory Filter Topology

namespace FZEchelon.AverageCost.Analysis

lemma mean_pos_of_nonneg_atomless (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν0 : ν (Set.Iio 0) = 0) (hνatom : ν {0} = 0) (hνint : Integrable id ν) :
    0 < ∫ t, t ∂ν := by
  have hnonneg : ∀ᵐ t ∂ν, 0 ≤ t := by simpa only [ae_iff, not_le, Set.Iio] using hν0
  have hne : ∀ᵐ t ∂ν, t ≠ 0 := by simpa only [ae_iff, not_not, Set.setOf_eq_eq_singleton] using hνatom
  have hm : 0 ≤ ∫ t, t ∂ν := integral_nonneg_of_ae hnonneg
  by_contra h
  have heq : (∫ t, t ∂ν) = 0 := le_antisymm (le_of_not_gt h) hm
  have hae : ∀ᵐ t ∂ν, t = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hνint).1 heq
  have hfalse : ∀ᵐ t ∂ν, False := by
    filter_upwards [hne, hae] with t hn he
    exact hn he
  have hz : ν = 0 := by simpa using hfalse
  have heqmass := congrArg (fun μ : Measure ℝ => μ Set.univ) hz
  simpa using heqmass

lemma cumulative_demand_atTop (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν0 : ν (Set.Iio 0) = 0) (hνatom : ν {0} = 0) (hνint : Integrable id ν) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => ν),
      Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n, ω j) atTop atTop := by
  let P := Measure.infinitePi (fun _ : ℕ => ν)
  have hmap (n : ℕ) : P.map (fun ω => ω n) = ν :=
    Measure.infinitePi_map_eval (fun _ : ℕ => ν) n
  have hi : Integrable (fun ω : ℕ → ℝ => ω 0) P := by
    have hh : Integrable id (P.map (fun ω => ω 0)) := by rw [hmap]; exact hνint
    exact hh.comp_measurable (measurable_pi_apply 0)
  have hind : iIndepFun (fun n : ℕ => fun ω : ℕ → ℝ => ω n) P :=
    iIndepFun_infinitePi (X := fun _ : ℕ => (id : ℝ → ℝ)) (fun _ => measurable_id)
  have hident (n : ℕ) : IdentDistrib (fun ω : ℕ → ℝ => ω n) (fun ω => ω 0) P P :=
    ⟨(measurable_pi_apply n).aemeasurable, (measurable_pi_apply 0).aemeasurable,
      (hmap n).trans (hmap 0).symm⟩
  have havg := strong_law_ae_real (fun n : ℕ => fun ω : ℕ → ℝ => ω n)
    hi (fun i j hij => hind.indepFun hij) hident
  have hmean : (∫ ω, ω 0 ∂P) = ∫ t, t ∂ν := by
    have hmapint := integral_map (μ := P) (φ := fun ω : ℕ → ℝ => ω 0)
      (f := fun t : ℝ => t) (measurable_pi_apply 0).aemeasurable aestronglyMeasurable_id
    rw [hmap] at hmapint
    exact hmapint.symm
  rw [hmean] at havg
  have hm := mean_pos_of_nonneg_atomless ν hν0 hνatom hνint
  filter_upwards [havg] with ω hω
  have ht := hω.pos_mul_atTop hm tendsto_natCast_atTop_atTop
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)))

lemma demand_path_nonneg (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν0 : ν (Set.Iio 0) = 0) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => ν), ∀ n, 0 ≤ ω n := by
  have hnonneg : ∀ᵐ t ∂ν, 0 ≤ t := by simpa only [ae_iff, not_le, Set.Iio] using hν0
  rw [ae_all_iff]
  intro n
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) n).quasiMeasurePreserving.tendsto_ae hnonneg

lemma expected_residual_tendsto_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν0 : ν (Set.Iio 0) = 0) (hνatom : ν {0} = 0) (hνint : Integrable id ν)
    (A : ℝ) :
    Tendsto (fun n : ℕ => ∫ ω : ℕ → ℝ, max 0 (A - ∑ j ∈ Finset.range n, ω j)
      ∂Measure.infinitePi (fun _ : ℕ => ν)) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence
    (μ := Measure.infinitePi (fun _ : ℕ => ν))
    (F := fun n (ω : ℕ → ℝ) => max 0 (A - ∑ j ∈ Finset.range n, ω j))
    (f := fun _ => (0 : ℝ)) (fun _ => max 0 A)
    (fun n => (show Measurable (fun ω : ℕ → ℝ => max 0 (A - ∑ j ∈ Finset.range n, ω j))
      from by fun_prop).aestronglyMeasurable) (integrable_const _) ?_ ?_
  · simpa only [integral_zero] using h
  · intro n
    filter_upwards [demand_path_nonneg ν hν0] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    apply max_le_max le_rfl
    exact sub_le_self _ (Finset.sum_nonneg (fun j _ => hω j))
  · filter_upwards [cumulative_demand_atTop ν hν0 hνatom hνint] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω.eventually_ge_atTop A] with n hn
    exact (max_eq_left (sub_nonpos.mpr hn)).symm

lemma residual_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν0 : ν (Set.Iio 0) = 0) (A : ℝ) (n : ℕ) :
    Integrable (fun ω : ℕ → ℝ => max 0 (A - ∑ j ∈ Finset.range n, ω j))
      (Measure.infinitePi (fun _ : ℕ => ν)) := by
  apply (integrable_const (max 0 A)).mono' (by fun_prop)
  filter_upwards [demand_path_nonneg ν hν0] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
  exact max_le_max le_rfl (sub_le_self _ (Finset.sum_nonneg (fun j _ => hω j)))

lemma residual_cesaro_tendsto_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν0 : ν (Set.Iio 0) = 0) (hνatom : ν {0} = 0) (hνint : Integrable id ν)
    (A : ℝ) :
    Tendsto (fun n : ℕ => (n⁻¹ : ℝ) * ∑ k ∈ Finset.range n,
      ∫ ω : ℕ → ℝ, max 0 (A - ∑ j ∈ Finset.range k, ω j)
        ∂Measure.infinitePi (fun _ : ℕ => ν)) atTop (𝓝 0) :=
  (expected_residual_tendsto_zero ν hν0 hνatom hνint A).cesaro

end FZEchelon.AverageCost.Analysis

open Filter Topology

namespace FZEchelon.AverageCost.Analysis

lemma ereal_limsup_add_tendsto (u : ℕ → EReal) (v : ℕ → ℝ) (a : ℝ)
    (hv : Tendsto v atTop (𝓝 a)) :
    limsup (fun n => u n + (v n : EReal)) atTop = limsup u atTop + (a : EReal) := by
  have ht : Tendsto (fun n => (v n : EReal)) atTop (𝓝 (a : EReal)) :=
    EReal.tendsto_coe.2 hv
  have hs := ht.limsup_eq
  have hi := ht.liminf_eq
  have hsum : (u + fun n => (v n : EReal)) = (fun n => u n + (v n : EReal)) := by
    funext n
    rfl
  apply le_antisymm
  · have htop : limsup (fun n => (v n : EReal)) atTop ≠ ⊤ := by
      rw [hs]
      exact EReal.coe_ne_top a
    have hbot : limsup (fun n => (v n : EReal)) atTop ≠ ⊥ := by
      rw [hs]
      exact EReal.coe_ne_bot a
    have hh := EReal.limsup_add_le (u := u) (v := fun n => (v n : EReal))
      (Or.inr htop) (Or.inr hbot)
    rw [hsum, hs] at hh
    exact hh
  · have hh := EReal.le_limsup_add (f := atTop) (u := u) (v := fun n => (v n : EReal))
    rw [hsum, hi] at hh
    exact hh

lemma ereal_limsup_sandwich (u v : ℕ → EReal) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0))
    (hlo : ∀ᶠ n in atTop, u n ≤ v n)
    (hhi : ∀ᶠ n in atTop, v n ≤ u n + (e n : EReal)) :
    limsup v atTop = limsup u atTop := by
  apply le_antisymm
  · have h := limsup_le_limsup hhi
    rwa [ereal_limsup_add_tendsto u e 0 he, EReal.coe_zero, add_zero] at h
  · exact limsup_le_limsup hlo

lemma ereal_limsup_add_const (u : ℕ → EReal) (a : ℝ) :
    limsup (fun n => u n + (a : EReal)) atTop = limsup u atTop + (a : EReal) :=
  ereal_limsup_add_tendsto u (fun _ => a) a tendsto_const_nhds

lemma ereal_average_shift (u : EReal) (c : ℝ) (n : ℕ) (hn : 0 < n) :
    (((1 : ℝ) / n : ℝ) : EReal) * (u + (((n : ℝ) * c : ℝ) : EReal)) =
      (((1 : ℝ) / n : ℝ) : EReal) * u + (c : EReal) := by
  have hp : (0 : ℝ) ≤ 1 / (n : ℝ) := div_nonneg zero_le_one (Nat.cast_nonneg _)
  rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hp) (EReal.coe_ne_top _),
    ← EReal.coe_mul]
  congr 1
  congr 1
  simpa only [one_div] using inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr hn.ne') c

end FZEchelon.AverageCost.Analysis

open MeasureTheory Filter

namespace FZEchelon.AverageCost.Analysis

lemma nonneg_lintegral_add_const_pos {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → ℝ) (c : ℝ)
    (hf : ∀ᵐ ω ∂ν, 0 ≤ f ω) (hc : 0 ≤ c) :
    ((∫⁻ ω, ENNReal.ofReal (f ω + c) ∂ν : ENNReal) : EReal) =
      ((∫⁻ ω, ENNReal.ofReal (f ω) ∂ν : ENNReal) : EReal) + (c : EReal) := by
  have heq : (fun ω => ENNReal.ofReal (f ω + c)) =ᵐ[ν]
      (fun ω => ENNReal.ofReal (f ω) + ENNReal.ofReal c) := by
    filter_upwards [hf] with ω hω
    exact ENNReal.ofReal_add hω hc
  rw [lintegral_congr_ae heq, lintegral_add_right _ measurable_const]
  simp only [lintegral_const, measure_univ, mul_one, EReal.coe_ennreal_add,
    EReal.coe_ennreal_ofReal, max_eq_left hc]

lemma nonneg_lintegral_add_const {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → ℝ) (c : ℝ)
    (hf : ∀ᵐ ω ∂ν, 0 ≤ f ω) (hfc : ∀ᵐ ω ∂ν, 0 ≤ f ω + c) :
    ((∫⁻ ω, ENNReal.ofReal (f ω + c) ∂ν : ENNReal) : EReal) =
      ((∫⁻ ω, ENNReal.ofReal (f ω) ∂ν : ENNReal) : EReal) + (c : EReal) := by
  by_cases hc : 0 ≤ c
  · exact nonneg_lintegral_add_const_pos ν f c hf hc
  · have hh := nonneg_lintegral_add_const_pos ν (fun ω => f ω + c) (-c) hfc
      (neg_nonneg.mpr (le_of_not_ge hc))
    simp only [add_neg_cancel_right] at hh
    have h := congrArg (fun z : EReal => z + (c : EReal)) hh
    rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero] at h
    exact h.symm

lemma nonneg_lintegral_add_integrable {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (f g : Ω → ℝ)
    (hf : ∀ᵐ ω ∂ν, 0 ≤ f ω) (hg : ∀ᵐ ω ∂ν, 0 ≤ g ω) (hgi : Integrable g ν) :
    ((∫⁻ ω, ENNReal.ofReal (f ω + g ω) ∂ν : ENNReal) : EReal) =
      ((∫⁻ ω, ENNReal.ofReal (f ω) ∂ν : ENNReal) : EReal) + ((∫ ω, g ω ∂ν : ℝ) : EReal) := by
  have heq : (fun ω => ENNReal.ofReal (f ω + g ω)) =ᵐ[ν]
      (fun ω => ENNReal.ofReal (f ω) + ENNReal.ofReal (g ω)) := by
    filter_upwards [hf, hg] with ω hωf hωg
    exact ENNReal.ofReal_add hωf hωg
  rw [lintegral_congr_ae heq, lintegral_add_right' _ hgi.aestronglyMeasurable.aemeasurable.ennreal_ofReal,
    ← ofReal_integral_eq_lintegral_ofReal hgi hg, EReal.coe_ennreal_add,
    EReal.coe_ennreal_ofReal]
  rw [max_eq_left (integral_nonneg_of_ae hg)]

lemma costN_of_nonneg {S A : Type*} (f : S → A → ℝ → S) (c : S → A → ℝ)
    (ν : Measure ℝ) (π : Policy S A) (s : S)
    (hc : ∀ ω k, 0 ≤ c (Policy.path f π s ω k) (π.action s ω k)) (n : ℕ) :
    Policy.costN f c 1 ν π s n =
      ((∫⁻ ω, ENNReal.ofReal (∑ k ∈ Finset.range n,
        c (Policy.path f π s ω k) (π.action s ω k))
        ∂Measure.infinitePi (fun _ : ℕ => ν) : ENNReal) : EReal) := by
  unfold Policy.costN
  simp only [one_pow, one_mul]
  have hn : (fun ω => ∑ k ∈ Finset.range n,
      ENNReal.ofReal (-c (Policy.path f π s ω k) (π.action s ω k))) = fun _ => 0 := by
    funext ω
    apply Finset.sum_eq_zero
    intro k hk
    exact ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr (hc ω k))
  rw [hn, lintegral_zero, EReal.coe_ennreal_zero, sub_zero]
  congr 1
  apply lintegral_congr
  intro ω
  exact (ENNReal.ofReal_sum_of_nonneg (fun k _ => hc ω k)).symm

end FZEchelon.AverageCost.Analysis

open MeasureTheory Filter Topology

namespace FZEchelon.AverageCost.Analysis

/-- A bundle of hypotheses already present in the exact average-cost target. -/
structure CostConditions (m : Model) (a : ℝ) : Prop where
  alpha : m.α = 1
  orderRate : m.cd = 0
  shipRate : m.cr = 0
  fixed : 0 ≤ m.K
  depotHolding : 0 ≤ m.hd
  outletPenalty : 0 ≤ m.pr
  totalHolding : 0 ≤ m.hd + m.hr
  shortageRate : 0 < m.hd + m.pr
  demandNonneg : m.ν (Set.Iio 0) = 0
  demandIntegrable : Integrable id m.ν
  minimum : ∀ x, m.R a ≤ m.R x

variable (m : Model) [IsProbabilityMeasure m.ν] (a : ℝ) (H : CostConditions m a)

include H

lemma sys_stage_nonneg (s : SysState m.L) (act : ℝ × ℝ) (hf : m.SysFeasible s act) :
    0 ≤ m.sysCost s act :=
  sysCost_nonneg m H.alpha H.fixed H.orderRate H.shipRate H.depotHolding H.outletPenalty
    H.totalHolding (μ_nonneg m H.demandNonneg) s act hf

lemma depot_stage_nonneg (p : DepotState m.L) (y : ℝ) : 0 ≤ m.depotCost a p y :=
  depotCost_nonneg m H.alpha H.fixed H.orderRate H.depotHolding H.outletPenalty
    H.shortageRate H.demandNonneg H.demandIntegrable a H.minimum p y

lemma depot_stage_shift_nonneg (p : DepotState m.L) (y : ℝ) :
    0 ≤ m.depotCost a p y + m.R a :=
  shifted_depotCost_nonneg m H.alpha H.fixed H.orderRate H.depotHolding H.outletPenalty
    H.totalHolding (μ_nonneg m H.demandNonneg) a p y

lemma sysCostN_rep (π : Policy (SysState m.L) (ℝ × ℝ)) (s : SysState m.L)
    (hπ : m.SysAdmissible π s) (n : ℕ) :
    m.sysCostN π s n =
      ((∫⁻ ω, ENNReal.ofReal (∑ k ∈ Finset.range n,
        m.sysCost (Policy.path m.sysNext π s ω k) (π.action s ω k))
        ∂Measure.infinitePi (fun _ : ℕ => m.ν) : ENNReal) : EReal) := by
  unfold Model.sysCostN
  rw [H.alpha]
  exact costN_of_nonneg _ _ _ _ _ (fun ω k => sys_stage_nonneg m a H _ _ (hπ.2 ω k)) n

lemma depotCostN_rep (π : Policy (DepotState m.L) ℝ) (p : DepotState m.L) (n : ℕ) :
    m.depotCostN a π p n =
      ((∫⁻ ω, ENNReal.ofReal (∑ k ∈ Finset.range n,
        m.depotCost a (Policy.path m.depotNext π p ω k) (π.action p ω k))
        ∂Measure.infinitePi (fun _ : ℕ => m.ν) : ENNReal) : EReal) := by
  unfold Model.depotCostN
  rw [H.alpha]
  exact costN_of_nonneg _ _ _ _ _ (fun ω k => depot_stage_nonneg m a H _ _) n

lemma depotSum_nonneg (π : Policy (DepotState m.L) ℝ) (p : DepotState m.L)
    (ω : ℕ → ℝ) (n : ℕ) :
    0 ≤ ∑ k ∈ Finset.range n, m.depotCost a (Policy.path m.depotNext π p ω k) (π.action p ω k) :=
  Finset.sum_nonneg (fun k _ => depot_stage_nonneg m a H _ _)

lemma depotSum_shift_nonneg (π : Policy (DepotState m.L) ℝ) (p : DepotState m.L)
    (ω : ℕ → ℝ) (n : ℕ) :
    0 ≤ (∑ k ∈ Finset.range n, m.depotCost a (Policy.path m.depotNext π p ω k) (π.action p ω k))
      + (n : ℝ) * m.R a := by
  have h := Finset.sum_nonneg (s := Finset.range n)
    (fun k _ => depot_stage_shift_nonneg m a H
      (Policy.path m.depotNext π p ω k) (π.action p ω k))
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h

lemma shifted_depotCostN_rep (π : Policy (DepotState m.L) ℝ) (p : DepotState m.L) (n : ℕ) :
    m.depotCostN a π p n + (((n : ℝ) * m.R a : ℝ) : EReal) =
      ((∫⁻ ω, ENNReal.ofReal ((∑ k ∈ Finset.range n,
        m.depotCost a (Policy.path m.depotNext π p ω k) (π.action p ω k)) + (n : ℝ) * m.R a)
        ∂Measure.infinitePi (fun _ : ℕ => m.ν) : ENNReal) : EReal) := by
  rw [depotCostN_rep m a H]
  exact (nonneg_lintegral_add_const _ _ _
    (Eventually.of_forall (fun ω => depotSum_nonneg m a H π p ω n))
    (Eventually.of_forall (fun ω => depotSum_shift_nonneg m a H π p ω n))).symm

lemma projected_costN_lower (π : Policy (SysState m.L) (ℝ × ℝ)) (s : SysState m.L)
    (hπ : m.SysAdmissible π s) (n : ℕ) :
    m.depotCostN a (projectOrders m s.2.2 π) (s.1, s.2.1) n +
      (((n : ℝ) * m.R a : ℝ) : EReal) ≤ m.sysCostN π s n := by
  rw [shifted_depotCostN_rep m a H, sysCostN_rep m a H π s hπ]
  apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
  apply lintegral_mono
  intro ω
  apply ENNReal.ofReal_le_ofReal
  have hR := R_convex m H.alpha H.outletPenalty H.totalHolding H.demandIntegrable
  have h := Finset.sum_le_sum (s := Finset.range n) (fun k _ =>
    stage_lower m H.alpha H.shipRate hR a H.minimum
      (Policy.path m.sysNext π s ω k) (π.action s ω k) (hπ.2 ω k))
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    projectOrders_path, projectOrders_action] using h

lemma projected_average_lower (π : Policy (SysState m.L) (ℝ × ℝ)) (s : SysState m.L)
    (hπ : m.SysAdmissible π s) :
    m.depotAvg a (projectOrders m s.2.2 π) (s.1, s.2.1) + (m.R a : EReal) ≤ m.sysAvg π s := by
  unfold Model.depotAvg Model.sysAvg Policy.avgCost
  rw [← ereal_limsup_add_const]
  refine limsup_le_limsup ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have h := projected_costN_lower m a H π s hπ n
  have hp : (0 : EReal) ≤ (((1 : ℝ) / n : ℝ) : EReal) :=
    EReal.coe_nonneg.mpr (div_nonneg zero_le_one (Nat.cast_nonneg _))
  have hh := mul_le_mul_of_nonneg_left h hp
  rw [ereal_average_shift _ _ n (lt_of_lt_of_le Nat.zero_lt_one hn)] at hh
  exact hh

lemma candidate_costN_lower (σ : DepotState m.L → ℝ) (hσm : Measurable σ)
    (hσ : ∀ p, 0 ≤ σ p) (s : SysState m.L) (hs : InDomain s) (n : ℕ) :
    m.depotCostN a (m.depotStationary σ) (s.1, s.2.1) n +
      (((n : ℝ) * m.R a : ℝ) : EReal) ≤ m.sysCostN (m.piStar σ a) s n := by
  rw [shifted_depotCostN_rep m a H,
    sysCostN_rep m a H _ s (piStar_admissible m σ a hσm hσ s hs)]
  apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
  apply lintegral_mono
  intro ω
  apply ENNReal.ofReal_le_ofReal
  have hstage (k : ℕ) : m.depotCost a
      (Policy.path m.depotNext (m.depotStationary σ) (s.1, s.2.1) ω k)
      ((m.depotStationary σ).action (s.1, s.2.1) ω k) + m.R a ≤
      m.sysCost (Policy.path m.sysNext (m.piStar σ a) s ω k)
        ((m.piStar σ a).action s ω k) := by
    rw [piStar_stage_cost m H.alpha H.shipRate σ a hσ s hs ω k]
    exact le_add_of_nonneg_right (outletExcess_nonneg m a H.minimum _)
  have h := Finset.sum_le_sum (s := Finset.range n) (fun k _ => hstage k)
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h

lemma candidate_costN_upper (σ : DepotState m.L → ℝ) (hσm : Measurable σ)
    (hσ : ∀ p, 0 ≤ σ p) (s : SysState m.L) (hs : InDomain s) (n : ℕ) :
    m.sysCostN (m.piStar σ a) s n ≤
      m.depotCostN a (m.depotStationary σ) (s.1, s.2.1) n +
        (((n : ℝ) * m.R a : ℝ) : EReal) +
        (((m.hd + m.pr + (m.hd + m.hr)) * ∑ k ∈ Finset.range n,
          ∫ ω : ℕ → ℝ, max 0 (s.2.2 - a - ∑ j ∈ Finset.range k, ω j)
            ∂Measure.infinitePi (fun _ : ℕ => m.ν) : ℝ) : EReal) := by
  let P := Measure.infinitePi (fun _ : ℕ => m.ν)
  let C := m.hd + m.pr + (m.hd + m.hr)
  have hC : 0 ≤ C := add_nonneg (add_nonneg H.depotHolding H.outletPenalty) H.totalHolding
  let F : (ℕ → ℝ) → ℝ := fun ω =>
    (∑ k ∈ Finset.range n, m.depotCost a
      (Policy.path m.depotNext (m.depotStationary σ) (s.1, s.2.1) ω k)
      ((m.depotStationary σ).action (s.1, s.2.1) ω k)) + (n : ℝ) * m.R a
  let G : (ℕ → ℝ) → ℝ := fun ω =>
    C * ∑ k ∈ Finset.range n, max 0 (s.2.2 - a - ∑ j ∈ Finset.range k, ω j)
  have hF : ∀ᵐ ω ∂P, 0 ≤ F ω := Eventually.of_forall (fun ω =>
    depotSum_shift_nonneg m a H _ _ ω n)
  have hG : ∀ᵐ ω ∂P, 0 ≤ G ω := Eventually.of_forall (fun ω =>
    mul_nonneg hC (Finset.sum_nonneg (fun k _ => le_max_left _ _)))
  have hGi : Integrable G P :=
    (integrable_finsetSum _ (fun k _ => residual_integrable m.ν H.demandNonneg (s.2.2 - a) k)).const_mul C
  have hGint : (∫ ω, G ω ∂P) = C * ∑ k ∈ Finset.range n,
      ∫ ω : ℕ → ℝ, max 0 (s.2.2 - a - ∑ j ∈ Finset.range k, ω j) ∂P := by
    rw [integral_const_mul, integral_finsetSum]
    intro k hk
    exact residual_integrable m.ν H.demandNonneg (s.2.2 - a) k
  have hbound : m.sysCostN (m.piStar σ a) s n ≤
      ((∫⁻ ω, ENNReal.ofReal (F ω + G ω) ∂P : ENNReal) : EReal) := by
    rw [sysCostN_rep m a H _ s (piStar_admissible m σ a hσm hσ s hs)]
    apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
    apply lintegral_mono_ae
    filter_upwards [demand_path_nonneg m.ν H.demandNonneg] with ω hω
    apply ENNReal.ofReal_le_ofReal
    have hstage (k : ℕ) :
        m.sysCost (Policy.path m.sysNext (m.piStar σ a) s ω k)
          ((m.piStar σ a).action s ω k) ≤
        m.depotCost a (Policy.path m.depotNext (m.depotStationary σ) (s.1, s.2.1) ω k)
          ((m.depotStationary σ).action (s.1, s.2.1) ω k) + m.R a +
          C * max 0 (s.2.2 - a - ∑ j ∈ Finset.range k, ω j) := by
      rw [piStar_stage_cost m H.alpha H.shipRate σ a hσ s hs ω k]
      exact add_le_add le_rfl
        (piStar_excess_bound m σ a C hC
          (R_abs_sub_le m H.alpha H.depotHolding H.outletPenalty H.totalHolding H.demandIntegrable)
          s ω hω k)
    have h := Finset.sum_le_sum (s := Finset.range n) (fun k _ => hstage k)
    simpa only [F, G, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, Finset.mul_sum] using h
  rw [nonneg_lintegral_add_integrable P F G hF hG hGi, hGint] at hbound
  have hshift := shifted_depotCostN_rep m a H (m.depotStationary σ) (s.1, s.2.1) n
  change m.depotCostN a (m.depotStationary σ) (s.1, s.2.1) n +
    (((n : ℝ) * m.R a : ℝ) : EReal) = ((∫⁻ ω, ENNReal.ofReal (F ω) ∂P : ENNReal) : EReal) at hshift
  rw [← hshift] at hbound
  exact hbound

lemma candidate_average (hνatom : m.ν {0} = 0)
    (σ : DepotState m.L → ℝ) (hσm : Measurable σ) (hσ : ∀ p, 0 ≤ σ p)
    (s : SysState m.L) (hs : InDomain s) :
    m.sysAvg (m.piStar σ a) s =
      m.depotAvg a (m.depotStationary σ) (s.1, s.2.1) + (m.R a : EReal) := by
  let C := m.hd + m.pr + (m.hd + m.hr)
  let e : ℕ → ℝ := fun n => (1 : ℝ) / n * (C * ∑ k ∈ Finset.range n,
    ∫ ω : ℕ → ℝ, max 0 (s.2.2 - a - ∑ j ∈ Finset.range k, ω j)
      ∂Measure.infinitePi (fun _ : ℕ => m.ν))
  have he : Tendsto e atTop (𝓝 0) := by
    have h := (residual_cesaro_tendsto_zero m.ν H.demandNonneg hνatom H.demandIntegrable
      (s.2.2 - a)).const_mul C
    convert h using 1
    · funext n
      simp only [e, one_div]
      ring
    · simp
  unfold Model.sysAvg Model.depotAvg Policy.avgCost
  rw [← ereal_limsup_add_const]
  apply ereal_limsup_sandwich _ _ e he
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have h := candidate_costN_lower m a H σ hσm hσ s hs n
    have hp : (0 : EReal) ≤ (((1 : ℝ) / n : ℝ) : EReal) :=
      EReal.coe_nonneg.mpr (div_nonneg zero_le_one (Nat.cast_nonneg _))
    have hh := mul_le_mul_of_nonneg_left h hp
    rwa [ereal_average_shift _ _ n (lt_of_lt_of_le Nat.zero_lt_one hn)] at hh
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have h := candidate_costN_upper m a H σ hσm hσ s hs n
    have hp : (0 : EReal) ≤ (((1 : ℝ) / n : ℝ) : EReal) :=
      EReal.coe_nonneg.mpr (div_nonneg zero_le_one (Nat.cast_nonneg _))
    have hh := mul_le_mul_of_nonneg_left h hp
    rw [EReal.left_distrib_of_nonneg_of_ne_top hp (EReal.coe_ne_top _),
      ereal_average_shift _ _ n (lt_of_lt_of_le Nat.zero_lt_one hn), ← EReal.coe_mul] at hh
    exact hh

end FZEchelon.AverageCost.Analysis

open MeasureTheory Filter Topology
open FZEchelon.AverageCost FZEchelon.AverageCost.Analysis

theorem solution (m : Model) (hα : m.α = 1) (hcd : m.cd = 0)
    (hcr : m.cr = 0) (hK : 0 < m.K) (hhd : 0 < m.hd) (hhr : 0 < m.hr) (hpr : 0 < m.pr)
    [IsProbabilityMeasure m.ν] (hν0 : m.ν (Set.Iio 0) = 0) (hνatom : ∀ t, m.ν {t} = 0)
    (hνint : Integrable id m.ν)
    (xstar : ℝ) (hx : ∀ x, m.R xstar ≤ m.R x)
    (σd : DepotState m.L → ℝ) (hσm : Measurable σd) (hσ0 : ∀ p, 0 ≤ σd p)
    (hσopt : ∀ p : DepotState m.L, (∀ k, 0 ≤ p.1 k) →
      ∀ π : Policy (DepotState m.L) ℝ, m.DepotAdmissible π p →
        m.depotAvg xstar (m.depotStationary σd) p ≤ m.depotAvg xstar π p) :
    ∀ s : SysState m.L, InDomain s →
      m.sysAvg (m.piStar σd xstar) s
        = m.depotOptAvg xstar (s.1, s.2.1) + ((m.R xstar : ℝ) : EReal) := by
  let H : CostConditions m xstar :=
    { alpha := hα
      orderRate := hcd
      shipRate := hcr
      fixed := hK.le
      depotHolding := hhd.le
      outletPenalty := hpr.le
      totalHolding := (add_pos hhd hhr).le
      shortageRate := add_pos hhd hpr
      demandNonneg := hν0
      demandIntegrable := hνint
      minimum := hx }
  intro s hs
  rw [candidate_average m xstar H (hνatom 0) σd hσm hσ0 s hs]
  apply congrArg (fun z : EReal => z + (m.R xstar : EReal))
  change m.depotAvg xstar (m.depotStationary σd) (s.1, s.2.1) =
    ⨅ π : {π : Policy (DepotState m.L) ℝ // m.DepotAdmissible π (s.1, s.2.1)},
      m.depotAvg xstar π.1 (s.1, s.2.1)
  apply le_antisymm
  · exact le_iInf (fun π => hσopt (s.1, s.2.1) hs.1 π.1 π.2)
  · exact iInf_le_of_le ⟨m.depotStationary σd, depotStationary_admissible m σd hσm hσ0 _⟩ le_rfl
