-- Prove2me | solution 1 for GallegoOzerADI.PositiveSetup.myopic_order_up_to_optimal
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-06T01:40:18.425159+00:00
-- url     : https://prove2.me/submissions/0eed29c9-a9b3-4cb9-b81d-8140e6705f1c

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model
import Definitions.Def_GallegoOzerADI_PositiveSetup_MyopicLevels

set_option autoImplicit false

/- Complete checked body: AttributedReplenishment -/
section

/- Complete attributed body: Sol_GallegoOzerADI_PositiveSetup_myopic_bounds -/
section
-- Prove2me | solution 1 for GallegoOzerADI.PositiveSetup.myopic_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:33:31.000906+00:00
-- url     : https://prove2.me/submissions/8ffbdff3-0c9d-4c8f-afe9-090d7934d45d


open MeasureTheory

namespace GallegoOzerADI.PositiveSetup

open Filter Topology

/-! ### The set-up indicator and the order-cost operator -/

lemma aux_myb_ind_nonneg (z : ℝ) : 0 ≤ setupIndicator z := by
  unfold setupIndicator; split_ifs <;> norm_num

lemma aux_myb_ind_le (z : ℝ) : setupIndicator z ≤ 1 := by
  unfold setupIndicator; split_ifs <;> norm_num

lemma aux_myb_ind_zero : setupIndicator 0 = 0 := by simp [setupIndicator]

lemma aux_myb_ind_pos {z : ℝ} (hz : 0 < z) : setupIndicator z = 1 := by
  simp [setupIndicator, hz]

lemma aux_myb_oc_bdd {K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) (x : ℝ) :
    BddBelow (Set.range fun y : {y : ℝ // x ≤ y} => K * setupIndicator ((y : ℝ) - x) + f y) := by
  refine ⟨c, ?_⟩
  rintro _ ⟨y, rfl⟩
  have := hc y
  have := mul_nonneg hK (aux_myb_ind_nonneg ((y : ℝ) - x))
  linarith

lemma aux_myb_oc_le {K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) {x y : ℝ}
    (hxy : x ≤ y) : orderCost K f x ≤ K * setupIndicator (y - x) + f y :=
  ciInf_le (aux_myb_oc_bdd hK hc x) ⟨y, hxy⟩

lemma aux_myb_oc_le_self {K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y)
    (x : ℝ) : orderCost K f x ≤ f x := by
  have := aux_myb_oc_le hK hc (le_refl x)
  rwa [sub_self, aux_myb_ind_zero, mul_zero, zero_add] at this

lemma aux_myb_oc_le_K {K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) {x y : ℝ}
    (hxy : x ≤ y) : orderCost K f x ≤ K + f y := by
  have := aux_myb_oc_le hK hc hxy
  have := mul_le_of_le_one_right hK (aux_myb_ind_le (y - x))
  linarith

lemma aux_myb_oc_ge {K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) (x : ℝ) :
    c ≤ orderCost K f x := by
  unfold orderCost
  have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_refl x⟩⟩
  refine le_ciInf fun y => ?_
  have := hc y
  have := mul_nonneg hK (aux_myb_ind_nonneg ((y : ℝ) - x))
  linarith

/-! ### The running infimum -/

noncomputable def aux_myb_m (f : ℝ → ℝ) (x : ℝ) : ℝ := ⨅ y : {y : ℝ // x ≤ y}, f y

lemma aux_myb_m_bdd {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) (x : ℝ) :
    BddBelow (Set.range fun y : {y : ℝ // x ≤ y} => f y) :=
  ⟨c, by rintro _ ⟨y, rfl⟩; exact hc y⟩

lemma aux_myb_m_le {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) {x y : ℝ} (h : x ≤ y) :
    aux_myb_m f x ≤ f y := ciInf_le (aux_myb_m_bdd hc x) ⟨y, h⟩

lemma aux_myb_le_m {f : ℝ → ℝ} {x r : ℝ} (h : ∀ y, x ≤ y → r ≤ f y) : r ≤ aux_myb_m f x := by
  have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_refl x⟩⟩
  exact le_ciInf fun y => h y y.2

lemma aux_myb_oc_eq {K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) (x : ℝ) :
    orderCost K f x = min (f x) (K + aux_myb_m f x) := by
  apply le_antisymm
  · refine le_min (aux_myb_oc_le_self hK hc x) ?_
    have : orderCost K f x - K ≤ aux_myb_m f x := aux_myb_le_m fun y hy => by
      have := aux_myb_oc_le_K hK hc hy; linarith
    linarith
  · unfold orderCost
    have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_refl x⟩⟩
    refine le_ciInf fun y => ?_
    rcases eq_or_lt_of_le y.2 with h | h
    · rw [← h, sub_self, aux_myb_ind_zero, mul_zero, zero_add]
      exact min_le_left _ _
    · rw [aux_myb_ind_pos (by linarith)]
      have := aux_myb_m_le hc y.2
      exact le_trans (min_le_right _ _) (by linarith)

lemma aux_myb_m_mono {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) {a b : ℝ} (hab : a ≤ b) :
    aux_myb_m f a ≤ aux_myb_m f b :=
  aux_myb_le_m fun _ hy => aux_myb_m_le hc (hab.trans hy)

lemma aux_myb_m_cont {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) (hf : Continuous f) :
    Continuous (aux_myb_m f) := by
  rw [Metric.continuous_iff]
  intro x₀ ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuous_iff.1 hf x₀ (ε / 3) (by linarith)
  have key : ∀ a, |a - x₀| < δ → |f a - f x₀| < ε / 3 := fun a ha => by
    have := hδf a (by rwa [Real.dist_eq]); rwa [Real.dist_eq] at this
  refine ⟨δ, hδ, fun x hx => ?_⟩
  rw [Real.dist_eq] at hx ⊢
  have hx' := abs_lt.1 hx
  rcases le_total x₀ x with h | h
  · have h1 := aux_myb_m_mono hc h
    have hfx := abs_lt.1 (key x hx)
    have hmx := aux_myb_m_le hc (le_refl x)
    have h2 : aux_myb_m f x - 2 * ε / 3 ≤ aux_myb_m f x₀ := aux_myb_le_m fun y hy => by
      rcases le_total x y with h' | h'
      · have := aux_myb_m_le hc h'; linarith
      · have := abs_lt.1 (key y (abs_lt.2 ⟨by linarith, by linarith⟩))
        linarith [this.1, this.2, hfx.1, hfx.2]
    rw [abs_lt]; constructor <;> linarith
  · have h1 := aux_myb_m_mono hc h
    have hmx0 := aux_myb_m_le hc (le_refl x₀)
    have h2 : aux_myb_m f x₀ - ε / 3 ≤ aux_myb_m f x := aux_myb_le_m fun y hy => by
      rcases le_total x₀ y with h' | h'
      · have := aux_myb_m_le hc h'; linarith
      · have := abs_lt.1 (key y (abs_lt.2 ⟨by linarith, by linarith⟩))
        linarith [this.1, this.2]
    rw [abs_lt]; constructor <;> linarith

lemma aux_myb_m_rat {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) (hf : Continuous f) (x : ℝ) :
    aux_myb_m f x = ⨅ q : ℚ, f (x + |(q : ℝ)|) := by
  have hbdd : BddBelow (Set.range fun q : ℚ => f (x + |(q : ℝ)|)) :=
    ⟨c, by rintro _ ⟨q, rfl⟩; exact hc _⟩
  apply le_antisymm
  · exact le_ciInf fun q => aux_myb_m_le hc (by linarith [abs_nonneg (q : ℝ)])
  · refine aux_myb_le_m fun y hy => ?_
    have hp : ∀ u : ℝ, (⨅ q : ℚ, f (x + |(q : ℝ)|)) ≤ f (x + |u|) := by
      intro u
      refine Rat.denseRange_cast.induction_on (p := fun u : ℝ => (⨅ q : ℚ, f (x + |(q : ℝ)|)) ≤
        f (x + |u|)) u ?_ (fun q => ciInf_le hbdd q)
      exact isClosed_le continuous_const (hf.comp (continuous_const.add continuous_abs))
    have e : x + |y - x| = y := by rw [abs_of_nonneg (by linarith)]; ring
    have := hp (y - x)
    rwa [e] at this

/-! ### Norm bounds for the transitions -/

def aux_myb_n1 {n : ℕ} (o : Fin n → ℝ) : ℝ := ∑ j, |o j|

lemma aux_myb_n1_nonneg {n : ℕ} (o : Fin n → ℝ) : 0 ≤ aux_myb_n1 o :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma aux_myb_le_n1 {n : ℕ} (o : Fin n → ℝ) (j : Fin n) : |o j| ≤ aux_myb_n1 o :=
  Finset.single_le_sum (f := fun j => |o j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

lemma aux_myb_obs_le {M : ℕ} (o : Fin M → ℝ) (j : ℕ) : |obsComp o j| ≤ aux_myb_n1 o := by
  unfold obsComp; split_ifs with h
  · exact aux_myb_le_n1 o _
  · simpa using aux_myb_n1_nonneg o

lemma aux_myb_nextX_le {L M : ℕ} (y : ℝ) (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ) :
    |nextX y o D| ≤ |y| + (L + 2) * aux_myb_n1 D + aux_myb_n1 o := by
  unfold nextX
  have h1 : |∑ k : Fin (L + 2), D (Fin.castLE (by omega) k)| ≤ (L + 2) * aux_myb_n1 D := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => aux_myb_le_n1 D _).trans ?_
    simp
  have h2 := aux_myb_obs_le o 0
  have h3 := abs_sub (y - ∑ k : Fin (L + 2), D (Fin.castLE (by omega) k)) (obsComp o 0)
  have h4 := abs_sub y (∑ k : Fin (L + 2), D (Fin.castLE (by omega) k))
  linarith

lemma aux_myb_nextO_le {L M : ℕ} (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ) :
    aux_myb_n1 (nextO o D) ≤ M * (aux_myb_n1 o + aux_myb_n1 D) := by
  have : ∀ j : Fin M, |nextO o D j| ≤ aux_myb_n1 o + aux_myb_n1 D := fun j => by
    unfold nextO
    exact (abs_add_le _ _).trans (add_le_add (aux_myb_obs_le o _) (aux_myb_le_n1 D _))
  calc aux_myb_n1 (nextO o D) = ∑ j, |nextO o D j| := rfl
    _ ≤ ∑ _j : Fin M, (aux_myb_n1 o + aux_myb_n1 D) := Finset.sum_le_sum fun j _ => this j
    _ = _ := by simp [mul_add]

lemma aux_myb_trans_le {L M : ℕ} (y : ℝ) (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ) :
    |nextX y o D| + aux_myb_n1 (nextO o D) ≤
      |y| + (L + M + 2) * aux_myb_n1 D + (M + 1) * aux_myb_n1 o := by
  have := aux_myb_nextX_le y o D
  have := aux_myb_nextO_le o D
  linarith

/-! ### The backward induction -/

variable {L M : ℕ}

def aux_myb_Inv (f : ℝ → (Fin M → ℝ) → ℝ) : Prop :=
  (∀ o, Continuous (fun x => f x o)) ∧
  Measurable (fun p : ℝ × (Fin M → ℝ) => f p.1 p.2) ∧
  (∃ c, ∀ x o, c ≤ f x o) ∧
  (∃ C B, 0 ≤ B ∧ ∀ x o, f x o ≤ C + B * (|x| + aux_myb_n1 o))

lemma aux_myb_VJ {K : ℝ} (hK : 0 < K) {V : ℝ → (Fin M → ℝ) → ℝ} (h : aux_myb_Inv V) :
    aux_myb_Inv (fun x o => orderCost K (fun y => V y o) x) := by
  obtain ⟨hcont, hmeas, ⟨c, hc⟩, ⟨C, B, hB, hCB⟩⟩ := h
  have hK0 := hK.le
  refine ⟨fun o => ?_, ?_, ⟨c, fun x o => aux_myb_oc_ge hK0 (hc · o) x⟩,
    ⟨C, B, hB, fun x o => (aux_myb_oc_le_self hK0 (hc · o) x).trans (hCB x o)⟩⟩
  · have : (fun x => orderCost K (fun y => V y o) x) =
        fun x => min (V x o) (K + aux_myb_m (fun y => V y o) x) :=
      funext fun x => aux_myb_oc_eq hK0 (hc · o) x
    rw [this]
    exact (hcont o).min (continuous_const.add (aux_myb_m_cont (hc · o) (hcont o)))
  · have : (fun p : ℝ × (Fin M → ℝ) => orderCost K (fun y => V y p.2) p.1) =
        fun p => min (V p.1 p.2) (K + ⨅ q : ℚ, V (p.1 + |(q : ℝ)|) p.2) := funext fun p => by
      rw [aux_myb_oc_eq hK0 (hc · p.2) p.1, aux_myb_m_rat (hc · p.2) (hcont p.2) p.1]
    rw [this]
    refine hmeas.min (measurable_const.add (Measurable.iInf fun q => ?_))
    exact hmeas.comp ((measurable_fst.add_const _).prodMk measurable_snd)

lemma aux_myb_base (P : Model L M) : aux_myb_Inv (P.J (P.T + 1)) := by
  have h0 : P.J (P.T + 1) = fun _ _ => 0 := funext fun x => funext fun o => P.J_terminal x o
  rw [h0]
  exact ⟨fun _ => continuous_const, measurable_const, ⟨0, fun _ _ => le_refl _⟩,
    ⟨0, 0, le_refl _, fun x o => by simp⟩⟩

lemma aux_myb_obs_cont (j : ℕ) : Continuous (fun o : Fin M → ℝ => obsComp o j) := by
  unfold obsComp; split_ifs
  · exact continuous_apply _
  · exact continuous_const

lemma aux_myb_JV (P : Model L M) (s : ℕ) (h : aux_myb_Inv (P.J (s + 1))) :
    aux_myb_Inv (P.V s) ∧
      ∀ y o, Integrable (fun D => P.J (s + 1) (nextX y o D) (nextO o D)) (P.μ s) := by
  obtain ⟨hcont, hmeas, ⟨c, hc⟩, ⟨C, B, hB, hCB⟩⟩ := h
  have := P.μ_prob s
  have hαpos : 0 < P.α (s + 1) := P.α_pos (s + 1)
  have hGc : Continuous (P.G s) :=
    continuousOn_univ.1 ((P.G_convex s).continuousOn isOpen_univ)
  obtain ⟨y₀, hy₀⟩ := hGc.exists_forall_le (P.G_coercive s)
  obtain ⟨a, b, hab⟩ := P.G_linearGrowth s
  have hDint : Integrable (fun D : Fin (L + M + 2) → ℝ => aux_myb_n1 D) (P.μ s) := by
    unfold aux_myb_n1
    exact integrable_finsetSum _ fun k _ => (P.μ_integrable s k).abs
  have hXc : Continuous (fun q : (ℝ × (Fin M → ℝ)) × (Fin (L + M + 2) → ℝ) =>
      nextX q.1.1 q.1.2 q.2) := by
    unfold nextX
    refine (continuous_fst.fst.sub ?_).sub ((aux_myb_obs_cont 0).comp continuous_fst.snd)
    exact continuous_finsetSum _ fun k _ => (continuous_apply _).comp continuous_snd
  have hOc : Continuous (fun q : (ℝ × (Fin M → ℝ)) × (Fin (L + M + 2) → ℝ) =>
      nextO q.1.2 q.2) := by
    unfold nextO
    refine continuous_pi fun j => ?_
    exact ((aux_myb_obs_cont _).comp continuous_fst.snd).add
      ((continuous_apply _).comp continuous_snd)
  have hΦ : Measurable (fun q : (ℝ × (Fin M → ℝ)) × (Fin (L + M + 2) → ℝ) =>
      ((nextX q.1.1 q.1.2 q.2, nextO q.1.2 q.2) : ℝ × (Fin M → ℝ))) :=
    (hXc.prodMk hOc).measurable
  have hFmeas2 : Measurable (fun q : (ℝ × (Fin M → ℝ)) × (Fin (L + M + 2) → ℝ) =>
      P.J (s + 1) (nextX q.1.1 q.1.2 q.2) (nextO q.1.2 q.2)) := hmeas.comp hΦ
  have hFmeas : ∀ y o, Measurable (fun D => P.J (s + 1) (nextX y o D) (nextO o D)) :=
    fun y o => hFmeas2.comp (measurable_prodMk_left (x := ((y, o) : ℝ × (Fin M → ℝ))))
  have hFup : ∀ (y : ℝ) (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ), P.J (s + 1) (nextX y o D) (nextO o D) ≤
      C + B * (|y| + (L + M + 2) * aux_myb_n1 D + (M + 1) * aux_myb_n1 o) := fun y o D => by
    have h1 := hCB (nextX y o D) (nextO o D)
    have h2 := aux_myb_trans_le y o D
    have h3 := mul_le_mul_of_nonneg_left h2 hB
    linarith
  have hstuff : ∀ (y : ℝ) (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ),
      0 ≤ B * (|y| + (L + M + 2) * aux_myb_n1 D + (M + 1) * aux_myb_n1 o) := fun y o D =>
    mul_nonneg hB (add_nonneg (add_nonneg (abs_nonneg y)
      (mul_nonneg (by positivity) (aux_myb_n1_nonneg D)))
      (mul_nonneg (by positivity) (aux_myb_n1_nonneg o)))
  have hFbd : ∀ (y : ℝ) (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ), |P.J (s + 1) (nextX y o D) (nextO o D)| ≤
      |c| + |C| + B * (|y| + (L + M + 2) * aux_myb_n1 D + (M + 1) * aux_myb_n1 o) :=
    fun y o D => by
    have h1 := hFup y o D
    have h2 := hc (nextX y o D) (nextO o D)
    have h3 := hstuff y o D
    rw [abs_le]
    constructor
    · linarith [neg_abs_le c, abs_nonneg C]
    · linarith [le_abs_self C, abs_nonneg c]
  have hFint : ∀ y o, Integrable (fun D => P.J (s + 1) (nextX y o D) (nextO o D)) (P.μ s) :=
    fun y o => by
    refine Integrable.mono' ((integrable_const
      (|c| + |C| + B * (|y| + (M + 1) * aux_myb_n1 o))).add
      (hDint.const_mul (B * (L + M + 2)))) (hFmeas y o).aestronglyMeasurable
      (Filter.Eventually.of_forall fun D => ?_)
    rw [Real.norm_eq_abs]
    have := hFbd y o D
    simp only [Pi.add_apply]
    linarith
  have hIlow : ∀ y o, c ≤ ∫ D, P.J (s + 1) (nextX y o D) (nextO o D) ∂(P.μ s) := fun y o => by
    have := integral_mono (integrable_const c) (hFint y o) (fun D => hc _ _)
    simpa using this
  have hIup : ∀ y o, ∫ D, P.J (s + 1) (nextX y o D) (nextO o D) ∂(P.μ s) ≤
      C + B * (|y| + (M + 1) * aux_myb_n1 o) +
        B * (L + M + 2) * ∫ D, aux_myb_n1 D ∂(P.μ s) := fun y o => by
    have hg : Integrable (fun D => (C + B * (|y| + (M + 1) * aux_myb_n1 o)) +
        B * (L + M + 2) * aux_myb_n1 D) (P.μ s) :=
      (integrable_const _).add (hDint.const_mul _)
    have hpt : ∀ D : Fin (L + M + 2) → ℝ, P.J (s + 1) (nextX y o D) (nextO o D) ≤
        (C + B * (|y| + (M + 1) * aux_myb_n1 o)) + B * (L + M + 2) * aux_myb_n1 D :=
      fun D => by have := hFup y o D; linarith
    have := integral_mono (hFint y o) hg hpt
    rw [integral_add (integrable_const _) (hDint.const_mul _), integral_const_mul] at this
    simpa using this
  have hVlow : ∀ y o, P.G s y₀ + P.α (s + 1) * c ≤ P.V s y o := fun y o => by
    have := mul_le_mul_of_nonneg_left (hIlow y o) hαpos.le
    have := hy₀ y
    show _ ≤ P.G s y + P.α (s + 1) * _
    linarith
  refine ⟨⟨fun o => ?_, ?_, ⟨_, hVlow⟩, ?_⟩, hFint⟩
  · -- continuity
    show Continuous fun y => P.G s y + P.α (s + 1) *
      ∫ D, P.J (s + 1) (nextX y o D) (nextO o D) ∂(P.μ s)
    refine hGc.add (continuous_const.mul ?_)
    rw [continuous_iff_continuousAt]
    intro y₁
    have hbint : Integrable (fun D => (|c| + |C| + B * ((|y₁| + 1) + (M + 1) * aux_myb_n1 o)) +
        B * (L + M + 2) * aux_myb_n1 D) (P.μ s) := (integrable_const _).add (hDint.const_mul _)
    refine continuousAt_of_dominated ?_ ?_ hbint ?_
    · exact Filter.Eventually.of_forall fun y => (hFmeas y o).aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds y₁ one_pos] with y hy
      refine Filter.Eventually.of_forall fun D => ?_
      rw [Real.norm_eq_abs]
      have h1 := hFbd y o D
      have h2 : |y| ≤ |y₁| + 1 := by
        rw [Metric.mem_ball, Real.dist_eq] at hy
        have := abs_sub_abs_le_abs_sub y y₁; linarith
      have h3 := mul_le_mul_of_nonneg_left h2 hB
      linarith
    · refine Filter.Eventually.of_forall fun D => ?_
      have : Continuous fun y => nextX y o D := by unfold nextX; fun_prop
      exact ((hcont (nextO o D)).comp this).continuousAt
  · -- measurability
    show Measurable fun p : ℝ × (Fin M → ℝ) => P.G s p.1 + P.α (s + 1) *
      ∫ D, P.J (s + 1) (nextX p.1 p.2 D) (nextO p.2 D) ∂(P.μ s)
    refine (hGc.measurable.comp measurable_fst).add (measurable_const.mul ?_)
    exact (hFmeas2.stronglyMeasurable.integral_prod_right' (ν := P.μ s)).measurable
  · -- upper bound
    refine ⟨a + P.α (s + 1) * (C + B * (L + M + 2) * ∫ D, aux_myb_n1 D ∂(P.μ s)),
      |b| + P.α (s + 1) * (B * (M + 1)),
      add_nonneg (abs_nonneg b) (mul_nonneg hαpos.le (mul_nonneg hB (by positivity))),
      fun y o => ?_⟩
    have h1 := hIup y o
    have h2 := mul_le_mul_of_nonneg_left h1 hαpos.le
    have h3 : P.G s y ≤ a + |b| * |y| := by
      have := hab y
      have := le_abs_self (P.G s y)
      have := mul_le_mul_of_nonneg_right (le_abs_self b) (abs_nonneg y)
      linarith
    have h4 := aux_myb_n1_nonneg o
    have h5 : P.α (s + 1) * B * |y| ≤ P.α (s + 1) * B * (M + 1) * |y| := by
      have h0 : 0 ≤ P.α (s + 1) * B * |y| := mul_nonneg (mul_nonneg hαpos.le hB) (abs_nonneg y)
      have hM : (0:ℝ) ≤ M := Nat.cast_nonneg M
      nlinarith [mul_nonneg h0 hM]
    have h6 : 0 ≤ |b| * aux_myb_n1 o := mul_nonneg (abs_nonneg b) h4
    show P.G s y + P.α (s + 1) * _ ≤ _
    nlinarith

lemma aux_myb_all (P : Model L M) : ∀ n, n ≤ P.T → aux_myb_Inv (P.J (P.T + 1 - n)) := by
  intro n
  induction n with
  | zero => intro _; rw [Nat.sub_zero]; exact aux_myb_base P
  | succ n ih =>
    intro hn
    have h := ih (by omega)
    have e1 : P.T + 1 - n = (P.T - n) + 1 := by omega
    rw [e1] at h
    have hV := (aux_myb_JV P (P.T - n) h).1
    have e2 : P.T + 1 - (n + 1) = P.T - n := by omega
    rw [e2]
    have hJ : P.J (P.T - n) =
        fun x o => orderCost (P.K (P.T - n)) (fun y => P.V (P.T - n) y o) x :=
      funext fun x => funext fun o => P.J_eq (P.T - n) (by omega) (by omega) x o
    rw [hJ]
    exact aux_myb_VJ (P.K_pos _) hV

/-! ### Properties of the single-period cost -/

lemma aux_myb_Gprops {G : ℝ → ℝ} (hconv : ConvexOn ℝ Set.univ G)
    (hcoer : Tendsto G (cocompact ℝ) atTop) :
    (∀ x, G (myopicOrderUpTo G) ≤ G x) ∧
    (∀ y, y < myopicOrderUpTo G → G (myopicOrderUpTo G) < G y) ∧
    (∀ y y', y ≤ y' → y' ≤ myopicOrderUpTo G → G y' ≤ G y) ∧
    (∀ y y', myopicOrderUpTo G ≤ y → y ≤ y' → G y ≤ G y') := by
  have hGc : Continuous G := continuousOn_univ.1 (hconv.continuousOn isOpen_univ)
  obtain ⟨y₀, hy₀⟩ := hGc.exists_forall_le hcoer
  have hne : ({y : ℝ | ∀ x, G y ≤ G x}).Nonempty := ⟨y₀, hy₀⟩
  have hbdd : BddBelow {y : ℝ | ∀ x, G y ≤ G x} := by
    have hev : ∀ᶠ y in cocompact ℝ, G y₀ < G y := hcoer.eventually_gt_atTop (G y₀)
    obtain ⟨Kc, hKc, hsub⟩ := mem_cocompact.1 hev
    refine hKc.bddBelow.mono fun y hy => ?_
    by_contra hyK
    have h1 : G y₀ < G y := hsub hyK
    have h2 : G y ≤ G y₀ := hy y₀
    linarith
  have hclosed : IsClosed {y : ℝ | ∀ x, G y ≤ G x} := by
    have : {y : ℝ | ∀ x, G y ≤ G x} = ⋂ x, {y | G y ≤ G x} := by ext y; simp
    rw [this]; exact isClosed_iInter fun x => isClosed_le hGc continuous_const
  have hmem : ∀ x, G (myopicOrderUpTo G) ≤ G x := hclosed.csInf_mem hne hbdd
  refine ⟨hmem, fun y hy => ?_, fun y y' h1 h2 => ?_, fun y y' h1 h2 => ?_⟩
  · by_contra h
    push Not at h
    have hyZ : y ∈ {y : ℝ | ∀ x, G y ≤ G x} := fun x => h.trans (hmem x)
    have := csInf_le hbdd hyZ
    unfold myopicOrderUpTo at hy
    linarith
  · have hz : y' ∈ segment ℝ y (myopicOrderUpTo G) := by
      rw [segment_eq_Icc (h1.trans h2)]; exact ⟨h1, h2⟩
    have := hconv.le_on_segment (Set.mem_univ _) (Set.mem_univ _) hz
    exact this.trans (max_le le_rfl (hmem y))
  · have hz : y ∈ segment ℝ (myopicOrderUpTo G) y' := by
      rw [segment_eq_Icc (h1.trans h2)]; exact ⟨h1, h2⟩
    have := hconv.le_on_segment (Set.mem_univ _) (Set.mem_univ _) hz
    exact this.trans (max_le (hmem y') le_rfl)

/-! ### Transitions preserve nonnegativity -/

lemma aux_myb_obs_nonneg {o : Fin M → ℝ} (ho : ∀ j, 0 ≤ o j) (j : ℕ) : 0 ≤ obsComp o j := by
  unfold obsComp; split_ifs
  · exact ho _
  · exact le_refl _

lemma aux_myb_nextO_nonneg {o : Fin M → ℝ} (ho : ∀ j, 0 ≤ o j) {D : Fin (L + M + 2) → ℝ}
    (hD : ∀ k, 0 ≤ D k) : ∀ j, 0 ≤ nextO o D j := fun j => by
  unfold nextO
  exact add_nonneg (aux_myb_obs_nonneg ho _) (hD _)

lemma aux_myb_nextX_mono {y y' : ℝ} (h : y ≤ y') (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ) :
    nextX y o D ≤ nextX y' o D := by
  unfold nextX; linarith

lemma aux_myb_nextX_le_self {o : Fin M → ℝ} (ho : ∀ j, 0 ≤ o j) {D : Fin (L + M + 2) → ℝ}
    (hD : ∀ k, 0 ≤ D k) (y : ℝ) : nextX y o D ≤ y := by
  unfold nextX
  have h1 : 0 ≤ ∑ k : Fin (L + 2), D (Fin.castLE (by omega) k) :=
    Finset.sum_nonneg fun k _ => hD _
  have h2 := aux_myb_obs_nonneg ho 0
  linarith

/-! ### Comparison properties of the order-cost operator -/

lemma aux_myb_ocanti {K : ℝ} (hK : 0 < K) {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) {b : ℝ}
    (hf : ∀ y y', y ≤ y' → y' ≤ b → f y' ≤ f y) {x x' : ℝ} (hxx : x ≤ x') (hx' : x' ≤ b) :
    orderCost K f x' ≤ orderCost K f x := by
  rw [aux_myb_oc_eq hK.le hc x]
  refine le_min ((aux_myb_oc_le_self hK.le hc x').trans (hf x x' hxx hx')) ?_
  have : orderCost K f x' - K ≤ aux_myb_m f x := aux_myb_le_m fun y hy => by
    rcases le_total y x' with h | h
    · have h1 := hf y x' h hx'
      have h2 := aux_myb_oc_le_self hK.le hc x'
      linarith
    · have := aux_myb_oc_le_K hK.le hc h
      linarith
  linarith

lemma aux_myb_ocK {K : ℝ} (hK : 0 < K) {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) {x x' : ℝ}
    (hxx : x ≤ x') : orderCost K f x ≤ K + orderCost K f x' := by
  rw [aux_myb_oc_eq hK.le hc x']
  have h1 := aux_myb_oc_le_K hK.le hc hxx
  have h2 : orderCost K f x - K ≤ aux_myb_m f x' := aux_myb_le_m fun y hy =>
    by have := aux_myb_oc_le_K hK.le hc (hxx.trans hy); linarith
  have h3 : orderCost K f x - K ≤ min (f x') (K + aux_myb_m f x') :=
    le_min (by linarith) (by linarith)
  linarith

/-! ### Monotonicity below the myopic level and the `K`-bound -/

lemma aux_myb_Vanti (P : Model L M) (G : ℝ → ℝ) (hG : ∀ t, P.G t = G) (s : ℕ)
    (hint : ∀ y o, Integrable (fun D => P.J (s + 1) (nextX y o D) (nextO o D)) (P.μ s))
    (hJ : ∀ o : Fin M → ℝ, (∀ j, 0 ≤ o j) → ∀ x x', x ≤ x' → x' ≤ myopicOrderUpTo G →
      P.J (s + 1) x' o ≤ P.J (s + 1) x o)
    (o : Fin M → ℝ) (ho : ∀ j, 0 ≤ o j) (y y' : ℝ) (hyy : y ≤ y')
    (hy' : y' ≤ myopicOrderUpTo G) :
    P.V s y' o ≤ P.V s y o := by
  have hconv : ConvexOn ℝ Set.univ G := by rw [← hG 0]; exact P.G_convex 0
  have hcoer : Tendsto G (cocompact ℝ) atTop := by rw [← hG 0]; exact P.G_coercive 0
  obtain ⟨-, -, hanti, -⟩ := aux_myb_Gprops hconv hcoer
  have hαpos := P.α_pos (s + 1)
  have hI : ∫ D, P.J (s + 1) (nextX y' o D) (nextO o D) ∂(P.μ s) ≤
      ∫ D, P.J (s + 1) (nextX y o D) (nextO o D) ∂(P.μ s) := by
    refine integral_mono_ae (hint y' o) (hint y o) ?_
    filter_upwards [P.μ_nonneg s] with D hD
    exact hJ _ (aux_myb_nextO_nonneg ho hD) _ _ (aux_myb_nextX_mono hyy o D)
      ((aux_myb_nextX_le_self ho hD y').trans hy')
  have h1 := mul_le_mul_of_nonneg_left hI hαpos.le
  have h2 := hanti y y' hyy hy'
  simp only [Model.V, hG]
  linarith

lemma aux_myb_mono (P : Model L M) (G : ℝ → ℝ) (hG : ∀ t, P.G t = G) : ∀ n, n ≤ P.T →
    ∀ o : Fin M → ℝ, (∀ j, 0 ≤ o j) → ∀ x x', x ≤ x' → x' ≤ myopicOrderUpTo G →
      P.J (P.T + 1 - n) x' o ≤ P.J (P.T + 1 - n) x o := by
  intro n
  induction n with
  | zero => intro _ o _ x x' _ _; rw [Nat.sub_zero, P.J_terminal, P.J_terminal]
  | succ n ih =>
    intro hn o ho x x' hxx hx'
    have h := ih (by omega)
    have e1 : P.T + 1 - n = (P.T - n) + 1 := by omega
    rw [e1] at h
    have hinv := aux_myb_all P n (by omega)
    rw [e1] at hinv
    obtain ⟨hVinv, hint⟩ := aux_myb_JV P (P.T - n) hinv
    obtain ⟨c, hc⟩ := hVinv.2.2.1
    have e2 : P.T + 1 - (n + 1) = P.T - n := by omega
    rw [e2, P.J_eq _ (by omega) (by omega), P.J_eq _ (by omega) (by omega)]
    exact aux_myb_ocanti (P.K_pos _) (hc · o)
      (fun y y' hyy hy' => aux_myb_Vanti P G hG (P.T - n) hint h o ho y y' hyy hy') hxx hx'

lemma aux_myb_Kb (P : Model L M) (s : ℕ) (hs1 : 1 ≤ s) (hsT : s ≤ P.T + 1) (o : Fin M → ℝ)
    {x x' : ℝ} (hxx : x ≤ x') : P.J s x o ≤ P.K s + P.J s x' o := by
  rcases eq_or_lt_of_le hsT with h | h
  · subst h; rw [P.J_terminal, P.J_terminal]; linarith [P.K_pos (P.T + 1)]
  · have hinv := aux_myb_all P (P.T - s) (by omega)
    rw [show P.T + 1 - (P.T - s) = s + 1 by omega] at hinv
    obtain ⟨c, hc⟩ := (aux_myb_JV P s hinv).1.2.2.1
    rw [P.J_eq s hs1 (by omega), P.J_eq s hs1 (by omega)]
    exact aux_myb_ocK (P.K_pos s) (hc · o) hxx

end GallegoOzerADI.PositiveSetup

open GallegoOzerADI.PositiveSetup

open MeasureTheory

theorem checked_myopic_bounds {L M : ℕ} [NeZero M] (P : Model L M) (G : ℝ → ℝ) (K α : ℝ)
    (ν : Measure (Fin (L + M + 2) → ℝ)) (hG : ∀ t, P.G t = G) (hK : ∀ t, P.K t = K)
    (hα : ∀ t, P.α t = α) (_hμ : ∀ t, P.μ t = ν) (t : ℕ) (ht₁ : 1 ≤ t) (htT : t ≤ P.T)
    (o : Fin M → ℝ) (ho : ∀ j, 0 ≤ o j) (S s : ℝ)
    (hS : IsLeast {y | ∀ x, P.V t y o ≤ P.V t x o} S)
    (hs : IsGreatest {x | P.H t x o ≤ 0} s) :
    myopicOrderUpTo G ≤ S ∧ S ≤ myopicUpperLevel G K α ∧ myopicReorderPoint G K ≤ s := by
  have hconv : ConvexOn ℝ Set.univ G := by rw [← hG 0]; exact P.G_convex 0
  have hcoer : Filter.Tendsto G (Filter.cocompact ℝ) Filter.atTop := by
    rw [← hG 0]; exact P.G_coercive 0
  have hKpos : 0 < K := by rw [← hK 0]; exact P.K_pos 0
  have hαpos : 0 < α := by rw [← hα 0]; exact P.α_pos 0
  obtain ⟨hmin, hstrict, hanti, hmono⟩ := aux_myb_Gprops hconv hcoer
  have hinv := aux_myb_all P (P.T - t) (by omega)
  rw [show P.T + 1 - (P.T - t) = t + 1 by omega] at hinv
  obtain ⟨-, hFint⟩ := aux_myb_JV P t hinv
  have := P.μ_prob t
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ,
      F = fun y => ∫ D, P.J (t + 1) (nextX y o D) (nextO o D) ∂(P.μ t) := ⟨_, rfl⟩
  have hV : ∀ y, P.V t y o = G y + α * F y := fun y => by
    simp only [Model.V, hG, hα, hF]
  have hm := aux_myb_mono P G hG (P.T - t) (by omega)
  rw [show P.T + 1 - (P.T - t) = t + 1 by omega] at hm
  have hF1 : ∀ y y', y ≤ y' → y' ≤ myopicOrderUpTo G → F y' ≤ F y := by
    intro y y' hyy hy'
    simp only [hF]
    refine integral_mono_ae (hFint y' o) (hFint y o) ?_
    filter_upwards [P.μ_nonneg t] with D hD
    exact hm _ (aux_myb_nextO_nonneg ho hD) _ _ (aux_myb_nextX_mono hyy o D)
      ((aux_myb_nextX_le_self ho hD y').trans hy')
  have hKb := aux_myb_Kb P (t + 1) (by omega) (by omega)
  have hF2 : ∀ y y', y ≤ y' → F y ≤ K + F y' := by
    intro y y' hyy
    simp only [hF]
    have hpt : ∀ D : Fin (L + M + 2) → ℝ, P.J (t + 1) (nextX y o D) (nextO o D) ≤
        K + P.J (t + 1) (nextX y' o D) (nextO o D) := fun D => by
      have := hKb (nextO o D) (aux_myb_nextX_mono hyy o D)
      rwa [hK] at this
    have hg : Integrable (fun D => K + P.J (t + 1) (nextX y' o D) (nextO o D)) (P.μ t) :=
      (integrable_const K).add (hFint y' o)
    have := integral_mono (hFint y o) hg hpt
    rw [integral_add (integrable_const K) (hFint y' o)] at this
    simpa using this
  -- the least minimizer lies above the myopic level
  have c1 : myopicOrderUpTo G ≤ S := by
    by_contra hlt
    push Not at hlt
    have h1 : P.V t S o ≤ P.V t (myopicOrderUpTo G) o := hS.1 _
    rw [hV, hV] at h1
    have h2 := hF1 S (myopicOrderUpTo G) hlt.le le_rfl
    have h3 := hstrict S hlt
    have h4 := mul_le_mul_of_nonneg_left h2 hαpos.le
    linarith
  -- the upper bound
  have hGS : G S ≤ G (myopicOrderUpTo G) + α * K := by
    have h1 : P.V t S o ≤ P.V t (myopicOrderUpTo G) o := hS.1 _
    rw [hV, hV] at h1
    have h2 := hF2 (myopicOrderUpTo G) S c1
    have h3 := mul_le_mul_of_nonneg_left h2 hαpos.le
    rw [mul_add] at h3
    linarith
  have htop : Filter.Tendsto G Filter.atTop Filter.atTop := hcoer.mono_left atTop_le_cocompact
  have hbot : Filter.Tendsto G Filter.atBot Filter.atTop := hcoer.mono_left atBot_le_cocompact
  have c2 : S ≤ myopicUpperLevel G K α := by
    unfold myopicUpperLevel
    obtain ⟨y0, hy0⟩ := ((Filter.eventually_gt_atTop (myopicOrderUpTo G)).and
      (htop.eventually_gt_atTop (G (myopicOrderUpTo G) + α * K))).exists
    refine le_csInf ⟨y0, hy0⟩ fun y hy => ?_
    by_contra hlt
    push Not at hlt
    have := hmono y S hy.1.le hlt.le
    linarith [hy.2]
  have c3 : myopicReorderPoint G K ≤ s := by
    unfold myopicReorderPoint
    obtain ⟨y0, hy0⟩ := ((Filter.eventually_le_atBot (myopicOrderUpTo G)).and
      (hbot.eventually_ge_atTop (K + G (myopicOrderUpTo G)))).exists
    refine csSup_le ⟨y0, hy0⟩ fun y hy => hs.2 ?_
    show P.K t + (⨅ z : {z : ℝ // y ≤ z}, P.V t z o) - P.V t y o ≤ 0
    have hbdd : BddBelow (Set.range fun z : {z : ℝ // y ≤ z} => P.V t z o) :=
      ⟨P.V t S o, by rintro _ ⟨z, rfl⟩; exact hS.1 z⟩
    have h1 : (⨅ z : {z : ℝ // y ≤ z}, P.V t z o) ≤ P.V t (myopicOrderUpTo G) o :=
      ciInf_le hbdd ⟨_, hy.1⟩
    have h2 := hF1 y (myopicOrderUpTo G) hy.1 le_rfl
    have h3 := mul_le_mul_of_nonneg_left h2 hαpos.le
    rw [hV (myopicOrderUpTo G)] at h1
    rw [hV y, hK t]
    linarith [hy.2]
  exact ⟨c1, c2, c3⟩
end

/- Complete attributed body: Sol_GallegoOzerADI_PositiveSetup_sS_policy_optimal -/
section
-- Prove2me | solution 1 for GallegoOzerADI.PositiveSetup.sS_policy_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:40:59.297702+00:00
-- url     : https://prove2.me/submissions/4cf5d748-7666-4a88-8948-82fb2b48dae7


open MeasureTheory Filter Topology

namespace GallegoOzerADI.PositiveSetup

def aux_so_KC (K : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
    f (θ * x₁ + (1 - θ) * x₂) ≤ θ * f x₁ + (1 - θ) * (K + f x₂)

lemma aux_so_KC_three {K : ℝ} {f : ℝ → ℝ} (hf : aux_so_KC K f) {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hac : a < c) :
    (c - a) * f b ≤ (c - b) * f a + (b - a) * (K + f c) := by
  have hca : 0 < c - a := by linarith
  set θ := (c - b) / (c - a) with hθ
  have h0 : 0 ≤ θ := div_nonneg (by linarith) hca.le
  have h1 : θ ≤ 1 := (div_le_one hca).2 (by linarith)
  have e1 : (c - a) * θ = c - b := by rw [hθ]; field_simp
  have e2 : (c - a) * (1 - θ) = b - a := by rw [mul_sub, e1]; ring
  have hb : θ * a + (1 - θ) * c = b := by
    have : (c - a) * (θ * a + (1 - θ) * c) = (c - a) * b := by
      have : (c - a) * (θ * a + (1 - θ) * c) = ((c - a) * θ) * a + ((c - a) * (1 - θ)) * c := by
        ring
      rw [this, e1, e2]; ring
    exact mul_left_cancel₀ hca.ne' this
  have := hf a c hac.le θ h0 h1
  rw [hb] at this
  calc (c - a) * f b ≤ (c - a) * (θ * f a + (1 - θ) * (K + f c)) :=
        mul_le_mul_of_nonneg_left this hca.le
    _ = ((c - a) * θ) * f a + ((c - a) * (1 - θ)) * (K + f c) := by ring
    _ = (c - b) * f a + (b - a) * (K + f c) := by rw [e1, e2]

lemma aux_so_min_attained {f : ℝ → ℝ} (hc : Continuous f)
    (hco : Tendsto f (cocompact ℝ) atTop) (x : ℝ) :
    ∃ y, x ≤ y ∧ ∀ z, x ≤ z → f y ≤ f z := by
  obtain ⟨y, hy, hmin⟩ := hc.continuousOn.exists_isMinOn' (s := Set.Ici x) isClosed_Ici
    Set.self_mem_Ici (((hco.eventually (eventually_ge_atTop (f x)))).filter_mono inf_le_left)
  exact ⟨y, hy, fun z hz => hmin hz⟩

lemma aux_so_scarf {K : ℝ} (hK : 0 < K) {f : ℝ → ℝ} (hc : Continuous f)
    (hkc : aux_so_KC K f) (hco : Tendsto f (cocompact ℝ) atTop) :
    ∃ S s : ℝ, IsLeast {y | ∀ x, f y ≤ f x} S ∧ IsGreatest {x | reorderGap K f x ≤ 0} s ∧
      s < S ∧ f s = K + f S ∧ (∀ x, orderCost K f x = f (max x s)) ∧
      (∀ x, orderCost K f x =
        ⨅ q : ℚ, (K * setupIndicator (max (q : ℝ) x - x) + f (max (q : ℝ) x))) ∧
      (∀ x, orderCost K f x ≤ f x) ∧ aux_so_KC K (fun x => orderCost K f x) := by
  have hbot : Tendsto f atBot atTop :=
    hco.mono_left (by rw [cocompact_eq_atBot_atTop]; exact le_sup_left)
  obtain ⟨y₀, hy₀⟩ := hc.exists_forall_le hco
  -- the least minimizer
  set Mset := {y | ∀ x, f y ≤ f x} with hMset
  have hMcl : IsClosed Mset := by
    simp only [hMset, Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_le hc continuous_const
  obtain ⟨R, hR⟩ := (tendsto_atBot_atTop.1 hbot) (f y₀ + 1)
  have hMbdd : BddBelow Mset := by
    refine ⟨R, fun y hy => ?_⟩
    by_contra h
    push Not at h
    have := hR y h.le
    have := hy y₀
    linarith
  have hMne : Mset.Nonempty := ⟨y₀, hy₀⟩
  set S := sInf Mset with hSdef
  have hSM : S ∈ Mset := hMcl.csInf_mem hMne hMbdd
  have hSmin : ∀ x, f S ≤ f x := hSM
  -- the reorder point
  set A := {x | x ≤ S ∧ K + f S ≤ f x} with hAdef
  have hAcl : IsClosed A := (isClosed_le continuous_id continuous_const).inter
    (isClosed_le continuous_const hc)
  obtain ⟨R', hR'⟩ := (tendsto_atBot_atTop.1 hbot) (K + f S)
  have hAne : A.Nonempty := ⟨min R' S, min_le_right _ _, hR' _ (min_le_left _ _)⟩
  have hAbdd : BddAbove A := ⟨S, fun x hx => hx.1⟩
  set s := sSup A with hsdef
  have hsA : s ∈ A := hAcl.csSup_mem hAne hAbdd
  have hsS : s < S := by
    rcases lt_or_eq_of_le hsA.1 with h | h
    · exact h
    · exfalso
      have := hsA.2
      rw [h] at this
      linarith
  have hfs : f s = K + f S := by
    have hmem : K + f S ∈ Set.Icc (f S) (f s) := ⟨by linarith, hsA.2⟩
    obtain ⟨c, hc1, hc2⟩ := intermediate_value_Icc' hsS.le hc.continuousOn hmem
    have hcA : c ∈ A := ⟨hc1.2, hc2.ge⟩
    have : c ≤ s := le_csSup hAbdd hcA
    have hcs : c = s := le_antisymm this hc1.1
    rw [← hcs, hc2]
  -- key facts
  have F1 : ∀ x, x ≤ s → K + f S ≤ f x := by
    intro x hx
    have h3 := aux_so_KC_three hkc hx hsS.le (lt_of_le_of_lt hx hsS)
    rw [hfs] at h3
    have hpos : 0 < S - s := by linarith
    have : (S - s) * (K + f S) ≤ (S - s) * f x := by nlinarith
    exact le_of_mul_le_mul_left this hpos
  have F2 : ∀ x, s < x → x ≤ S → f x < K + f S := by
    intro x hx hxS
    by_contra h
    push Not at h
    have : x ≤ s := le_csSup hAbdd ⟨hxS, h⟩
    linarith
  have F3 : ∀ x y, S ≤ x → x ≤ y → f x < K + f y := by
    intro x y hx hxy
    rcases lt_or_eq_of_le hxy with h | h
    · have hSy : S < y := lt_of_le_of_lt hx h
      have h3 := aux_so_KC_three hkc hx hxy hSy
      have h4 : (y - x) * f S < (y - x) * (K + f y) :=
        mul_lt_mul_of_pos_left (by linarith [hSmin y]) (by linarith)
      have hpos : 0 < y - S := by linarith
      have : (y - S) * f x < (y - S) * (K + f y) := by nlinarith
      exact lt_of_mul_lt_mul_left this hpos.le
    · rw [h]; linarith
  have F4 : ∀ x y, s < x → x ≤ y → f x < K + f y := by
    intro x y hx hxy
    rcases le_or_gt x S with h | h
    · linarith [F2 x hx h, hSmin y]
    · exact F3 x y h.le hxy
  have lower : ∀ x y, x ≤ y → f (max x s) ≤ K * setupIndicator (y - x) + f y := by
    intro x y hxy
    rcases le_or_gt x s with hx | hx
    · rw [max_eq_right hx, hfs]
      by_cases hy : 0 < y - x
      · simp only [setupIndicator, hy, if_true, mul_one]
        linarith [hSmin y]
      · have : y = x := by linarith
        subst this
        simp only [setupIndicator, sub_self, lt_irrefl, if_false, mul_zero, zero_add]
        exact F1 y hx
    · rw [max_eq_left hx.le]
      by_cases hy : 0 < y - x
      · simp only [setupIndicator, hy, if_true, mul_one]
        exact (F4 x y hx hxy).le
      · have : y = x := by linarith
        simp [setupIndicator, this]
  have attain : ∀ x, ∃ y, x ≤ y ∧ K * setupIndicator (y - x) + f y = f (max x s) := by
    intro x
    rcases le_or_gt x s with hx | hx
    · refine ⟨S, by linarith, ?_⟩
      have : 0 < S - x := by linarith
      simp only [setupIndicator, this, if_true, mul_one, max_eq_right hx, hfs]
    · refine ⟨x, le_rfl, ?_⟩
      simp [setupIndicator, max_eq_left hx.le]
  have hJ : ∀ x, orderCost K f x = f (max x s) := by
    intro x
    have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_rfl⟩⟩
    unfold orderCost
    have hbdd : BddBelow (Set.range fun y : {y : ℝ // x ≤ y} =>
        K * setupIndicator ((y : ℝ) - x) + f y) := by
      refine ⟨f (max x s), ?_⟩
      rintro _ ⟨y, rfl⟩
      exact lower x y y.2
    apply le_antisymm
    · obtain ⟨y, hy, heq⟩ := attain x
      exact (ciInf_le hbdd ⟨y, hy⟩).trans_eq heq
    · exact le_ciInf fun y => lower x y y.2
  have hQ : ∀ x, orderCost K f x =
      ⨅ q : ℚ, (K * setupIndicator (max (q : ℝ) x - x) + f (max (q : ℝ) x)) := by
    intro x
    rw [hJ x]
    symm
    have hbdd : BddBelow (Set.range fun q : ℚ =>
        K * setupIndicator (max (q : ℝ) x - x) + f (max (q : ℝ) x)) := by
      refine ⟨f (max x s), ?_⟩
      rintro _ ⟨q, rfl⟩
      exact lower x _ (le_max_right _ _)
    apply le_antisymm
    · rcases le_or_gt x s with hx | hx
      · by_contra hlt
        push Not at hlt
        set c₀ := ⨅ q : ℚ, (K * setupIndicator (max (q : ℝ) x - x) + f (max (q : ℝ) x))
        rw [max_eq_right hx, hfs] at hlt
        have hε : 0 < c₀ - K - f S := by linarith
        obtain ⟨δ, hδ, hδf⟩ := Metric.continuous_iff.1 hc S (c₀ - K - f S) hε
        have hxS : max x (S - δ) < S := max_lt (by linarith) (by linarith)
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hxS
        have hqx : x < q := lt_of_le_of_lt (le_max_left _ _) hq1
        have hqd : S - δ < q := lt_of_le_of_lt (le_max_right _ _) hq1
        have hfq : f q < c₀ - K := by
          have := hδf q (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
          rw [Real.dist_eq, abs_lt] at this
          linarith [this.2]
        have hle : c₀ ≤ K * setupIndicator (max (q : ℝ) x - x) + f (max (q : ℝ) x) :=
          ciInf_le hbdd q
        have hmax : max (q : ℝ) x = q := max_eq_left hqx.le
        have hpos : 0 < (q : ℝ) - x := by linarith
        have hind : setupIndicator ((q : ℝ) - x) = 1 := by simp [setupIndicator, hpos]
        rw [hmax, hind] at hle
        linarith
      · obtain ⟨q, hq⟩ := exists_rat_lt x
        have hle := ciInf_le hbdd q
        have hmax : max (q : ℝ) x = x := max_eq_right hq.le
        simp only [hmax, sub_self, setupIndicator, lt_irrefl, if_false, mul_zero,
          zero_add] at hle
        rw [max_eq_left hx.le]
        exact hle
    · exact le_ciInf fun q => lower x _ (le_max_right _ _)
  refine ⟨S, s, ⟨hSM, fun y hy => csInf_le hMbdd hy⟩, ⟨?_, ?_⟩, hsS, hfs, hJ, hQ, ?_, ?_⟩
  · -- s is in the reorder set
    show reorderGap K f s ≤ 0
    unfold reorderGap
    have : Nonempty {y : ℝ // s ≤ y} := ⟨⟨s, le_rfl⟩⟩
    have hbdd : BddBelow (Set.range fun y : {y : ℝ // s ≤ y} => f y) :=
      ⟨f S, by rintro _ ⟨y, rfl⟩; exact hSmin y⟩
    have : (⨅ y : {y : ℝ // s ≤ y}, f y) = f S :=
      le_antisymm (ciInf_le hbdd ⟨S, hsS.le⟩) (le_ciInf fun y => hSmin y)
    rw [this, hfs]; linarith
  · intro x hx
    change reorderGap K f x ≤ 0 at hx
    by_contra hxs
    push Not at hxs
    obtain ⟨y, hy, hymin⟩ := aux_so_min_attained hc hco x
    unfold reorderGap at hx
    have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_rfl⟩⟩
    have hbdd : BddBelow (Set.range fun y : {y : ℝ // x ≤ y} => f y) :=
      ⟨f S, by rintro _ ⟨y, rfl⟩; exact hSmin y⟩
    have : (⨅ y : {y : ℝ // x ≤ y}, f y) = f y :=
      le_antisymm (ciInf_le hbdd ⟨y, hy⟩) (le_ciInf fun z => hymin z z.2)
    rw [this] at hx
    have := F4 x y hxs hy
    linarith
  · intro x
    rw [hJ x]
    rcases le_or_gt x s with hx | hx
    · rw [max_eq_right hx, hfs]; exact F1 x hx
    · rw [max_eq_left hx.le]
  · -- K-convexity of the optimal cost
    have hfun : (fun x => orderCost K f x) = fun x => f (max x s) := funext hJ
    rw [hfun]
    intro x₁ x₂ hx θ h0 h1
    beta_reduce
    set x := θ * x₁ + (1 - θ) * x₂ with hxdef
    have hx1 : x₁ ≤ x := by nlinarith
    have hx2 : x ≤ x₂ := by nlinarith
    rcases lt_or_ge s x₁ with hs1 | hs1
    · rw [max_eq_left (by linarith : s ≤ x), max_eq_left hs1.le,
        max_eq_left (by linarith : s ≤ x₂)]
      exact hkc x₁ x₂ hx θ h0 h1
    · rw [max_eq_right hs1]
      rcases le_or_gt x₂ s with hs2 | hs2
      · rw [max_eq_right (by linarith : x ≤ s), max_eq_right hs2]
        nlinarith
      · rw [max_eq_left hs2.le]
        have hD : f s ≤ K + f x₂ := by rw [hfs]; linarith [hSmin x₂]
        rcases le_or_gt x s with hxs | hxs
        · rw [max_eq_right hxs]
          nlinarith
        · rw [max_eq_left hxs.le]
          have h3 := aux_so_KC_three hkc hxs.le hx2 hs2
          have hprod : 0 ≤ θ * (K + f x₂ - f s) * (s - x₁) :=
            mul_nonneg (mul_nonneg h0 (by linarith)) (by linarith)
          have hpos : 0 < x₂ - s := by linarith
          have : (x₂ - s) * f x ≤ (x₂ - s) * (θ * f s + (1 - θ) * (K + f x₂)) := by
            rw [hxdef] at h3 ⊢
            nlinarith
          exact le_of_mul_le_mul_left this hpos

variable {L M : ℕ}

noncomputable def aux_so_W (P : Model L M) (p : ℕ) (F : ℝ → (Fin M → ℝ) → ℝ) (y : ℝ)
    (o : Fin M → ℝ) : ℝ :=
  P.G p y + P.α (p + 1) * ∫ D, F (nextX y o D) (nextO o D) ∂(P.μ p)

def aux_so_Good (F : ℝ → (Fin M → ℝ) → ℝ) (k : ℝ) : Prop :=
  Measurable (fun q : ℝ × (Fin M → ℝ) => F q.1 q.2) ∧
  (∀ o, Continuous fun x => F x o) ∧
  (∀ o, aux_so_KC k (fun x => F x o)) ∧
  (∃ c, ∀ x o, c ≤ F x o) ∧
  (∃ a b, 0 ≤ b ∧ ∀ x o, F x o ≤ a + b * (|x| + ‖o‖))

lemma aux_so_obsComp_cont (j : ℕ) : Continuous (fun o : Fin M → ℝ => obsComp o j) := by
  unfold obsComp
  by_cases h : j < M
  · simp only [h, dif_pos]; exact continuous_apply _
  · simp only [h, dif_neg, not_false_eq_true]; exact continuous_const

lemma aux_so_obsComp_le (o : Fin M → ℝ) (j : ℕ) : |obsComp o j| ≤ ‖o‖ := by
  unfold obsComp
  split_ifs with h
  · rw [← Real.norm_eq_abs]; exact norm_le_pi_norm o _
  · simp

lemma aux_so_trans_cont : Continuous (fun z : (ℝ × (Fin M → ℝ)) × (Fin (L + M + 2) → ℝ) =>
    ((nextX z.1.1 z.1.2 z.2, nextO z.1.2 z.2) : ℝ × (Fin M → ℝ))) := by
  refine Continuous.prodMk ?_ ?_
  · unfold nextX
    refine ((continuous_fst.comp continuous_fst).sub ?_).sub
      ((aux_so_obsComp_cont 0).comp (continuous_snd.comp continuous_fst))
    exact continuous_finsetSum _ fun k _ => (continuous_apply _).comp continuous_snd
  · unfold nextO
    refine continuous_pi fun j => ?_
    exact ((aux_so_obsComp_cont _).comp (continuous_snd.comp continuous_fst)).add
      ((continuous_apply _).comp continuous_snd)

lemma aux_so_nextX_le (y : ℝ) (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ) :
    |nextX y o D| ≤ |y| + ((L : ℝ) + 2) * ∑ k, |D k| + ‖o‖ := by
  unfold nextX
  have h1 : |∑ k : Fin (L + 2), D (Fin.castLE (by omega) k)| ≤ ((L : ℝ) + 2) * ∑ k, |D k| := by
    calc _ ≤ ∑ k : Fin (L + 2), |D (Fin.castLE (by omega) k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin (L + 2), ∑ k', |D k'| := Finset.sum_le_sum fun k _ =>
          Finset.single_le_sum (f := fun k' => |D k'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ _)
      _ = _ := by simp
  have h2 := aux_so_obsComp_le o 0
  have h1' := abs_le.1 h1
  have h2' := abs_le.1 h2
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [le_abs_self y, neg_abs_le y]

lemma aux_so_nextO_le (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ) :
    ‖nextO o D‖ ≤ ‖o‖ + ∑ k, |D k| := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  unfold nextO
  rw [Real.norm_eq_abs]
  have h1 := aux_so_obsComp_le o (j.val + 1)
  have h2 : |D ⟨L + 2 + j.val, by have := j.isLt; omega⟩| ≤ ∑ k, |D k| :=
    Finset.single_le_sum (f := fun k => |D k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

lemma aux_so_pt_bound {F : ℝ → (Fin M → ℝ) → ℝ} {c a b : ℝ} (hb : 0 ≤ b)
    (hc : ∀ x o, c ≤ F x o) (hab : ∀ x o, F x o ≤ a + b * (|x| + ‖o‖))
    (y : ℝ) (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ) :
    ‖F (nextX y o D) (nextO o D)‖ ≤
      (|c| + |a| + b * (|y| + 2 * ‖o‖)) + b * ((L : ℝ) + 3) * ∑ k, |D k| := by
  rw [Real.norm_eq_abs]
  have h1 := aux_so_nextX_le y o D
  have h2 := aux_so_nextO_le o D
  have hs : 0 ≤ |nextX y o D| + ‖nextO o D‖ := by positivity
  have h3 : b * (|nextX y o D| + ‖nextO o D‖) ≤ b * (|y| + 2 * ‖o‖) + b * ((L : ℝ) + 3) * ∑ k, |D k| := by
    have : |nextX y o D| + ‖nextO o D‖ ≤ (|y| + 2 * ‖o‖) + ((L : ℝ) + 3) * ∑ k, |D k| := by
      linarith
    calc b * (|nextX y o D| + ‖nextO o D‖) ≤ b * ((|y| + 2 * ‖o‖) + ((L : ℝ) + 3) * ∑ k, |D k|) :=
          mul_le_mul_of_nonneg_left this hb
      _ = _ := by ring
  have h4 := hc (nextX y o D) (nextO o D)
  have h5 := hab (nextX y o D) (nextO o D)
  have h6 : 0 ≤ b * (|nextX y o D| + ‖nextO o D‖) := mul_nonneg hb hs
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [le_abs_self a, neg_abs_le c, abs_nonneg a, abs_nonneg c]

lemma aux_so_sumD_int (P : Model L M) (p : ℕ) :
    Integrable (fun D : Fin (L + M + 2) → ℝ => ∑ k, |D k|) (P.μ p) :=
  integrable_finsetSum _ fun k _ => (P.μ_integrable p k).abs

lemma aux_so_meas_D {F : ℝ → (Fin M → ℝ) → ℝ}
    (hF : Measurable (fun q : ℝ × (Fin M → ℝ) => F q.1 q.2)) (y : ℝ) (o : Fin M → ℝ) :
    Measurable (fun D : Fin (L + M + 2) → ℝ => F (nextX y o D) (nextO o D)) := by
  have hc : Continuous (fun D : Fin (L + M + 2) → ℝ =>
      ((nextX y o D, nextO o D) : ℝ × (Fin M → ℝ))) :=
    (aux_so_trans_cont (L := L) (M := M)).comp
      (continuous_const.prodMk continuous_id :
        Continuous fun D : Fin (L + M + 2) → ℝ => ((y, o), D))
  exact hF.comp hc.measurable

lemma aux_so_integrable (P : Model L M) (p : ℕ) {F : ℝ → (Fin M → ℝ) → ℝ} {k : ℝ}
    (hF : aux_so_Good F k) (y : ℝ) (o : Fin M → ℝ) :
    Integrable (fun D => F (nextX y o D) (nextO o D)) (P.μ p) := by
  have := P.μ_prob p
  obtain ⟨c, hc⟩ := hF.2.2.2.1
  obtain ⟨a, b, hb, hab⟩ := hF.2.2.2.2
  refine Integrable.mono' ((integrable_const (|c| + |a| + b * (|y| + 2 * ‖o‖))).add ((aux_so_sumD_int P p).const_mul
    (b * ((L : ℝ) + 3)))) (aux_so_meas_D hF.1 y o).aestronglyMeasurable ?_
  exact Eventually.of_forall fun D => aux_so_pt_bound hb hc hab y o D

lemma aux_so_G_cont (P : Model L M) (p : ℕ) : Continuous (P.G p) :=
  continuousOn_univ.1 ((P.G_convex p).continuousOn isOpen_univ)

lemma aux_so_W_cont (P : Model L M) (p : ℕ) {F : ℝ → (Fin M → ℝ) → ℝ} {k : ℝ}
    (hF : aux_so_Good F k) (o : Fin M → ℝ) : Continuous (fun y => aux_so_W P p F y o) := by
  have := P.μ_prob p
  obtain ⟨c, hc⟩ := hF.2.2.2.1
  obtain ⟨a, b, hb, hab⟩ := hF.2.2.2.2
  unfold aux_so_W
  refine (aux_so_G_cont P p).add (continuous_const.mul ?_)
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  refine continuousAt_of_dominated (bound := fun D =>
      (|c| + |a| + b * ((|y₀| + 1) + 2 * ‖o‖)) + b * ((L : ℝ) + 3) * ∑ k, |D k|)
    (Eventually.of_forall fun y => (aux_so_integrable P p hF y o).aestronglyMeasurable) ?_
    ((integrable_const _).add ((aux_so_sumD_int P p).const_mul _)) ?_
  · filter_upwards [Metric.ball_mem_nhds y₀ one_pos] with y hy
    refine Eventually.of_forall fun D => (aux_so_pt_bound hb hc hab y o D).trans ?_
    have : |y| ≤ |y₀| + 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hy
      have := abs_sub_abs_le_abs_sub y y₀
      linarith
    have := mul_le_mul_of_nonneg_left this hb
    nlinarith
  · refine Eventually.of_forall fun D => ?_
    have h1 : Continuous (fun y => nextX y o D) := by
      unfold nextX; exact (continuous_id.sub continuous_const).sub continuous_const
    exact ((hF.2.1 (nextO o D)).comp h1).continuousAt

lemma aux_so_int_const (P : Model L M) (p : ℕ) (c : ℝ) :
    ∫ _D, c ∂(P.μ p) = c := by
  have := P.μ_prob p
  simp

lemma aux_so_W_KC (P : Model L M) (p : ℕ) {F : ℝ → (Fin M → ℝ) → ℝ} {k : ℝ}
    (hF : aux_so_Good F k) (hk : P.α (p + 1) * k ≤ P.K p) (o : Fin M → ℝ) :
    aux_so_KC (P.K p) (fun y => aux_so_W P p F y o) := by
  intro y₁ y₂ hy θ h0 h1
  have := P.μ_prob p
  have hI := fun y => aux_so_integrable P p hF y o
  have hpt : ∀ D : Fin (L + M + 2) → ℝ, F (nextX (θ * y₁ + (1 - θ) * y₂) o D) (nextO o D) ≤
      θ * F (nextX y₁ o D) (nextO o D) + (1 - θ) * (k + F (nextX y₂ o D) (nextO o D)) := by
    intro D
    have e : nextX (θ * y₁ + (1 - θ) * y₂) o D =
        θ * nextX y₁ o D + (1 - θ) * nextX y₂ o D := by unfold nextX; ring
    rw [e]
    exact hF.2.2.1 (nextO o D) _ _ (by unfold nextX; linarith) θ h0 h1
  have hint2 : Integrable (fun D => θ * F (nextX y₁ o D) (nextO o D) +
      (1 - θ) * (k + F (nextX y₂ o D) (nextO o D))) (P.μ p) :=
    ((hI y₁).const_mul θ).add (((integrable_const k).add (hI y₂)).const_mul (1 - θ))
  have hint : ∫ D, F (nextX (θ * y₁ + (1 - θ) * y₂) o D) (nextO o D) ∂(P.μ p) ≤
      θ * ∫ D, F (nextX y₁ o D) (nextO o D) ∂(P.μ p) +
        (1 - θ) * (k + ∫ D, F (nextX y₂ o D) (nextO o D) ∂(P.μ p)) := by
    calc _ ≤ ∫ D, (θ * F (nextX y₁ o D) (nextO o D) +
          (1 - θ) * (k + F (nextX y₂ o D) (nextO o D))) ∂(P.μ p) :=
          integral_mono (hI _) hint2 hpt
      _ = _ := by
          have hk2 : Integrable (fun D => k + F (nextX y₂ o D) (nextO o D)) (P.μ p) :=
            (integrable_const k).add (hI y₂)
          have e1 : ∫ D, (θ * F (nextX y₁ o D) (nextO o D) +
              (1 - θ) * (k + F (nextX y₂ o D) (nextO o D))) ∂(P.μ p) =
              ∫ D, θ * F (nextX y₁ o D) (nextO o D) ∂(P.μ p) +
              ∫ D, (1 - θ) * (k + F (nextX y₂ o D) (nextO o D)) ∂(P.μ p) :=
            integral_add ((hI y₁).const_mul θ) (hk2.const_mul (1 - θ))
          have e2 : ∫ D, (k + F (nextX y₂ o D) (nextO o D)) ∂(P.μ p) =
              ∫ _D, k ∂(P.μ p) + ∫ D, F (nextX y₂ o D) (nextO o D) ∂(P.μ p) :=
            integral_add (integrable_const k) (hI y₂)
          rw [e1, integral_const_mul, integral_const_mul, e2, aux_so_int_const]
  have hG := (P.G_convex p).2 (Set.mem_univ y₁) (Set.mem_univ y₂) h0 (by linarith : 0 ≤ 1 - θ)
    (by ring : θ + (1 - θ) = 1)
  simp only [smul_eq_mul] at hG
  unfold aux_so_W
  have hα := P.α_pos (p + 1)
  have h3 := mul_le_mul_of_nonneg_left hint hα.le
  have h4 : 0 ≤ (1 - θ) * (P.K p - P.α (p + 1) * k) := mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma aux_so_W_lower (P : Model L M) (p : ℕ) {F : ℝ → (Fin M → ℝ) → ℝ} {k c : ℝ}
    (hF : aux_so_Good F k) (hc : ∀ x o, c ≤ F x o) (y : ℝ) (o : Fin M → ℝ) :
    P.G p y + P.α (p + 1) * c ≤ aux_so_W P p F y o := by
  have := P.μ_prob p
  unfold aux_so_W
  have : c ≤ ∫ D, F (nextX y o D) (nextO o D) ∂(P.μ p) := by
    calc c = ∫ _D, c ∂(P.μ p) := (aux_so_int_const P p c).symm
      _ ≤ _ := integral_mono (integrable_const c) (aux_so_integrable P p hF y o)
          (fun D => hc _ _)
  have := mul_le_mul_of_nonneg_left this (P.α_pos (p + 1)).le
  linarith

lemma aux_so_W_coer (P : Model L M) (p : ℕ) {F : ℝ → (Fin M → ℝ) → ℝ} {k : ℝ}
    (hF : aux_so_Good F k) (o : Fin M → ℝ) :
    Tendsto (fun y => aux_so_W P p F y o) (cocompact ℝ) atTop := by
  obtain ⟨c, hc⟩ := hF.2.2.2.1
  exact tendsto_atTop_mono (fun y => aux_so_W_lower P p hF hc y o)
    (tendsto_atTop_add_const_right _ _ (P.G_coercive p))

lemma aux_so_W_upper (P : Model L M) (p : ℕ) {F : ℝ → (Fin M → ℝ) → ℝ} {k : ℝ}
    (hF : aux_so_Good F k) :
    ∃ a b, 0 ≤ b ∧ ∀ y o, aux_so_W P p F y o ≤ a + b * (|y| + ‖o‖) := by
  have := P.μ_prob p
  obtain ⟨c, hc⟩ := hF.2.2.2.1
  obtain ⟨a, b, hb, hab⟩ := hF.2.2.2.2
  obtain ⟨aG, bG, hG⟩ := P.G_linearGrowth p
  set E := ∫ D, ∑ k, |D k| ∂(P.μ p) with hE
  set α := P.α (p + 1) with hα
  have hαpos : 0 < α := P.α_pos (p + 1)
  refine ⟨aG + α * (|c| + |a| + b * ((L : ℝ) + 3) * E), |bG| + 2 * α * b, by positivity, ?_⟩
  intro y o
  unfold aux_so_W
  have hint : ∫ D, F (nextX y o D) (nextO o D) ∂(P.μ p) ≤
      (|c| + |a| + b * (|y| + 2 * ‖o‖)) + b * ((L : ℝ) + 3) * E := by
    calc _ ≤ ∫ D, ((|c| + |a| + b * (|y| + 2 * ‖o‖)) + b * ((L : ℝ) + 3) * ∑ k, |D k|)
          ∂(P.μ p) := integral_mono (aux_so_integrable P p hF y o)
            ((integrable_const _).add ((aux_so_sumD_int P p).const_mul _))
            (fun D => (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans
              (aux_so_pt_bound hb hc hab y o D)))
      _ = _ := by
          rw [integral_add (integrable_const _) ((aux_so_sumD_int P p).const_mul _),
            integral_const_mul, aux_so_int_const]
  have hGy : P.G p y ≤ aG + |bG| * |y| := by
    have := hG y
    have := le_abs_self (P.G p y)
    have := mul_le_mul_of_nonneg_right (le_abs_self bG) (abs_nonneg y)
    linarith
  have h1 := mul_le_mul_of_nonneg_left hint hαpos.le
  have h2 : 0 ≤ α * b * |y| := by positivity
  have h3 : 0 ≤ ‖o‖ := norm_nonneg _
  have h4 : 0 ≤ |bG| * ‖o‖ := by positivity
  nlinarith

lemma aux_so_W_meas (P : Model L M) (p : ℕ) {F : ℝ → (Fin M → ℝ) → ℝ} {k : ℝ}
    (hF : aux_so_Good F k) :
    Measurable (fun q : ℝ × (Fin M → ℝ) => aux_so_W P p F q.1 q.2) := by
  have := P.μ_prob p
  unfold aux_so_W
  refine ((aux_so_G_cont P p).measurable.comp measurable_fst).add (measurable_const.mul ?_)
  have hsm : StronglyMeasurable (Function.uncurry fun (q : ℝ × (Fin M → ℝ))
      (D : Fin (L + M + 2) → ℝ) => F (nextX q.1 q.2 D) (nextO q.2 D)) :=
    (hF.1.comp (aux_so_trans_cont (L := L) (M := M)).measurable).stronglyMeasurable
  exact (hsm.integral_prod_right (ν := P.μ p)).measurable

lemma aux_so_setupIndicator_meas : Measurable setupIndicator := by
  unfold setupIndicator
  exact Measurable.ite measurableSet_Ioi measurable_const measurable_const

lemma aux_so_step (P : Model L M) (p : ℕ) {F : ℝ → (Fin M → ℝ) → ℝ} {k : ℝ}
    (hF : aux_so_Good F k) (hk : P.α (p + 1) * k ≤ P.K p) :
    aux_so_Good (fun x o => orderCost (P.K p) (fun y => aux_so_W P p F y o) x) (P.K p) := by
  obtain ⟨c, hc⟩ := hF.2.2.2.1
  have hsc := fun o => aux_so_scarf (P.K_pos p) (aux_so_W_cont P p hF o)
    (aux_so_W_KC P p hF hk o) (aux_so_W_coer P p hF o)
  choose S s hS hs hsS hfs hJ hQ hle hKC using hsc
  obtain ⟨y₀, hy₀⟩ := (aux_so_G_cont P p).exists_forall_le (P.G_coercive p)
  obtain ⟨a', b', hb', hab'⟩ := aux_so_W_upper P p hF
  refine ⟨?_, ?_, hKC, ?_, ⟨a', b', hb', fun x o => (hle o x).trans (hab' x o)⟩⟩
  · have hfun : (fun q : ℝ × (Fin M → ℝ) =>
        orderCost (P.K p) (fun y => aux_so_W P p F y q.2) q.1) =
        fun q => ⨅ r : ℚ, (P.K p * setupIndicator (max (r : ℝ) q.1 - q.1) +
          aux_so_W P p F (max (r : ℝ) q.1) q.2) := funext fun q => hQ q.2 q.1
    rw [hfun]
    refine Measurable.iInf fun r => ?_
    refine (measurable_const.mul (aux_so_setupIndicator_meas.comp
      ((measurable_const.max measurable_fst).sub measurable_fst))).add ?_
    exact (aux_so_W_meas P p hF).comp ((measurable_const.max measurable_fst).prodMk measurable_snd)
  · intro o
    have : (fun x => orderCost (P.K p) (fun y => aux_so_W P p F y o) x) =
        fun x => aux_so_W P p F (max x (s o)) o := funext (hJ o)
    rw [this]
    exact (aux_so_W_cont P p hF o).comp (continuous_id.max continuous_const)
  · refine ⟨P.G p y₀ + P.α (p + 1) * c, fun x o => ?_⟩
    show _ ≤ orderCost (P.K p) (fun y => aux_so_W P p F y o) x
    rw [hJ o x]
    have := aux_so_W_lower P p hF hc (max x (s o)) o
    have := hy₀ (max x (s o))
    linarith

noncomputable def aux_so_kk (P : Model L M) : ℕ → ℝ
  | 0 => 0
  | n + 1 => P.K (P.T - n)

lemma aux_so_Jgo_succ (P : Model L M) (n : ℕ) :
    P.Jgo (n + 1) = fun x o =>
      orderCost (P.K (P.T - n)) (fun y => aux_so_W P (P.T - n) (P.Jgo n) y o) x := rfl

lemma aux_so_good_all (P : Model L M) :
    ∀ n, n ≤ P.T → aux_so_Good (P.Jgo n) (aux_so_kk P n) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨measurable_const, fun _ => continuous_const, fun _ => ?_, ⟨0, fun _ _ => le_rfl⟩,
      ⟨0, 0, le_rfl, fun _ _ => by simp [Model.Jgo]⟩⟩
    intro x₁ x₂ _ θ _ _
    simp [Model.Jgo, aux_so_kk]
  | succ n ih =>
    intro hn
    have hF := ih (by omega)
    rw [aux_so_Jgo_succ]
    apply aux_so_step P (P.T - n) hF
    cases n with
    | zero => simp only [aux_so_kk, mul_zero]; exact (P.K_pos _).le
    | succ m =>
      simp only [aux_so_kk]
      have := P.discount_setup (P.T - (m + 1))
      rw [show P.T - (m + 1) + 1 = P.T - m by omega] at this
      rw [show P.T - (m + 1) + 1 = P.T - m by omega]
      exact this

end GallegoOzerADI.PositiveSetup

open GallegoOzerADI.PositiveSetup

theorem checked_sS_policy_optimal {L M : ℕ} [NeZero M] (P : Model L M) (t : ℕ) (ht₁ : 1 ≤ t)
    (htT : t ≤ P.T) (o : Fin M → ℝ) :
    ∃ S s : ℝ, IsLeast {y | ∀ x, P.V t y o ≤ P.V t x o} S ∧
      IsGreatest {x | P.H t x o ≤ 0} s ∧
      ∀ x, (x ≤ s → x < S ∧ P.J t x o = P.K t + P.V t S o) ∧
        (s < x → P.J t x o = P.V t x o) := by
  have hF := aux_so_good_all P (P.T - t) (by omega)
  have hJt : P.J (t + 1) = P.Jgo (P.T - t) := by
    unfold Model.J
    rw [show P.T + 1 - (t + 1) = P.T - t by omega]
  have hV : ∀ y o, P.V t y o = aux_so_W P t (P.Jgo (P.T - t)) y o := by
    intro y o
    simp only [Model.V, aux_so_W, hJt]
  have hk : P.α (t + 1) * aux_so_kk P (P.T - t) ≤ P.K t := by
    rcases h : P.T - t with _ | m
    · simp only [aux_so_kk, mul_zero]; exact (P.K_pos t).le
    · simp only [aux_so_kk]
      rw [show P.T - m = t + 1 by omega]
      exact P.discount_setup t
  obtain ⟨S, s, hS, hs, hsS, hfs, hJ, -, -, -⟩ := aux_so_scarf (P.K_pos t)
    (aux_so_W_cont P t hF o) (aux_so_W_KC P t hF hk o) (aux_so_W_coer P t hF o)
  have hVf : (fun y => P.V t y o) = fun y => aux_so_W P t (P.Jgo (P.T - t)) y o :=
    funext fun y => hV y o
  have hJeq : ∀ x, P.J t x o = aux_so_W P t (P.Jgo (P.T - t)) (max x s) o := by
    intro x
    rw [P.J_eq t ht₁ htT x o, hVf]
    exact hJ x
  refine ⟨S, s, ?_, ?_, fun x => ⟨fun hx => ⟨lt_of_le_of_lt hx hsS, ?_⟩, fun hx => ?_⟩⟩
  · simp only [hV]; exact hS
  · have : {x | P.H t x o ≤ 0} = {x | reorderGap (P.K t)
        (fun y => aux_so_W P t (P.Jgo (P.T - t)) y o) x ≤ 0} := by
      ext x
      simp only [Set.mem_ofPred_eq, Model.H, hVf]
    rw [this]; exact hs
  · rw [hJeq, max_eq_right hx, hV]; exact hfs
  · rw [hJeq, max_eq_left hx.le, hV]
end


end

/- Complete checked body: ContinuationEquality -/
section

set_option autoImplicit false
open MeasureTheory

namespace GallegoOzerADI.PositiveSetupProof
open GallegoOzerADI.PositiveSetup

variable {L M : ℕ} [NeZero M]

theorem nextX_le_myopic_reorder (G : ℝ → ℝ) (K α : ℝ)
    (o : Fin M → ℝ) (D : Fin (L+M+2) → ℝ) (hD : ∀ k,0 ≤ D k)
    (hobs : myopicUpperLevel G K α - myopicReorderPoint G K ≤ o 0)
    (y : ℝ) (hy : y ≤ myopicUpperLevel G K α) :
    nextX y o D ≤ myopicReorderPoint G K := by
  have hsum : 0 ≤ ∑ k : Fin (L+2), D (Fin.castLE (by omega) k) :=
    Finset.sum_nonneg (fun k _ => hD _)
  have hzero : obsComp o 0 = o 0 := by simp [obsComp,NeZero.pos M]
  unfold nextX
  rw [hzero]
  linarith

theorem continuation_eq_ae (P : Model L M) (G : ℝ → ℝ) (K α : ℝ)
    (ν : Measure (Fin (L+M+2) → ℝ)) (hG : ∀ t,P.G t=G) (hK : ∀ t,P.K t=K)
    (hα : ∀ t,P.α t=α) (hμ : ∀ t,P.μ t=ν)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) (o : Fin M → ℝ)
    (ho : ∀ j,0 ≤ o j)
    (hobs : myopicUpperLevel G K α - myopicReorderPoint G K ≤ o 0)
    (a b : ℝ) (ha : a ≤ myopicUpperLevel G K α) (hb : b ≤ myopicUpperLevel G K α) :
    (fun D => P.J (t+1) (nextX a o D) (nextO o D)) =ᵐ[P.μ t]
      (fun D => P.J (t+1) (nextX b o D) (nextO o D)) := by
  by_cases ht : t=P.T
  · subst t
    exact Filter.Eventually.of_forall (fun D => by simp only [P.J_terminal])
  · have hn : t+1 ≤ P.T := by omega
    have htNext : 1 ≤ t+1 := ht1.trans (Nat.le_succ t)
    filter_upwards [P.μ_nonneg t] with D hD
    have hon := aux_myb_nextO_nonneg ho hD
    obtain ⟨S,s,hS,hs,hpolicy⟩ := checked_sS_policy_optimal P (t+1) htNext hn (nextO o D)
    have hbounds := checked_myopic_bounds P G K α ν hG hK hα hμ (t+1) htNext hn
      (nextO o D) hon S s hS hs
    have hxa : nextX a o D ≤ s :=
      (nextX_le_myopic_reorder G K α o D hD hobs a ha).trans hbounds.2.2
    have hxb : nextX b o D ≤ s :=
      (nextX_le_myopic_reorder G K α o D hD hobs b hb).trans hbounds.2.2
    exact ((hpolicy (nextX a o D)).1 hxa).2.trans (((hpolicy (nextX b o D)).1 hxb).2.symm)

end GallegoOzerADI.PositiveSetupProof

end

/- Complete checked body: MyopicLeastness -/
section

set_option autoImplicit false
open MeasureTheory Filter

namespace GallegoOzerADI.PositiveSetupProof
open GallegoOzerADI.PositiveSetup

theorem myopic_order_up_to_isLeast {L M : ℕ} [NeZero M] (P : Model L M)
    (G : ℝ → ℝ) (K α : ℝ) (ν : Measure (Fin (L+M+2) → ℝ))
    (hG : ∀ t,P.G t=G) (hK : ∀ t,P.K t=K) (hα : ∀ t,P.α t=α) (hμ : ∀ t,P.μ t=ν)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) (o : Fin M → ℝ) (ho : ∀ j,0 ≤ o j)
    (hobs : myopicUpperLevel G K α - myopicReorderPoint G K ≤ o 0) :
    IsLeast {y | ∀ x,P.V t y o ≤ P.V t x o} (myopicOrderUpTo G) := by
  obtain ⟨S,s,hS,hs,_⟩ := checked_sS_policy_optimal P t ht1 htT o
  have hb := checked_myopic_bounds P G K α ν hG hK hα hμ t ht1 htT o ho S s hS hs
  have hconv : ConvexOn ℝ Set.univ G := by
    rw [← hG 0]
    exact P.G_convex 0
  have hcoer : Tendsto G (cocompact ℝ) atTop := by
    rw [← hG 0]
    exact P.G_coercive 0
  have hmin := (aux_myb_Gprops hconv hcoer).1
  have he := continuation_eq_ae P G K α ν hG hK hα hμ t ht1 htT o ho hobs
    (myopicOrderUpTo G) S (hb.1.trans hb.2.1) hb.2.1
  have hint := integral_congr_ae he
  have hcost : P.V t (myopicOrderUpTo G) o ≤ P.V t S o := by
    unfold Model.V
    simp only [hG t,hint]
    exact add_le_add (hmin S) le_rfl
  have hglobal : ∀ x,P.V t (myopicOrderUpTo G) o ≤ P.V t x o :=
    fun x => hcost.trans (hS.1 x)
  have heq : S=myopicOrderUpTo G := le_antisymm (hS.2 hglobal) hb.1
  simpa only [heq] using hS

end GallegoOzerADI.PositiveSetupProof

end

/- Complete checked body: ReplenishmentRoot -/
section

open MeasureTheory

namespace GallegoOzerADI.PositiveSetup

theorem myopic_order_up_to_optimal {L M : ℕ} [NeZero M] (P : Model L M) (G : ℝ → ℝ)
    (K α : ℝ) (ν : Measure (Fin (L + M + 2) → ℝ)) (hG : ∀ t, P.G t = G)
    (hK : ∀ t, P.K t = K) (hα : ∀ t, P.α t = α) (hμ : ∀ t, P.μ t = ν) (t : ℕ) (ht₁ : 1 ≤ t)
    (htT : t ≤ P.T) (o : Fin M → ℝ) (ho : ∀ j, 0 ≤ o j)
    (hobs : myopicUpperLevel G K α - myopicReorderPoint G K ≤ o 0) :
    IsLeast {y | ∀ x, P.V t y o ≤ P.V t x o} (myopicOrderUpTo G) := by
  exact GallegoOzerADI.PositiveSetupProof.myopic_order_up_to_isLeast
    P G K α ν hG hK hα hμ t ht₁ htT o ho hobs

end GallegoOzerADI.PositiveSetup

end

open GallegoOzerADI.PositiveSetup
open MeasureTheory

theorem solution {L M : ℕ} [NeZero M] (P : Model L M) (G : ℝ → ℝ)
    (K α : ℝ) (ν : Measure (Fin (L + M + 2) → ℝ)) (hG : ∀ t, P.G t = G)
    (hK : ∀ t, P.K t = K) (hα : ∀ t, P.α t = α) (hμ : ∀ t, P.μ t = ν) (t : ℕ) (ht₁ : 1 ≤ t)
    (htT : t ≤ P.T) (o : Fin M → ℝ) (ho : ∀ j, 0 ≤ o j)
    (hobs : myopicUpperLevel G K α - myopicReorderPoint G K ≤ o 0) :
    IsLeast {y | ∀ x, P.V t y o ≤ P.V t x o} (myopicOrderUpTo G) := by
  exact GallegoOzerADI.PositiveSetup.myopic_order_up_to_optimal P G K α ν hG hK hα hμ t ht₁ htT o ho hobs

#print axioms GallegoOzerADI.PositiveSetup.myopic_order_up_to_optimal
#print axioms solution
