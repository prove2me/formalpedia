-- Prove2me | solution 1 for GallegoOzerADI.PositiveSetup.myopic_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:33:31.000906+00:00
-- url     : https://prove2.me/submissions/8ffbdff3-0c9d-4c8f-afe9-090d7934d45d

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model
import Definitions.Def_GallegoOzerADI_PositiveSetup_MyopicLevels

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

theorem solution {L M : ℕ} [NeZero M] (P : Model L M) (G : ℝ → ℝ) (K α : ℝ)
    (ν : Measure (Fin (L + M + 2) → ℝ)) (hG : ∀ t, P.G t = G) (hK : ∀ t, P.K t = K)
    (hα : ∀ t, P.α t = α) (hμ : ∀ t, P.μ t = ν) (t : ℕ) (ht₁ : 1 ≤ t) (htT : t ≤ P.T)
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
