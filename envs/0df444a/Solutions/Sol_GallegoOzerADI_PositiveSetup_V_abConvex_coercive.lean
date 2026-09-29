-- Prove2me | solution 1 for GallegoOzerADI.PositiveSetup.V_abConvex_coercive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:28:41.505147+00:00
-- url     : https://prove2.me/submissions/00966279-bd3b-4793-a311-553ddaae642c

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model

open Filter

namespace GallegoOzerADI.PositiveSetup

open MeasureTheory Topology

/-! ### The set-up indicator and the order-cost operator -/

lemma aux_goV_ind_nonneg (z : ℝ) : 0 ≤ setupIndicator z := by
  unfold setupIndicator; split_ifs <;> norm_num

lemma aux_goV_ind_le (z : ℝ) : setupIndicator z ≤ 1 := by
  unfold setupIndicator; split_ifs <;> norm_num

lemma aux_goV_ind_zero : setupIndicator 0 = 0 := by simp [setupIndicator]

lemma aux_goV_ind_pos {z : ℝ} (hz : 0 < z) : setupIndicator z = 1 := by
  simp [setupIndicator, hz]

lemma aux_goV_oc_bdd {K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) (x : ℝ) :
    BddBelow (Set.range fun y : {y : ℝ // x ≤ y} => K * setupIndicator ((y : ℝ) - x) + f y) := by
  refine ⟨c, ?_⟩
  rintro _ ⟨y, rfl⟩
  have := hc y
  have := mul_nonneg hK (aux_goV_ind_nonneg ((y : ℝ) - x))
  linarith

lemma aux_goV_oc_le {K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) {x y : ℝ}
    (hxy : x ≤ y) : orderCost K f x ≤ K * setupIndicator (y - x) + f y :=
  ciInf_le (aux_goV_oc_bdd hK hc x) ⟨y, hxy⟩

lemma aux_goV_oc_le_self {K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y)
    (x : ℝ) : orderCost K f x ≤ f x := by
  have := aux_goV_oc_le hK hc (le_refl x)
  rwa [sub_self, aux_goV_ind_zero, mul_zero, zero_add] at this

lemma aux_goV_oc_le_K {K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) {x y : ℝ}
    (hxy : x ≤ y) : orderCost K f x ≤ K + f y := by
  have := aux_goV_oc_le hK hc hxy
  have := mul_le_of_le_one_right hK (aux_goV_ind_le (y - x))
  linarith

lemma aux_goV_oc_ge {K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) (x : ℝ) :
    c ≤ orderCost K f x := by
  unfold orderCost
  have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_refl x⟩⟩
  refine le_ciInf fun y => ?_
  have := hc y
  have := mul_nonneg hK (aux_goV_ind_nonneg ((y : ℝ) - x))
  linarith

lemma aux_goV_oc_approx {K : ℝ} {f : ℝ → ℝ} (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ y, x ≤ y ∧ K * setupIndicator (y - x) + f y < orderCost K f x + ε := by
  have h : orderCost K f x < orderCost K f x + ε := by linarith
  have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_refl x⟩⟩
  obtain ⟨y, hy⟩ := exists_lt_of_ciInf_lt h
  exact ⟨y, y.2, hy⟩

/-! ### Scarf's lemma: the order-cost operator preserves `K`-convexity -/

lemma aux_goV_scarf_core {K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y)
    (hf : ABConvex 0 K f) {x₁ x₂ θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (h12 : x₁ < x₂)
    {y₁ y₂ : ℝ} (hy₁ : x₁ ≤ y₁) (hy₂ : x₂ ≤ y₂) :
    orderCost K f (θ * x₁ + (1 - θ) * x₂) ≤
      θ * (K * setupIndicator (y₁ - x₁) + f y₁) +
        (1 - θ) * (K + (K * setupIndicator (y₂ - x₂) + f y₂)) := by
  have hx1 : x₁ < θ * x₁ + (1 - θ) * x₂ := by nlinarith [mul_pos (sub_pos.2 hθ1) (sub_pos.2 h12)]
  have hx2 : θ * x₁ + (1 - θ) * x₂ < x₂ := by nlinarith [mul_pos hθ0 (sub_pos.2 h12)]
  generalize hxdef : θ * x₁ + (1 - θ) * x₂ = x at hx1 hx2 ⊢
  generalize hA : K * setupIndicator (y₁ - x₁) + f y₁ = A
  generalize hB : K * setupIndicator (y₂ - x₂) + f y₂ = B
  have hB0 : f y₂ ≤ B := by
    have := mul_nonneg hK (aux_goV_ind_nonneg (y₂ - x₂)); linarith
  have hA0 : f y₁ ≤ A := by
    have := mul_nonneg hK (aux_goV_ind_nonneg (y₁ - x₁)); linarith
  have hgB : orderCost K f x ≤ K + B := by
    have := aux_goV_oc_le_K hK hc (show x ≤ y₂ by linarith); linarith
  by_cases hAB : K + B ≤ A
  · nlinarith [mul_le_mul_of_nonneg_left hAB hθ0.le]
  push Not at hAB
  by_cases hy1x : x ≤ y₁
  · have h1 : orderCost K f x ≤ A := by
      have := aux_goV_oc_le_K hK hc hy1x
      rw [← hA, aux_goV_ind_pos (by linarith : 0 < y₁ - x₁)]
      linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hθ0.le,
      mul_le_mul_of_nonneg_left hgB (sub_nonneg.2 hθ1.le)]
  push Not at hy1x
  have hd : 0 < y₂ - y₁ := by linarith
  have hν0 : 0 ≤ (y₂ - x) / (y₂ - y₁) := div_nonneg (by linarith) hd.le
  have hν1 : (y₂ - x) / (y₂ - y₁) ≤ 1 := (div_le_one hd).2 (by linarith)
  have hνx : (y₂ - x) / (y₂ - y₁) * y₁ + (1 - (y₂ - x) / (y₂ - y₁)) * y₂ = x := by
    field_simp; ring
  have hθν : θ ≤ (y₂ - x) / (y₂ - y₁) := by
    rw [le_div_iff₀ hd, ← hxdef]
    nlinarith [mul_nonneg hθ0.le (sub_nonneg.2 hy₁),
      mul_nonneg (sub_nonneg.2 hθ1.le) (sub_nonneg.2 hy₂)]
  generalize hν : (y₂ - x) / (y₂ - y₁) = ν at hν0 hν1 hνx hθν
  have hfx := hf y₁ y₂ (by linarith) ν hν0 hν1
  rw [hνx] at hfx
  have hgx := aux_goV_oc_le_self hK hc x
  have h1 : ν * (0 + f y₁) + (1 - ν) * (K + f y₂) ≤ ν * A + (1 - ν) * (K + B) := by
    nlinarith [mul_le_mul_of_nonneg_left hA0 hν0,
      mul_le_mul_of_nonneg_left hB0 (sub_nonneg.2 hν1)]
  have h2 : ν * A + (1 - ν) * (K + B) ≤ θ * A + (1 - θ) * (K + B) := by
    nlinarith [mul_le_mul_of_nonneg_right hθν (sub_nonneg.2 hAB.le)]
  linarith

lemma aux_goV_scarf {K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y)
    (hf : ABConvex 0 K f) : ABConvex 0 K (orderCost K f) := by
  intro x₁ x₂ h12 θ hθ0 hθ1
  rcases eq_or_lt_of_le hθ0 with h | hθ0'
  · rw [← h, show (0:ℝ) * x₁ + (1 - 0) * x₂ = x₂ by ring]
    linarith
  rcases eq_or_lt_of_le hθ1 with h | hθ1'
  · rw [h, show (1:ℝ) * x₁ + (1 - 1) * x₂ = x₁ by ring]
    linarith
  rcases eq_or_lt_of_le h12 with h | h12'
  · rw [show θ * x₁ + (1 - θ) * x₂ = x₁ by rw [← h]; ring, ← h]
    nlinarith [mul_nonneg (sub_nonneg.2 hθ1) hK]
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨y₁, hy₁, hA⟩ := aux_goV_oc_approx (K := K) (f := f) x₁ hε
  obtain ⟨y₂, hy₂, hB⟩ := aux_goV_oc_approx (K := K) (f := f) x₂ hε
  have := aux_goV_scarf_core hK hc hf hθ0' hθ1' h12' hy₁ hy₂
  nlinarith [mul_lt_mul_of_pos_left hA hθ0', mul_lt_mul_of_pos_left hB (sub_pos.2 hθ1')]

/-! ### The running infimum -/

noncomputable def aux_goV_m (f : ℝ → ℝ) (x : ℝ) : ℝ := ⨅ y : {y : ℝ // x ≤ y}, f y

lemma aux_goV_m_bdd {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) (x : ℝ) :
    BddBelow (Set.range fun y : {y : ℝ // x ≤ y} => f y) :=
  ⟨c, by rintro _ ⟨y, rfl⟩; exact hc y⟩

lemma aux_goV_m_le {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) {x y : ℝ} (h : x ≤ y) :
    aux_goV_m f x ≤ f y := ciInf_le (aux_goV_m_bdd hc x) ⟨y, h⟩

lemma aux_goV_le_m {f : ℝ → ℝ} {x r : ℝ} (h : ∀ y, x ≤ y → r ≤ f y) : r ≤ aux_goV_m f x := by
  have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_refl x⟩⟩
  exact le_ciInf fun y => h y y.2

lemma aux_goV_oc_eq {K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) (x : ℝ) :
    orderCost K f x = min (f x) (K + aux_goV_m f x) := by
  apply le_antisymm
  · refine le_min (aux_goV_oc_le_self hK hc x) ?_
    have : orderCost K f x - K ≤ aux_goV_m f x := aux_goV_le_m fun y hy => by
      have := aux_goV_oc_le_K hK hc hy; linarith
    linarith
  · unfold orderCost
    have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_refl x⟩⟩
    refine le_ciInf fun y => ?_
    rcases eq_or_lt_of_le y.2 with h | h
    · rw [← h, sub_self, aux_goV_ind_zero, mul_zero, zero_add]
      exact min_le_left _ _
    · rw [aux_goV_ind_pos (by linarith)]
      have := aux_goV_m_le hc y.2
      exact le_trans (min_le_right _ _) (by linarith)

lemma aux_goV_m_mono {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) {a b : ℝ} (hab : a ≤ b) :
    aux_goV_m f a ≤ aux_goV_m f b :=
  aux_goV_le_m fun _ hy => aux_goV_m_le hc (hab.trans hy)

lemma aux_goV_m_cont {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) (hf : Continuous f) :
    Continuous (aux_goV_m f) := by
  rw [Metric.continuous_iff]
  intro x₀ ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuous_iff.1 hf x₀ (ε / 3) (by linarith)
  have key : ∀ a, |a - x₀| < δ → |f a - f x₀| < ε / 3 := fun a ha => by
    have := hδf a (by rwa [Real.dist_eq]); rwa [Real.dist_eq] at this
  refine ⟨δ, hδ, fun x hx => ?_⟩
  rw [Real.dist_eq] at hx ⊢
  have hx' := abs_lt.1 hx
  rcases le_total x₀ x with h | h
  · have h1 := aux_goV_m_mono hc h
    have hfx := abs_lt.1 (key x hx)
    have hmx := aux_goV_m_le hc (le_refl x)
    have h2 : aux_goV_m f x - 2 * ε / 3 ≤ aux_goV_m f x₀ := aux_goV_le_m fun y hy => by
      rcases le_total x y with h' | h'
      · have := aux_goV_m_le hc h'; linarith
      · have := abs_lt.1 (key y (abs_lt.2 ⟨by linarith, by linarith⟩))
        linarith [this.1, this.2, hfx.1, hfx.2]
    rw [abs_lt]; constructor <;> linarith
  · have h1 := aux_goV_m_mono hc h
    have hmx0 := aux_goV_m_le hc (le_refl x₀)
    have h2 : aux_goV_m f x₀ - ε / 3 ≤ aux_goV_m f x := aux_goV_le_m fun y hy => by
      rcases le_total x₀ y with h' | h'
      · have := aux_goV_m_le hc h'; linarith
      · have := abs_lt.1 (key y (abs_lt.2 ⟨by linarith, by linarith⟩))
        linarith [this.1, this.2]
    rw [abs_lt]; constructor <;> linarith

lemma aux_goV_m_rat {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) (hf : Continuous f) (x : ℝ) :
    aux_goV_m f x = ⨅ q : ℚ, f (x + |(q : ℝ)|) := by
  have hbdd : BddBelow (Set.range fun q : ℚ => f (x + |(q : ℝ)|)) :=
    ⟨c, by rintro _ ⟨q, rfl⟩; exact hc _⟩
  apply le_antisymm
  · exact le_ciInf fun q => aux_goV_m_le hc (by linarith [abs_nonneg (q : ℝ)])
  · refine aux_goV_le_m fun y hy => ?_
    have hp : ∀ u : ℝ, (⨅ q : ℚ, f (x + |(q : ℝ)|)) ≤ f (x + |u|) := by
      intro u
      refine Rat.denseRange_cast.induction_on (p := fun u : ℝ => (⨅ q : ℚ, f (x + |(q : ℝ)|)) ≤
        f (x + |u|)) u ?_ (fun q => ciInf_le hbdd q)
      exact isClosed_le continuous_const (hf.comp (continuous_const.add continuous_abs))
    have e : x + |y - x| = y := by rw [abs_of_nonneg (by linarith)]; ring
    have := hp (y - x)
    rwa [e] at this

/-! ### Norm bounds for the transitions -/

def aux_goV_n1 {n : ℕ} (o : Fin n → ℝ) : ℝ := ∑ j, |o j|

lemma aux_goV_n1_nonneg {n : ℕ} (o : Fin n → ℝ) : 0 ≤ aux_goV_n1 o :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma aux_goV_le_n1 {n : ℕ} (o : Fin n → ℝ) (j : Fin n) : |o j| ≤ aux_goV_n1 o :=
  Finset.single_le_sum (f := fun j => |o j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

lemma aux_goV_obs_le {M : ℕ} (o : Fin M → ℝ) (j : ℕ) : |obsComp o j| ≤ aux_goV_n1 o := by
  unfold obsComp; split_ifs with h
  · exact aux_goV_le_n1 o _
  · simpa using aux_goV_n1_nonneg o

lemma aux_goV_nextX_le {L M : ℕ} (y : ℝ) (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ) :
    |nextX y o D| ≤ |y| + (L + 2) * aux_goV_n1 D + aux_goV_n1 o := by
  unfold nextX
  have h1 : |∑ k : Fin (L + 2), D (Fin.castLE (by omega) k)| ≤ (L + 2) * aux_goV_n1 D := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => aux_goV_le_n1 D _).trans ?_
    simp
  have h2 := aux_goV_obs_le o 0
  have h3 := abs_sub (y - ∑ k : Fin (L + 2), D (Fin.castLE (by omega) k)) (obsComp o 0)
  have h4 := abs_sub y (∑ k : Fin (L + 2), D (Fin.castLE (by omega) k))
  linarith

lemma aux_goV_nextO_le {L M : ℕ} (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ) :
    aux_goV_n1 (nextO o D) ≤ M * (aux_goV_n1 o + aux_goV_n1 D) := by
  have : ∀ j : Fin M, |nextO o D j| ≤ aux_goV_n1 o + aux_goV_n1 D := fun j => by
    unfold nextO
    exact (abs_add_le _ _).trans (add_le_add (aux_goV_obs_le o _) (aux_goV_le_n1 D _))
  calc aux_goV_n1 (nextO o D) = ∑ j, |nextO o D j| := rfl
    _ ≤ ∑ _j : Fin M, (aux_goV_n1 o + aux_goV_n1 D) := Finset.sum_le_sum fun j _ => this j
    _ = _ := by simp [mul_add]

lemma aux_goV_trans_le {L M : ℕ} (y : ℝ) (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ) :
    |nextX y o D| + aux_goV_n1 (nextO o D) ≤
      |y| + (L + M + 2) * aux_goV_n1 D + (M + 1) * aux_goV_n1 o := by
  have := aux_goV_nextX_le y o D
  have := aux_goV_nextO_le o D
  linarith

/-! ### The backward induction -/

variable {L M : ℕ}

def aux_goV_Inv (K : ℝ) (f : ℝ → (Fin M → ℝ) → ℝ) : Prop :=
  (∀ o, Continuous (fun x => f x o)) ∧
  Measurable (fun p : ℝ × (Fin M → ℝ) => f p.1 p.2) ∧
  (∃ c, ∀ x o, c ≤ f x o) ∧
  (∃ C B, 0 ≤ B ∧ ∀ x o, f x o ≤ C + B * (|x| + aux_goV_n1 o)) ∧
  (∀ o, ABConvex 0 K (fun x => f x o))

lemma aux_goV_VJ {K : ℝ} (hK : 0 < K) {V : ℝ → (Fin M → ℝ) → ℝ} (h : aux_goV_Inv K V) :
    aux_goV_Inv K (fun x o => orderCost K (fun y => V y o) x) := by
  obtain ⟨hcont, hmeas, ⟨c, hc⟩, ⟨C, B, hB, hCB⟩, hconv⟩ := h
  have hK0 := hK.le
  refine ⟨fun o => ?_, ?_, ⟨c, fun x o => aux_goV_oc_ge hK0 (hc · o) x⟩,
    ⟨C, B, hB, fun x o => (aux_goV_oc_le_self hK0 (hc · o) x).trans (hCB x o)⟩,
    fun o => aux_goV_scarf hK0 (hc · o) (hconv o)⟩
  · have : (fun x => orderCost K (fun y => V y o) x) =
        fun x => min (V x o) (K + aux_goV_m (fun y => V y o) x) :=
      funext fun x => aux_goV_oc_eq hK0 (hc · o) x
    rw [this]
    exact (hcont o).min (continuous_const.add (aux_goV_m_cont (hc · o) (hcont o)))
  · have : (fun p : ℝ × (Fin M → ℝ) => orderCost K (fun y => V y p.2) p.1) =
        fun p => min (V p.1 p.2) (K + ⨅ q : ℚ, V (p.1 + |(q : ℝ)|) p.2) := funext fun p => by
      rw [aux_goV_oc_eq hK0 (hc · p.2) p.1, aux_goV_m_rat (hc · p.2) (hcont p.2) p.1]
    rw [this]
    refine hmeas.min (measurable_const.add (Measurable.iInf fun q => ?_))
    exact hmeas.comp ((measurable_fst.add_const _).prodMk measurable_snd)

lemma aux_goV_base (P : Model L M) : aux_goV_Inv (P.K (P.T + 1)) (P.J (P.T + 1)) := by
  have h0 : P.J (P.T + 1) = fun _ _ => 0 := funext fun x => funext fun o => P.J_terminal x o
  rw [h0]
  refine ⟨fun _ => continuous_const, measurable_const, ⟨0, fun _ _ => le_refl _⟩,
    ⟨0, 0, le_refl _, fun x o => by simp⟩, fun o => ?_⟩
  intro x₁ x₂ _ θ _ hθ1
  have := P.K_pos (P.T + 1)
  show (0:ℝ) ≤ θ * (0 + 0) + (1 - θ) * (P.K (P.T + 1) + 0)
  nlinarith [mul_nonneg (sub_nonneg.2 hθ1) this.le]

lemma aux_goV_obs_cont (j : ℕ) : Continuous (fun o : Fin M → ℝ => obsComp o j) := by
  unfold obsComp; split_ifs
  · exact continuous_apply _
  · exact continuous_const

lemma aux_goV_JV (P : Model L M) (s : ℕ) (h : aux_goV_Inv (P.K (s + 1)) (P.J (s + 1))) :
    aux_goV_Inv (P.K s) (P.V s) ∧ ∀ o, Tendsto (fun y => P.V s y o) (cocompact ℝ) atTop := by
  obtain ⟨hcont, hmeas, ⟨c, hc⟩, ⟨C, B, hB, hCB⟩, hconv⟩ := h
  have := P.μ_prob s
  have hαpos : 0 < P.α (s + 1) := P.α_pos (s + 1)
  have hGc : Continuous (P.G s) :=
    continuousOn_univ.1 ((P.G_convex s).continuousOn isOpen_univ)
  obtain ⟨y₀, hy₀⟩ := hGc.exists_forall_le (P.G_coercive s)
  obtain ⟨a, b, hab⟩ := P.G_linearGrowth s
  have hDint : Integrable (fun D : Fin (L + M + 2) → ℝ => aux_goV_n1 D) (P.μ s) := by
    unfold aux_goV_n1
    exact integrable_finsetSum _ fun k _ => (P.μ_integrable s k).abs
  have hXc : Continuous (fun q : (ℝ × (Fin M → ℝ)) × (Fin (L + M + 2) → ℝ) =>
      nextX q.1.1 q.1.2 q.2) := by
    unfold nextX
    refine (continuous_fst.fst.sub ?_).sub ((aux_goV_obs_cont 0).comp continuous_fst.snd)
    exact continuous_finsetSum _ fun k _ => (continuous_apply _).comp continuous_snd
  have hOc : Continuous (fun q : (ℝ × (Fin M → ℝ)) × (Fin (L + M + 2) → ℝ) =>
      nextO q.1.2 q.2) := by
    unfold nextO
    refine continuous_pi fun j => ?_
    exact ((aux_goV_obs_cont _).comp continuous_fst.snd).add
      ((continuous_apply _).comp continuous_snd)
  have hΦ : Measurable (fun q : (ℝ × (Fin M → ℝ)) × (Fin (L + M + 2) → ℝ) =>
      ((nextX q.1.1 q.1.2 q.2, nextO q.1.2 q.2) : ℝ × (Fin M → ℝ))) :=
    (hXc.prodMk hOc).measurable
  have hFmeas2 : Measurable (fun q : (ℝ × (Fin M → ℝ)) × (Fin (L + M + 2) → ℝ) =>
      P.J (s + 1) (nextX q.1.1 q.1.2 q.2) (nextO q.1.2 q.2)) := hmeas.comp hΦ
  have hFmeas : ∀ y o, Measurable (fun D => P.J (s + 1) (nextX y o D) (nextO o D)) :=
    fun y o => hFmeas2.comp (measurable_prodMk_left (x := ((y, o) : ℝ × (Fin M → ℝ))))
  have hFup : ∀ (y : ℝ) (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ), P.J (s + 1) (nextX y o D) (nextO o D) ≤
      C + B * (|y| + (L + M + 2) * aux_goV_n1 D + (M + 1) * aux_goV_n1 o) := fun y o D => by
    have h1 := hCB (nextX y o D) (nextO o D)
    have h2 := aux_goV_trans_le y o D
    have h3 := mul_le_mul_of_nonneg_left h2 hB
    linarith
  have hstuff : ∀ (y : ℝ) (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ),
      0 ≤ B * (|y| + (L + M + 2) * aux_goV_n1 D + (M + 1) * aux_goV_n1 o) := fun y o D =>
    mul_nonneg hB (add_nonneg (add_nonneg (abs_nonneg y)
      (mul_nonneg (by positivity) (aux_goV_n1_nonneg D)))
      (mul_nonneg (by positivity) (aux_goV_n1_nonneg o)))
  have hFbd : ∀ (y : ℝ) (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ), |P.J (s + 1) (nextX y o D) (nextO o D)| ≤
      |c| + |C| + B * (|y| + (L + M + 2) * aux_goV_n1 D + (M + 1) * aux_goV_n1 o) :=
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
      (|c| + |C| + B * (|y| + (M + 1) * aux_goV_n1 o))).add
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
      C + B * (|y| + (M + 1) * aux_goV_n1 o) +
        B * (L + M + 2) * ∫ D, aux_goV_n1 D ∂(P.μ s) := fun y o => by
    have hg : Integrable (fun D => (C + B * (|y| + (M + 1) * aux_goV_n1 o)) +
        B * (L + M + 2) * aux_goV_n1 D) (P.μ s) :=
      (integrable_const _).add (hDint.const_mul _)
    have hpt : ∀ D : Fin (L + M + 2) → ℝ, P.J (s + 1) (nextX y o D) (nextO o D) ≤
        (C + B * (|y| + (M + 1) * aux_goV_n1 o)) + B * (L + M + 2) * aux_goV_n1 D :=
      fun D => by have := hFup y o D; linarith
    have := integral_mono (hFint y o) hg hpt
    rw [integral_add (integrable_const _) (hDint.const_mul _), integral_const_mul] at this
    simpa using this
  have hVlow : ∀ y o, P.G s y₀ + P.α (s + 1) * c ≤ P.V s y o := fun y o => by
    have := mul_le_mul_of_nonneg_left (hIlow y o) hαpos.le
    have := hy₀ y
    show _ ≤ P.G s y + P.α (s + 1) * _
    linarith
  refine ⟨⟨fun o => ?_, ?_, ⟨_, hVlow⟩, ?_, fun o => ?_⟩, fun o => ?_⟩
  · -- continuity
    show Continuous fun y => P.G s y + P.α (s + 1) *
      ∫ D, P.J (s + 1) (nextX y o D) (nextO o D) ∂(P.μ s)
    refine hGc.add (continuous_const.mul ?_)
    rw [continuous_iff_continuousAt]
    intro y₁
    have hbint : Integrable (fun D => (|c| + |C| + B * ((|y₁| + 1) + (M + 1) * aux_goV_n1 o)) +
        B * (L + M + 2) * aux_goV_n1 D) (P.μ s) := (integrable_const _).add (hDint.const_mul _)
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
    refine ⟨a + P.α (s + 1) * (C + B * (L + M + 2) * ∫ D, aux_goV_n1 D ∂(P.μ s)),
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
    have h4 := aux_goV_n1_nonneg o
    have h5 : P.α (s + 1) * B * |y| ≤ P.α (s + 1) * B * (M + 1) * |y| := by
      have h0 : 0 ≤ P.α (s + 1) * B * |y| := mul_nonneg (mul_nonneg hαpos.le hB) (abs_nonneg y)
      have hM : (0:ℝ) ≤ M := Nat.cast_nonneg M
      nlinarith [mul_nonneg h0 hM]
    have h6 : 0 ≤ |b| * aux_goV_n1 o := mul_nonneg (abs_nonneg b) h4
    show P.G s y + P.α (s + 1) * _ ≤ _
    nlinarith
  · -- K-convexity
    intro x₁ x₂ h12 θ hθ0 hθ1
    have hK := P.discount_setup s
    have hGx := (P.G_convex s).2 (Set.mem_univ x₁) (Set.mem_univ x₂) hθ0 (sub_nonneg.2 hθ1)
      (by ring)
    simp only [smul_eq_mul] at hGx
    have hpt : ∀ D : Fin (L + M + 2) → ℝ, P.J (s + 1) (nextX (θ * x₁ + (1 - θ) * x₂) o D) (nextO o D) ≤
        θ * P.J (s + 1) (nextX x₁ o D) (nextO o D) +
          (1 - θ) * (P.K (s + 1) + P.J (s + 1) (nextX x₂ o D) (nextO o D)) := fun D => by
      have e : nextX (θ * x₁ + (1 - θ) * x₂) o D =
          θ * nextX x₁ o D + (1 - θ) * nextX x₂ o D := by unfold nextX; ring
      have := hconv (nextO o D) (nextX x₁ o D) (nextX x₂ o D)
        (by unfold nextX; linarith) θ hθ0 hθ1
      simp only [zero_add] at this
      rw [e]; exact this
    have i1 : Integrable (fun D => θ * P.J (s + 1) (nextX x₁ o D) (nextO o D)) (P.μ s) :=
      (hFint x₁ o).const_mul θ
    have i2 : Integrable (fun D => P.K (s + 1) + P.J (s + 1) (nextX x₂ o D) (nextO o D))
        (P.μ s) := (integrable_const _).add (hFint x₂ o)
    have i3 : Integrable (fun D => (1 - θ) *
        (P.K (s + 1) + P.J (s + 1) (nextX x₂ o D) (nextO o D))) (P.μ s) := i2.const_mul _
    have hg : Integrable (fun D => θ * P.J (s + 1) (nextX x₁ o D) (nextO o D) + (1 - θ) *
        (P.K (s + 1) + P.J (s + 1) (nextX x₂ o D) (nextO o D))) (P.μ s) := i1.add i3
    have hint := integral_mono (hFint _ o) hg hpt
    rw [integral_add i1 i3, integral_const_mul, integral_const_mul,
      integral_add (integrable_const _) (hFint x₂ o)] at hint
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hint
    show P.G s _ + P.α (s + 1) * _ ≤
      θ * (0 + (P.G s x₁ + P.α (s + 1) * _)) +
        (1 - θ) * (P.K s + (P.G s x₂ + P.α (s + 1) * _))
    have h1 := mul_le_mul_of_nonneg_left hint hαpos.le
    have h2 := mul_le_mul_of_nonneg_left hK (sub_nonneg.2 hθ1)
    nlinarith
  · -- coercivity
    have hlow : ∀ y, P.G s y + P.α (s + 1) * c ≤ P.V s y o := fun y => by
      have := mul_le_mul_of_nonneg_left (hIlow y o) hαpos.le
      show _ ≤ P.G s y + P.α (s + 1) * _
      linarith
    exact tendsto_atTop_mono hlow (tendsto_atTop_add_const_right _ _ (P.G_coercive s))

lemma aux_goV_all (P : Model L M) : ∀ n, n ≤ P.T →
    aux_goV_Inv (P.K (P.T + 1 - n)) (P.J (P.T + 1 - n)) := by
  intro n
  induction n with
  | zero => intro _; rw [Nat.sub_zero]; exact aux_goV_base P
  | succ n ih =>
    intro hn
    have h := ih (by omega)
    have e1 : P.T + 1 - n = (P.T - n) + 1 := by omega
    rw [e1] at h
    have hV := (aux_goV_JV P (P.T - n) h).1
    have e2 : P.T + 1 - (n + 1) = P.T - n := by omega
    rw [e2]
    have hJ : P.J (P.T - n) =
        fun x o => orderCost (P.K (P.T - n)) (fun y => P.V (P.T - n) y o) x :=
      funext fun x => funext fun o => P.J_eq (P.T - n) (by omega) (by omega) x o
    rw [hJ]
    exact aux_goV_VJ (P.K_pos _) hV

end GallegoOzerADI.PositiveSetup

open GallegoOzerADI.PositiveSetup

theorem solution {L M : ℕ} [NeZero M] (P : Model L M) (t : ℕ) (ht₁ : 1 ≤ t)
    (htT : t ≤ P.T) (o : Fin M → ℝ) :
    ABConvex 0 (P.K t) (fun y => P.V t y o) ∧
      Tendsto (fun y => P.V t y o) (cocompact ℝ) atTop := by
  have h := aux_goV_all P (P.T - t) (by omega)
  have e : P.T + 1 - (P.T - t) = t + 1 := by omega
  rw [e] at h
  have := aux_goV_JV P t h
  exact ⟨this.1.2.2.2.2 o, this.2 o⟩
