-- Prove2me | solution 1 for BellmanDP.Inventory.constant_stock_level_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:20:32.05101+00:00
-- url     : https://prove2.me/submissions/5479f948-e5e9-4686-ae47-490c49513004

import Mathlib
import Definitions.Def_BellmanDP_Inventory_Model

open MeasureTheory Filter Topology


namespace BellmanDP.Inventory

noncomputable def Mv (φ f : ℝ → ℝ) (y : ℝ) : ℝ := ∫ s in Set.Ioi 0, f (max (y - s) 0) * φ s

lemma mv_int {φ f : ℝ → ℝ} (hφ : DemandDensity φ) (hf : Measurable f) {y B : ℝ} (hy : 0 ≤ y)
    (hB : ∀ t ∈ Set.Icc (0:ℝ) y, |f t| ≤ B) :
    IntegrableOn (fun s => f (max (y - s) 0) * φ s) (Set.Ioi 0) := by
  refine Integrable.bdd_mul (c := B) hφ.integrable
    ((hf.comp ((measurable_const.sub measurable_id).max measurable_const)).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
  have hs' : (0:ℝ) < s := hs
  rw [Real.norm_eq_abs]
  exact hB _ ⟨le_max_right _ _, max_le (by linarith) hy⟩

lemma shift_ii {φ f : ℝ → ℝ} (hφ : DemandDensity φ) (hf : Measurable f) {y B : ℝ} (hy : 0 ≤ y)
    (hB : ∀ t ∈ Set.Icc (0:ℝ) y, |f t| ≤ B) :
    IntervalIntegrable (fun s => f (y - s) * φ s) volume 0 y := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hy]
  refine ((mv_int hφ hf hy hB).mono_set Set.Ioc_subset_Ioi_self).congr_fun (fun s hs => ?_)
    measurableSet_Ioc
  simp only
  rw [max_eq_left (by linarith [hs.2])]

lemma mv_repr {φ f : ℝ → ℝ} (hφ : DemandDensity φ) (hf : Measurable f) {y B : ℝ} (hy : 0 ≤ y)
    (hB : ∀ t ∈ Set.Icc (0:ℝ) y, |f t| ≤ B) :
    f 0 * (∫ s in Set.Ioi y, φ s) + (∫ s in (0:ℝ)..y, f (y - s) * φ s) = Mv φ f y := by
  have hint := mv_int hφ hf hy hB
  have h := setIntegral_union (Set.Ioc_disjoint_Ioi_same (a := (0:ℝ)) (b := y)) measurableSet_Ioi
    (hint.mono_set Set.Ioc_subset_Ioi_self) (hint.mono_set (Set.Ioi_subset_Ioi hy))
  rw [Set.Ioc_union_Ioi_eq_Ioi hy] at h
  rw [Mv, h, intervalIntegral.integral_of_le hy, add_comm]
  congr 1
  · refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    rw [max_eq_left (by linarith [hs.2])]
  · rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    have : y < s := hs
    rw [max_eq_right (by linarith)]

lemma mv_sub_le {φ f g : ℝ → ℝ} (hφ : DemandDensity φ) (hf : Measurable f) (hg : Measurable g)
    {y Bf Bg D : ℝ} (hy : 0 ≤ y)
    (hBf : ∀ t ∈ Set.Icc (0:ℝ) y, |f t| ≤ Bf) (hBg : ∀ t ∈ Set.Icc (0:ℝ) y, |g t| ≤ Bg)
    (hD : ∀ t, 0 ≤ t → |f t - g t| ≤ D) : |Mv φ f y - Mv φ g y| ≤ D := by
  rw [Mv, Mv, ← integral_sub (mv_int hφ hf hy hBf) (mv_int hφ hg hy hBg)]
  have h1 : ‖∫ s in Set.Ioi 0, (f (max (y - s) 0) * φ s - g (max (y - s) 0) * φ s)‖ ≤
      ∫ s in Set.Ioi 0, D * φ s := by
    refine norm_integral_le_of_norm_le (hφ.integrable.const_mul D) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
    rw [Real.norm_eq_abs, ← sub_mul, abs_mul, abs_of_pos (hφ.pos s hs)]
    exact mul_le_mul_of_nonneg_right (hD _ (le_max_right _ _)) (hφ.pos s hs).le
  rw [integral_const_mul, hφ.total, mul_one, Real.norm_eq_abs] at h1
  exact h1

lemma mv_mono {φ v : ℝ → ℝ} (hφ : DemandDensity φ) (hv : Measurable v)
    (hB : ∀ y, ∃ B, ∀ t ∈ Set.Icc (0:ℝ) y, |v t| ≤ B) (hmono : MonotoneOn v (Set.Ici 0))
    {y₁ y₂ : ℝ} (h1 : 0 ≤ y₁) (h12 : y₁ ≤ y₂) : Mv φ v y₁ ≤ Mv φ v y₂ := by
  obtain ⟨B1, hB1⟩ := hB y₁
  obtain ⟨B2, hB2⟩ := hB y₂
  refine setIntegral_mono_on (mv_int hφ hv h1 hB1) (mv_int hφ hv (h1.trans h12) hB2)
    measurableSet_Ioi (fun s hs => ?_)
  refine mul_le_mul_of_nonneg_right ?_ (hφ.pos s hs).le
  exact hmono (show max (y₁ - s) 0 ∈ Set.Ici 0 from Set.mem_Ici.2 (le_max_right _ _)) (show max (y₂ - s) 0 ∈ Set.Ici 0 from Set.mem_Ici.2 (le_max_right _ _)) (max_le_max (by linarith) le_rfl)

lemma mv_const {φ v : ℝ → ℝ} (hφ : DemandDensity φ) {xbar y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ xbar)
    (hc : ∀ t ∈ Set.Icc (0:ℝ) xbar, v t = v 0) : Mv φ v y = v 0 := by
  rw [Mv]
  rw [show v 0 = v 0 * ∫ s in Set.Ioi 0, φ s by rw [hφ.total, mul_one], ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have : (0:ℝ) < s := hs
  rw [hc _ ⟨le_max_right _ _, max_le (by linarith) (by linarith)⟩]

lemma invTq_decomp (k p q a : ℝ) {φ f : ℝ → ℝ} (hφ : DemandDensity φ) (hf : Measurable f)
    {y B x : ℝ} (hy : 0 ≤ y) (hB : ∀ t ∈ Set.Icc (0:ℝ) y, |f t| ≤ B) :
    invTq k p q a φ f x y = -k * x + psiQ k p q a φ y + a * Mv φ (fun t => f t + k * t) y := by
  have hv : Measurable (fun t => f t + k * t) := hf.add (measurable_const.mul measurable_id)
  have hBv : ∀ t ∈ Set.Icc (0:ℝ) y, |f t + k * t| ≤ B + |k| * y := by
    intro t ht
    calc |f t + k * t| ≤ |f t| + |k * t| := abs_add_le _ _
      _ ≤ B + |k| * y := by
        rw [abs_mul, abs_of_nonneg ht.1]
        exact add_le_add (hB t ht) (mul_le_mul_of_nonneg_left ht.2 (abs_nonneg _))
  rw [← mv_repr hφ hv hy hBv]
  have hid : ∀ t ∈ Set.Icc (0:ℝ) y, |t| ≤ y := fun t ht => by rw [abs_of_nonneg ht.1]; exact ht.2
  have i1 := shift_ii hφ hf hy hB
  have i2 : IntervalIntegrable (fun s => (y - s) * φ s) volume 0 y := shift_ii hφ measurable_id hy hid
  have : (∫ s in (0:ℝ)..y, (f (y - s) + k * (y - s)) * φ s) =
      (∫ s in (0:ℝ)..y, f (y - s) * φ s) + k * ∫ s in (0:ℝ)..y, (y - s) * φ s := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add i1 (i2.const_mul k)]
    congr 1; funext s; ring
  rw [this]
  unfold invTq psiQ
  simp only [mul_zero, add_zero]
  ring

lemma invTq_shift (k p q a : ℝ) (φ f : ℝ → ℝ) (x y : ℝ) :
    invTq k p q a φ f x y + k * x = invTq k p q a φ f 0 y := by
  unfold invTq; ring


noncomputable def PhiOp (k p q a xbar : ℝ) (φ f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => invTq k p q a φ f x (max x xbar)

def InvP (k : ℝ) (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ (∃ B, ∀ t, 0 ≤ t → |f t| ≤ B) ∧ MonotoneOn (fun t => f t + k * t) (Set.Ici 0)

lemma invTq_contr (k p q a : ℝ) {φ f g : ℝ → ℝ} (hφ : DemandDensity φ) (ha : 0 ≤ a)
    (hf : Measurable f) (hg : Measurable g) {Bf Bg D : ℝ}
    (hBf : ∀ t, 0 ≤ t → |f t| ≤ Bf) (hBg : ∀ t, 0 ≤ t → |g t| ≤ Bg)
    (hD : ∀ t, 0 ≤ t → |f t - g t| ≤ D) (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    |invTq k p q a φ f x y - invTq k p q a φ g x y| ≤ a * D := by
  have h1 := mv_repr hφ hf hy (B := Bf) (fun t ht => hBf t ht.1)
  have h2 := mv_repr hφ hg hy (B := Bg) (fun t ht => hBg t ht.1)
  have : invTq k p q a φ f x y - invTq k p q a φ g x y = a * (Mv φ f y - Mv φ g y) := by
    rw [← h1, ← h2]; unfold invTq; ring
  rw [this, abs_mul, abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left
    (mv_sub_le hφ hf hg hy (fun t ht => hBf t ht.1) (fun t ht => hBg t ht.1) hD) ha

lemma Lq_bd (p q : ℝ) {φ : ℝ → ℝ} (hφ : DemandDensity φ) (hp : 0 ≤ p) (hq : 0 ≤ q) {y : ℝ}
    (hy : 0 ≤ y) :
    |∫ s in Set.Ioi y, (p * (s - y) + q) * φ s| ≤ ∫ s in Set.Ioi 0, (p * s + q) * φ s := by
  have hI : IntegrableOn (fun s => (p * s + q) * φ s) (Set.Ioi 0) := by
    have e : (fun s => (p * s + q) * φ s) = (fun s => p * (s * φ s) + q * φ s) := by
      funext s; ring
    rw [e]; exact (hφ.mean.const_mul p).add (hφ.integrable.const_mul q)
  have h1 : ‖∫ s in Set.Ioi y, (p * (s - y) + q) * φ s‖ ≤ ∫ s in Set.Ioi y, (p * s + q) * φ s := by
    refine norm_integral_le_of_norm_le (hI.mono_set (Set.Ioi_subset_Ioi hy)) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
    have hs' : y < s := hs
    have hφs := hφ.pos s (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by nlinarith) hφs.le)]
    exact mul_le_mul_of_nonneg_right (by nlinarith) hφs.le
  rw [Real.norm_eq_abs] at h1
  refine h1.trans (setIntegral_mono_set hI ?_ (Filter.Eventually.of_forall (Set.Ioi_subset_Ioi hy)))
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
  have hs' : (0:ℝ) < s := hs
  exact mul_nonneg (by nlinarith) (hφ.pos s hs').le

lemma phi0_bd (k p q a xbar : ℝ) {φ : ℝ → ℝ} (hφ : DemandDensity φ) (hk : 0 < k) (hp : 0 ≤ p)
    (hq : 0 ≤ q) (ha : 0 ≤ a) (hxbar : 0 ≤ xbar) {x : ℝ} (hx : 0 ≤ x) :
    |PhiOp k p q a xbar φ (fun _ => 0) x| ≤
      k * xbar + a * ∫ s in Set.Ioi 0, (p * s + q) * φ s := by
  have hm : 0 ≤ max x xbar := le_trans hx (le_max_left _ _)
  have hL := Lq_bd p q hφ hp hq hm
  simp only [PhiOp, invTq, zero_mul, intervalIntegral.integral_zero, add_zero]
  have h2 : |k * (max x xbar - x)| ≤ k * xbar := by
    rw [abs_of_nonneg (mul_nonneg hk.le (by linarith [le_max_left x xbar]))]
    refine mul_le_mul_of_nonneg_left ?_ hk.le
    rcases le_total x xbar with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  calc _ ≤ |k * (max x xbar - x)| + |a * ∫ s in Set.Ioi (max x xbar), (p * (s - max x xbar) + q) * φ s| :=
        abs_add_le _ _
    _ ≤ _ := by
        rw [abs_mul a, abs_of_nonneg ha]
        exact add_le_add h2 (mul_le_mul_of_nonneg_left hL ha)

lemma phi_const (k p q a xbar : ℝ) (φ f : ℝ → ℝ) (hxbar : 0 ≤ xbar) {t : ℝ} (ht : t ≤ xbar) :
    PhiOp k p q a xbar φ f t + k * t = PhiOp k p q a xbar φ f 0 + k * 0 := by
  simp only [PhiOp]
  rw [invTq_shift, invTq_shift, max_eq_right ht, max_eq_right hxbar]

lemma phi_mono (k p q a xbar : ℝ) {φ f : ℝ → ℝ} (hφ : DemandDensity φ) (ha : 0 ≤ a)
    (hxbar : 0 ≤ xbar) (hlast : MonotoneOn (psiQ k p q a φ) (Set.Ici xbar)) (hf : InvP k f) :
    Monotone (fun x => PhiOp k p q a xbar φ f x + k * x) := by
  obtain ⟨hfm, ⟨B, hB⟩, hmono⟩ := hf
  have hv : Measurable (fun t => f t + k * t) := hfm.add (measurable_const.mul measurable_id)
  have hBv : ∀ y, ∃ B', ∀ t ∈ Set.Icc (0:ℝ) y, |f t + k * t| ≤ B' := by
    intro y
    refine ⟨B + |k| * |y|, fun t ht => ?_⟩
    calc |f t + k * t| ≤ |f t| + |k * t| := abs_add_le _ _
      _ ≤ B + |k| * |y| := by
        rw [abs_mul]
        exact add_le_add (hB t ht.1) (mul_le_mul_of_nonneg_left
          (by rw [abs_of_nonneg ht.1, abs_of_nonneg (ht.1.trans ht.2)]; exact ht.2) (abs_nonneg _))
  intro x₁ x₂ h12
  simp only [PhiOp]
  have hm1 : 0 ≤ max x₁ xbar := le_trans hxbar (le_max_right _ _)
  have hm2 : 0 ≤ max x₂ xbar := le_trans hxbar (le_max_right _ _)
  rw [invTq_shift, invTq_shift, invTq_decomp k p q a hφ hfm hm1 (B := B) (fun t ht => hB t ht.1),
    invTq_decomp k p q a hφ hfm hm2 (B := B) (fun t ht => hB t ht.1)]
  have hmm : max x₁ xbar ≤ max x₂ xbar := max_le_max h12 le_rfl
  have hψ := hlast (Set.mem_Ici.2 (le_max_right x₁ xbar)) (Set.mem_Ici.2 (le_max_right x₂ xbar)) hmm
  have hM := mv_mono hφ hv hBv hmono hm1 hmm
  nlinarith

lemma phi_inv (k p q a xbar : ℝ) {φ f : ℝ → ℝ} (hφ : DemandDensity φ) (hk : 0 < k) (hp : 0 ≤ p)
    (hq : 0 ≤ q) (ha : 0 ≤ a) (hxbar : 0 ≤ xbar)
    (hlast : MonotoneOn (psiQ k p q a φ) (Set.Ici xbar)) (hf : InvP k f) :
    InvP k (PhiOp k p q a xbar φ f) := by
  have hM := phi_mono k p q a xbar hφ ha hxbar hlast hf
  obtain ⟨hfm, ⟨B, hB⟩, hmono⟩ := hf
  refine ⟨?_, ?_, fun x _ y _ hxy => hM hxy⟩
  · have : PhiOp k p q a xbar φ f =
        fun x => (PhiOp k p q a xbar φ f x + k * x) - k * x := by funext x; ring
    rw [this]
    exact hM.measurable.sub (measurable_const.mul measurable_id)
  · refine ⟨a * B + (k * xbar + a * ∫ s in Set.Ioi 0, (p * s + q) * φ s), fun x hx => ?_⟩
    have h1 := invTq_contr k p q a hφ ha hfm (measurable_const (a := (0:ℝ))) hB
      (Bg := 0) (fun t _ => by simp) (D := B) (fun t ht => by simpa using hB t ht) x
      (le_trans hx (le_max_left x xbar))
    have h2 := phi0_bd k p q a xbar hφ hk hp hq ha hxbar hx
    simp only [PhiOp] at h1 h2 ⊢
    calc _ = |(invTq k p q a φ f x (max x xbar) - invTq k p q a φ (fun _ => 0) x (max x xbar)) +
          invTq k p q a φ (fun _ => 0) x (max x xbar)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1 h2)


lemma invP_locB {k : ℝ} {f : ℝ → ℝ} (hf : InvP k f) :
    ∃ B, ∀ y, 0 ≤ y → ∀ t ∈ Set.Icc (0:ℝ) y, |f t| ≤ B := by
  obtain ⟨_, ⟨B, hB⟩, _⟩ := hf
  exact ⟨B, fun y _ t ht => hB t ht.1⟩

lemma least_of (k p q a xbar : ℝ) {φ f : ℝ → ℝ} (hφ : DemandDensity φ) (ha : 0 < a)
    (hxbar : 0 ≤ xbar)
    (hmin : ∀ y : ℝ, 0 ≤ y → psiQ k p q a φ xbar ≤ psiQ k p q a φ y)
    (hlast : MonotoneOn (psiQ k p q a φ) (Set.Ici xbar)) (hf : InvP k f)
    (hc : ∀ t ∈ Set.Icc (0:ℝ) xbar, f t + k * t = f 0) {x : ℝ} (hx : 0 ≤ x) :
    IsLeast (invTq k p q a φ f x '' Set.Ici x) (invTq k p q a φ f x (max x xbar)) := by
  refine ⟨⟨max x xbar, Set.mem_Ici.2 (le_max_left _ _), rfl⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hy' : x ≤ y := hy
  have y0 : 0 ≤ y := hx.trans hy'
  have hm0 : 0 ≤ max x xbar := hx.trans (le_max_left _ _)
  obtain ⟨hfm, ⟨B, hB⟩, hmono⟩ := hf
  have hv : Measurable (fun t => f t + k * t) := hfm.add (measurable_const.mul measurable_id)
  rw [invTq_decomp k p q a hφ hfm hm0 (B := B) (fun t ht => hB t ht.1),
    invTq_decomp k p q a hφ hfm y0 (B := B) (fun t ht => hB t ht.1)]
  rcases le_or_gt xbar y with h | h
  · have hmy : max x xbar ≤ y := max_le hy' h
    have hψ := hlast (Set.mem_Ici.2 (le_max_right x xbar)) (Set.mem_Ici.2 h) hmy
    have hBv : ∀ y, ∃ B', ∀ t ∈ Set.Icc (0:ℝ) y, |f t + k * t| ≤ B' := by
      intro y
      refine ⟨B + |k| * |y|, fun t ht => ?_⟩
      calc |f t + k * t| ≤ |f t| + |k * t| := abs_add_le _ _
        _ ≤ B + |k| * |y| := by
          rw [abs_mul]
          exact add_le_add (hB t ht.1) (mul_le_mul_of_nonneg_left
            (by rw [abs_of_nonneg ht.1, abs_of_nonneg (ht.1.trans ht.2)]; exact ht.2) (abs_nonneg _))
    have hM := mv_mono hφ hv hBv hmono hm0 hmy
    nlinarith
  · rw [max_eq_right (hy'.trans h.le)]
    have hψ := hmin y y0
    have hc' : ∀ t ∈ Set.Icc (0:ℝ) xbar, (fun t => f t + k * t) t = (fun t => f t + k * t) 0 := by
      intro t ht; simp only [mul_zero, add_zero]; exact hc t ht
    rw [mv_const hφ y0 h.le hc', mv_const hφ hxbar le_rfl hc']
    linarith

theorem rt_core (k p q a : ℝ) (φ : ℝ → ℝ)
    (hk : 0 < k) (hp : 0 < p) (hq : 0 ≤ q) (hφ : DemandDensity φ)
    (ha0 : 0 < a) (ha1 : a < 1)
    (xbar : ℝ) (hxbar : 0 ≤ xbar)
    (hmin : ∀ y : ℝ, 0 ≤ y → psiQ k p q a φ xbar ≤ psiQ k p q a φ y)
    (hlast : MonotoneOn (psiQ k p q a φ) (Set.Ici xbar)) :
    ∃ f : ℝ → ℝ, BoundedClass f ∧ SolvesInf (invTq k p q a φ) f ∧
      (∀ g : ℝ → ℝ, BoundedClass g → SolvesInf (invTq k p q a φ) g →
        Set.EqOn g f (Set.Ici 0)) ∧
      ∀ x : ℝ, 0 ≤ x →
        IsLeast (invTq k p q a φ f x '' Set.Ici x) (invTq k p q a φ f x (max x xbar)) := by
  set Φ := PhiOp k p q a xbar φ with hΦ
  set F : ℕ → ℝ → ℝ := fun n => Φ^[n] (fun _ => 0) with hFdef
  have hFs : ∀ n, F (n + 1) = Φ (F n) := fun n => Function.iterate_succ_apply' Φ n _
  have hF0 : InvP k (fun _ => (0:ℝ)) := by
    refine ⟨measurable_const, ⟨0, fun t _ => by simp⟩, fun s hs t ht hst => ?_⟩
    simp only [zero_add]; nlinarith
  have hInv : ∀ n, InvP k (F n) := by
    intro n; induction n with
    | zero => exact hF0
    | succ n ih => rw [hFs]; exact phi_inv k p q a xbar hφ hk hp.le hq ha0.le hxbar hlast ih
  obtain ⟨B1, hB1⟩ := (hInv 1).2.1
  have hstep : ∀ n x, |F (n + 2) x - F (n + 1) x| ≤ a ^ (n + 1) * B1 := by
    intro n; induction n with
    | zero =>
      intro x
      obtain ⟨b0, hb0⟩ := (hInv 0).2.1
      have := invTq_contr k p q a hφ ha0.le (hInv 1).1 (hInv 0).1 hB1 hb0 (D := B1)
        (fun t ht => by simpa [hFdef] using hB1 t ht) x (hxbar.trans (le_max_right x xbar))
      have e1 : F (0 + 2) x = invTq k p q a φ (F 1) x (max x xbar) := by rw [hFs 1]; rfl
      have e2 : F (0 + 1) x = invTq k p q a φ (F 0) x (max x xbar) := by rw [hFs 0]; rfl
      rw [e1, e2]; simpa using this
    | succ n ih =>
      intro x
      obtain ⟨b1, hb1⟩ := (hInv (n + 2)).2.1
      obtain ⟨b2, hb2⟩ := (hInv (n + 1)).2.1
      have := invTq_contr k p q a hφ ha0.le (hInv (n + 2)).1 (hInv (n + 1)).1 hb1 hb2
        (D := a ^ (n + 1) * B1) (fun t _ => ih t) x (hxbar.trans (le_max_right x xbar))
      have e1 : F (n + 1 + 2) x = invTq k p q a φ (F (n + 2)) x (max x xbar) := by rw [hFs (n + 2)]; rfl
      have e2 : F (n + 1 + 1) x = invTq k p q a φ (F (n + 1)) x (max x xbar) := by rw [hFs (n + 1)]; rfl
      rw [e1, e2]
      calc _ ≤ a * (a ^ (n + 1) * B1) := this
        _ = a ^ (n + 1 + 1) * B1 := by ring
  have hdist : ∀ x n, dist (F (n + 1) x) (F (n + 1 + 1) x) ≤ (a * B1) * a ^ n := by
    intro x n
    rw [dist_comm, Real.dist_eq]
    calc _ ≤ a ^ (n + 1) * B1 := hstep n x
      _ = _ := by ring
  have hcs : ∀ x, CauchySeq (fun n => F (n + 1) x) := fun x =>
    cauchySeq_of_le_geometric a (a * B1) ha1 (hdist x)
  set fs : ℝ → ℝ := fun x => limUnder atTop (fun n => F (n + 1) x) with hfs
  have htend : ∀ x, Tendsto (fun n => F (n + 1) x) atTop (𝓝 (fs x)) :=
    fun x => (hcs x).tendsto_limUnder
  have hd : ∀ x n, dist (F (n + 1) x) (fs x) ≤ a * B1 * a ^ n / (1 - a) := fun x n =>
    dist_le_of_le_geometric_of_tendsto a (a * B1) ha1 (hdist x) (htend x) n
  have hfsm : Measurable fs :=
    measurable_of_tendsto_metrizable (f := fun n => F (n + 1)) (fun n => (hInv (n + 1)).1)
      (tendsto_pi_nhds.2 htend)
  have hfsB : ∀ t, 0 ≤ t → |fs t| ≤ B1 + a * B1 / (1 - a) := by
    intro t ht
    have h1 := hd t 0
    rw [Real.dist_eq, pow_zero, mul_one] at h1
    have h2 := hB1 t ht
    calc |fs t| = |F (0 + 1) t - (F (0 + 1) t - fs t)| := by ring_nf
      _ ≤ |F (0 + 1) t| + |F (0 + 1) t - fs t| := abs_sub _ _
      _ ≤ _ := add_le_add h2 h1
  have hfsmono : MonotoneOn (fun t => fs t + k * t) (Set.Ici 0) := by
    intro t1 ht1 t2 ht2 h
    exact le_of_tendsto_of_tendsto' ((htend t1).add_const _) ((htend t2).add_const _)
      (fun n => (hInv (n + 1)).2.2 ht1 ht2 h)
  have hfsInv : InvP k fs := ⟨hfsm, ⟨_, hfsB⟩, hfsmono⟩
  have hfsc : ∀ t ∈ Set.Icc (0:ℝ) xbar, fs t + k * t = fs 0 := by
    intro t ht
    have e : (fun n => F (n + 1) t + k * t) = fun n => F (n + 1) 0 := by
      funext n
      rw [hFs n]
      have := phi_const k p q a xbar φ (F n) hxbar ht.2
      simpa using this
    have h1 := (htend t).add_const (k * t)
    rw [e] at h1
    exact tendsto_nhds_unique h1 (htend 0)
  have hfix : ∀ x, Φ fs x = fs x := by
    intro x
    have hb : ∀ n, |F (n + 1 + 1) x - Φ fs x| ≤ a * (a * B1 * a ^ n / (1 - a)) := by
      intro n
      obtain ⟨b2, hb2⟩ := (hInv (n + 1)).2.1
      have := invTq_contr k p q a hφ ha0.le hfsm (hInv (n + 1)).1 hfsB hb2
        (D := a * B1 * a ^ n / (1 - a))
        (fun t _ => by rw [abs_sub_comm, ← Real.dist_eq]; exact hd t n) x
        (hxbar.trans (le_max_right x xbar))
      rw [hFs (n + 1), abs_sub_comm]
      exact this
    have hlim : Tendsto (fun n : ℕ => a * (a * B1 * a ^ n / (1 - a))) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1).const_mul (a * B1)).div_const
        (1 - a) |>.const_mul a
      simpa using this
    have h1 : Tendsto (fun n => F (n + 1 + 1) x) atTop (𝓝 (Φ fs x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun n => norm_nonneg _) (fun n => by rw [Real.norm_eq_abs]; exact hb n) hlim
    exact tendsto_nhds_unique h1 ((htend x).comp (tendsto_add_atTop_nat 1))
  have hleast : ∀ x : ℝ, 0 ≤ x →
      IsLeast (invTq k p q a φ fs x '' Set.Ici x) (invTq k p q a φ fs x (max x xbar)) :=
    fun x hx => least_of k p q a xbar hφ ha0 hxbar hmin hlast hfsInv hfsc hx
  have hval : ∀ x, invTq k p q a φ fs x (max x xbar) = fs x := hfix
  refine ⟨fs, ⟨hfsm, _, hfsB⟩, fun x hx => ?_, ?_, hleast⟩
  · have := (hleast x hx).isGLB
    rwa [hval] at this
  · rintro g ⟨hgm, Mg, hMg⟩ hgs
    have key : ∀ n : ℕ, ∀ t, 0 ≤ t → |g t - fs t| ≤ a ^ n * (Mg + (B1 + a * B1 / (1 - a))) := by
      intro n; induction n with
      | zero =>
        intro t ht
        rw [pow_zero, one_mul]
        exact (abs_sub _ _).trans (add_le_add (hMg t ht) (hfsB t ht))
      | succ n ih =>
        intro x hx
        set D := a ^ n * (Mg + (B1 + a * B1 / (1 - a)))
        have hc : ∀ y, 0 ≤ y → |invTq k p q a φ g x y - invTq k p q a φ fs x y| ≤ a * D :=
          fun y hy => invTq_contr k p q a hφ ha0.le hgm hfsm hMg hfsB ih x hy
        have up : g x ≤ invTq k p q a φ g x (max x xbar) :=
          (hgs x hx).1 ⟨max x xbar, Set.mem_Ici.2 (le_max_left _ _), rfl⟩
        have h1 := hc (max x xbar) (hx.trans (le_max_left _ _))
        rw [hval] at h1
        have lo : fs x - a * D ≤ g x := by
          refine (hgs x hx).2 ?_
          rintro _ ⟨y, hy, rfl⟩
          have hy' : x ≤ y := hy
          have h2 := (hleast x hx).2 ⟨y, hy, rfl⟩
          rw [hval] at h2
          have h3 := hc y (hx.trans hy')
          rw [abs_le] at h3
          linarith
        rw [abs_le] at h1 ⊢
        constructor
        · calc -(a ^ (n + 1) * (Mg + (B1 + a * B1 / (1 - a)))) = -(a * D) := by ring
            _ ≤ _ := by linarith
        · calc g x - fs x ≤ a * D := by linarith
            _ = _ := by ring
    intro t ht
    have hlim : Tendsto (fun n : ℕ => a ^ n * (Mg + (B1 + a * B1 / (1 - a)))) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1).mul_const
        (Mg + (B1 + a * B1 / (1 - a)))
    have h0 : |g t - fs t| ≤ 0 := ge_of_tendsto' hlim (fun n => key n t ht)
    have := abs_nonpos_iff.1 h0
    linarith

lemma dd_ii {φ : ℝ → ℝ} (hφ : DemandDensity φ) {y : ℝ} (hy : 0 ≤ y) :
    IntervalIntegrable φ volume 0 y :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).2
    (hφ.integrable.mono_set Set.Ioc_subset_Ioi_self)

lemma dd_tail {φ : ℝ → ℝ} (hφ : DemandDensity φ) {y : ℝ} (hy : 0 ≤ y) :
    ∫ s in Set.Ioi y, φ s = 1 - ∫ s in (0:ℝ)..y, φ s := by
  have h := setIntegral_union (Set.Ioc_disjoint_Ioi_same (a := (0:ℝ)) (b := y)) measurableSet_Ioi
    (hφ.integrable.mono_set Set.Ioc_subset_Ioi_self) (hφ.integrable.mono_set (Set.Ioi_subset_Ioi hy))
  rw [Set.Ioc_union_Ioi_eq_Ioi hy, hφ.total] at h
  rw [intervalIntegral.integral_of_le hy]; linarith

lemma dd_strict {φ : ℝ → ℝ} (hφ : DemandDensity φ) {y₁ y₂ : ℝ} (h1 : 0 ≤ y₁) (h12 : y₁ < y₂) :
    (∫ s in (0:ℝ)..y₁, φ s) < ∫ s in (0:ℝ)..y₂, φ s := by
  have hi1 := dd_ii hφ h1
  have hi2 := dd_ii hφ (h1.trans h12.le)
  have h := intervalIntegral.integral_add_adjacent_intervals hi1 (hi1.symm.trans hi2)
  have hpos : 0 < ∫ s in y₁..y₂, φ s :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hi1.symm.trans hi2)
      (fun x hx => hφ.pos x (lt_of_le_of_lt h1 hx.1)) h12
  linarith

lemma root_iff (k p a : ℝ) (φ : ℝ → ℝ) (hk : 0 < k) (hp : 0 < p) (hφ : DemandDensity φ)
    (ha0 : 0 < a) (ha1 : a < 1) (hapk : k < a * p) {y : ℝ} (hy : 0 ≤ y) :
    StockLevelRoot k p a φ y ↔ (∫ s in (0 : ℝ)..y, φ s) = (a * p - k) / (a * (p - k)) := by
  have hpk : k < p := by nlinarith
  have hden : 0 < a * (p - k) := mul_pos ha0 (by linarith)
  unfold StockLevelRoot
  rw [dd_tail hφ hy, eq_div_iff hden.ne']
  constructor <;> intro h <;> linarith

theorem root_core (k p a : ℝ) (φ : ℝ → ℝ)
    (hk : 0 < k) (hp : 0 < p) (hφ : DemandDensity φ)
    (ha0 : 0 < a) (ha1 : a < 1) (hapk : k < a * p) :
    (∀ y : ℝ, 0 ≤ y →
      (StockLevelRoot k p a φ y ↔ (∫ s in (0 : ℝ)..y, φ s) = (a * p - k) / (a * (p - k)))) ∧
    ∃ xbar : ℝ, 0 ≤ xbar ∧ StockLevelRoot k p a φ xbar ∧
      ∀ y : ℝ, 0 ≤ y → StockLevelRoot k p a φ y → y = xbar := by
  refine ⟨fun y hy => root_iff k p a φ hk hp hφ ha0 ha1 hapk hy, ?_⟩
  have hpk : k < p := by nlinarith
  have hden : 0 < a * (p - k) := mul_pos ha0 (by linarith)
  set c := (a * p - k) / (a * (p - k)) with hc
  have hc0 : 0 < c := div_pos (by linarith) hden
  have hc1 : c < 1 := by rw [div_lt_one hden]; nlinarith
  have ht := intervalIntegral_tendsto_integral_Ioi (μ := volume) 0 hφ.integrable tendsto_id
  rw [hφ.total] at ht
  obtain ⟨b, hb⟩ := (ht.eventually (lt_mem_nhds hc1)).exists_forall_of_atTop
  set b' := max b 1
  have hb' : c < ∫ s in (0:ℝ)..b', φ s := hb b' (le_max_left _ _)
  have hb'0 : 0 ≤ b' := le_trans zero_le_one (le_max_right _ _)
  have hcont : ContinuousOn (fun x => ∫ s in (0:ℝ)..x, φ s) (Set.Icc 0 b') := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := b') (f := φ)
      (by rw [Set.uIcc_of_le hb'0, integrableOn_Icc_iff_integrableOn_Ioc]
          exact hφ.integrable.mono_set Set.Ioc_subset_Ioi_self)
    rwa [Set.uIcc_of_le hb'0] at this
  have hivt := intermediate_value_Icc hb'0 hcont
  obtain ⟨x, hx, hxc⟩ := hivt ⟨by simp; linarith, hb'.le⟩
  refine ⟨x, hx.1, (root_iff k p a φ hk hp hφ ha0 ha1 hapk hx.1).2 hxc, fun y hy hroot => ?_⟩
  have hyc := (root_iff k p a φ hk hp hφ ha0 ha1 hapk hy).1 hroot
  rcases lt_trichotomy y x with h | h | h
  · have := dd_strict hφ hy h; simp only at hxc; linarith
  · exact h
  · have := dd_strict hφ hx.1 h; simp only at hxc; linarith


lemma posmax_int {φ : ℝ → ℝ} (hφ : DemandDensity φ) {y : ℝ} (hy : 0 ≤ y) :
    IntegrableOn (fun s => max (s - y) 0 * φ s) (Set.Ioi 0) := by
  refine Integrable.mono' hφ.mean
    (((continuous_id.sub continuous_const).max continuous_const).aestronglyMeasurable.mul
      hφ.integrable.aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
  have hs' : (0:ℝ) < s := hs
  have hφs := (hφ.pos s hs').le
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_max_right _ _), abs_of_nonneg hφs]
  exact mul_le_mul_of_nonneg_right (max_le (by linarith) hs'.le) hφs

lemma posmax_eq {φ : ℝ → ℝ} (hφ : DemandDensity φ) {y : ℝ} (hy : 0 ≤ y) :
    ∫ s in Set.Ioi 0, max (s - y) 0 * φ s = ∫ s in Set.Ioi y, (s - y) * φ s := by
  have hint := posmax_int hφ hy
  have h := setIntegral_union (Set.Ioc_disjoint_Ioi_same (a := (0:ℝ)) (b := y)) measurableSet_Ioi
    (hint.mono_set Set.Ioc_subset_Ioi_self) (hint.mono_set (Set.Ioi_subset_Ioi hy))
  rw [Set.Ioc_union_Ioi_eq_Ioi hy] at h
  rw [h]
  have h0 : ∫ s in Set.Ioc 0 y, max (s - y) 0 * φ s = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0:ℝ)) (fun s hs => by
      rw [max_eq_right (by linarith [hs.2]), zero_mul])]
    simp
  rw [h0, zero_add]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have : y < s := hs
  rw [max_eq_left (by linarith)]

noncomputable def gfun (k p a y s : ℝ) : ℝ := k * y + a * (p * max (s - y) 0 - k * max (y - s) 0)

lemma g_int (k p a : ℝ) {φ : ℝ → ℝ} (hφ : DemandDensity φ) {y : ℝ} (hy : 0 ≤ y) :
    IntegrableOn (fun s => gfun k p a y s * φ s) (Set.Ioi 0) := by
  have hid : ∀ t ∈ Set.Icc (0:ℝ) y, |id t| ≤ y := fun t ht => by
    rw [id, abs_of_nonneg ht.1]; exact ht.2
  have i3 : IntegrableOn (fun s => max (y - s) 0 * φ s) (Set.Ioi 0) := mv_int hφ measurable_id hy hid
  have := ((hφ.integrable.const_mul (k * y)).add ((posmax_int hφ hy).const_mul (a * p))).sub
    (i3.const_mul (a * k))
  have e : (fun s => gfun k p a y s * φ s) =
      (fun s => k * y * φ s + a * p * (max (s - y) 0 * φ s) - a * k * (max (y - s) 0 * φ s)) := by
    funext s; unfold gfun; ring
  rw [e]; exact this

lemma psi_repr (k p a : ℝ) {φ : ℝ → ℝ} (hφ : DemandDensity φ) {y : ℝ} (hy : 0 ≤ y) :
    psiQ k p 0 a φ y = ∫ s in Set.Ioi 0, gfun k p a y s * φ s := by
  have hid : ∀ t ∈ Set.Icc (0:ℝ) y, |id t| ≤ y := fun t ht => by
    rw [id, abs_of_nonneg ht.1]; exact ht.2
  have i3 : IntegrableOn (fun s => max (y - s) 0 * φ s) (Set.Ioi 0) := mv_int hφ measurable_id hy hid
  have r3 := mv_repr hφ measurable_id hy hid
  simp only [id, zero_mul, zero_add] at r3
  have e : (fun s => gfun k p a y s * φ s) =
      (fun s => k * y * φ s + a * p * (max (s - y) 0 * φ s) - a * k * (max (y - s) 0 * φ s)) := by
    funext s; unfold gfun; ring
  have iA : IntegrableOn (fun s => k * y * φ s + a * p * (max (s - y) 0 * φ s)) (Set.Ioi 0) :=
    ((hφ.integrable.const_mul (k * y))).add ((posmax_int hφ hy).const_mul (a * p))
  have iB : IntegrableOn (fun s => a * k * (max (y - s) 0 * φ s)) (Set.Ioi 0) := i3.const_mul (a * k)
  rw [e, integral_sub iA iB, integral_add (hφ.integrable.const_mul (k * y))
    ((posmax_int hφ hy).const_mul (a * p)), integral_const_mul, integral_const_mul,
    integral_const_mul, hφ.total, posmax_eq hφ hy]
  have r3' : ∫ s in Set.Ioi 0, max (y - s) 0 * φ s = ∫ s in (0:ℝ)..y, (y - s) * φ s := by
    rw [r3]; rfl
  rw [r3']
  unfold psiQ
  have : ∫ s in Set.Ioi y, (p * (s - y) + 0) * φ s = p * ∫ s in Set.Ioi y, (s - y) * φ s := by
    rw [← integral_const_mul]; congr 1; funext s; ring
  rw [this]; ring

lemma g_mono_pt {k p a : ℝ} (h1 : a * p ≤ k) (h2 : a * k ≤ k) {y z : ℝ} (s : ℝ) (hyz : y ≤ z) :
    gfun k p a y s ≤ gfun k p a z s := by
  unfold gfun
  have h1' : 0 ≤ k - a * p := by linarith
  have h2' : 0 ≤ k - a * k := by linarith
  rcases le_total s y with hs | hs
  · rw [max_eq_right (by linarith : s - y ≤ 0), max_eq_left (by linarith : 0 ≤ y - s),
      max_eq_right (by linarith : s - z ≤ 0), max_eq_left (by linarith : 0 ≤ z - s)]
    nlinarith [mul_nonneg h2' (sub_nonneg.2 hyz)]
  · rcases le_total s z with hz | hz
    · rw [max_eq_left (by linarith : 0 ≤ s - y), max_eq_right (by linarith : y - s ≤ 0),
        max_eq_right (by linarith : s - z ≤ 0), max_eq_left (by linarith : 0 ≤ z - s)]
      nlinarith [mul_nonneg h2' (sub_nonneg.2 hz), mul_nonneg h1' (sub_nonneg.2 hs)]
    · rw [max_eq_left (by linarith : 0 ≤ s - y), max_eq_right (by linarith : y - s ≤ 0),
        max_eq_left (by linarith : 0 ≤ s - z), max_eq_right (by linarith : z - s ≤ 0)]
      nlinarith [mul_nonneg h1' (sub_nonneg.2 hyz)]

lemma g_sub_pt {k p a : ℝ} (h : a * k ≤ a * p) (y z s : ℝ) :
    gfun k p a y s + (z - y) * ((k - a * k) + (a * k - a * p) * (Set.Ioi y).indicator 1 s) ≤
      gfun k p a z s := by
  unfold gfun
  have h' : 0 ≤ a * p - a * k := by linarith
  by_cases hs : y < s
  · rw [Set.indicator_of_mem (show s ∈ Set.Ioi y from hs), Pi.one_apply,
      max_eq_left (by linarith : 0 ≤ s - y), max_eq_right (by linarith : y - s ≤ 0)]
    rcases le_total s z with hz | hz
    · rw [max_eq_right (by linarith : s - z ≤ 0), max_eq_left (by linarith : 0 ≤ z - s)]
      nlinarith [mul_nonneg h' (sub_nonneg.2 hz)]
    · rw [max_eq_left (by linarith : 0 ≤ s - z), max_eq_right (by linarith : z - s ≤ 0)]
      nlinarith
  · push_neg at hs
    rw [Set.indicator_of_notMem (show s ∉ Set.Ioi y from fun h => by simp at h; linarith),
      max_eq_right (by linarith : s - y ≤ 0), max_eq_left (by linarith : 0 ≤ y - s)]
    rcases le_total s z with hz | hz
    · rw [max_eq_right (by linarith : s - z ≤ 0), max_eq_left (by linarith : 0 ≤ z - s)]
      nlinarith
    · rw [max_eq_left (by linarith : 0 ≤ s - z), max_eq_right (by linarith : z - s ≤ 0)]
      nlinarith [mul_nonneg h' (sub_nonneg.2 hz)]

lemma psi_sub (k p a : ℝ) {φ : ℝ → ℝ} (hφ : DemandDensity φ) (h : a * k ≤ a * p) {y z : ℝ}
    (hy : 0 ≤ y) (hz : 0 ≤ z) :
    psiQ k p 0 a φ y + (z - y) * ((k - a * k) + (a * k - a * p) * ∫ s in Set.Ioi y, φ s) ≤
      psiQ k p 0 a φ z := by
  rw [psi_repr k p a hφ hy, psi_repr k p a hφ hz]
  have hind : IntegrableOn (fun s => (Set.Ioi y).indicator 1 s * φ s) (Set.Ioi 0) := by
    refine Integrable.bdd_mul (c := 1) hφ.integrable
      ((measurable_const.indicator measurableSet_Ioi).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun s => ?_
    by_cases hs : s ∈ Set.Ioi y <;> simp [Set.indicator, hs]
  have hindv : ∫ s in Set.Ioi 0, (Set.Ioi y).indicator 1 s * φ s = ∫ s in Set.Ioi y, φ s := by
    have e : (fun s => (Set.Ioi y).indicator 1 s * φ s) = (Set.Ioi y).indicator φ := by
      funext s; by_cases hs : s ∈ Set.Ioi y <;> simp [Set.indicator, hs]
    rw [e, setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi, max_eq_right hy]
  have hR : IntegrableOn (fun s => gfun k p a y s * φ s + (z - y) * ((k - a * k) * φ s +
      (a * k - a * p) * ((Set.Ioi y).indicator 1 s * φ s))) (Set.Ioi 0) :=
    (g_int k p a hφ hy).add (((hφ.integrable.const_mul _).add (hind.const_mul _)).const_mul _)
  have hcalc : ∫ s in Set.Ioi 0, (gfun k p a y s * φ s + (z - y) * ((k - a * k) * φ s +
      (a * k - a * p) * ((Set.Ioi y).indicator 1 s * φ s))) =
      (∫ s in Set.Ioi 0, gfun k p a y s * φ s) +
        (z - y) * ((k - a * k) + (a * k - a * p) * ∫ s in Set.Ioi y, φ s) := by
    have iC : IntegrableOn (fun s => (k - a * k) * φ s +
        (a * k - a * p) * ((Set.Ioi y).indicator 1 s * φ s)) (Set.Ioi 0) :=
      (hφ.integrable.const_mul _).add (hind.const_mul _)
    have iD : IntegrableOn (fun s => (z - y) * ((k - a * k) * φ s +
        (a * k - a * p) * ((Set.Ioi y).indicator 1 s * φ s))) (Set.Ioi 0) := iC.const_mul _
    have iE : IntegrableOn (fun s => (k - a * k) * φ s) (Set.Ioi 0) := hφ.integrable.const_mul _
    have iF : IntegrableOn (fun s => (a * k - a * p) * ((Set.Ioi y).indicator 1 s * φ s))
      (Set.Ioi 0) := hind.const_mul _
    rw [integral_add (g_int k p a hφ hy) iD, integral_const_mul,
      integral_add iE iF, integral_const_mul,
      integral_const_mul, hφ.total, hindv, mul_one]
  rw [← hcalc]
  refine setIntegral_mono_on hR (g_int k p a hφ hz) measurableSet_Ioi (fun s hs => ?_)
  have hφs := (hφ.pos s hs).le
  have := mul_le_mul_of_nonneg_right (g_sub_pt h y z s) hφs
  linarith [this]


lemma invT_eq (k p a : ℝ) (φ : ℝ → ℝ) : invT k p a φ = invTq k p 0 a φ := by
  funext f x y; unfold invT invTq; simp

lemma tail_anti {φ : ℝ → ℝ} (hφ : DemandDensity φ) {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) :
    ∫ s in Set.Ioi z, φ s ≤ ∫ s in Set.Ioi y, φ s := by
  refine setIntegral_mono_set (hφ.integrable.mono_set (Set.Ioi_subset_Ioi hy)) ?_
    (Filter.Eventually.of_forall (Set.Ioi_subset_Ioi hyz))
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
  have : y < s := hs
  exact (hφ.pos s (by linarith)).le

theorem goal_core (k p a : ℝ) (φ : ℝ → ℝ)
    (hk : 0 < k) (hp : 0 < p) (hφ : DemandDensity φ) (ha0 : 0 < a) (ha1 : a < 1) :
    (k < a * p →
      ∃ xbar : ℝ, 0 ≤ xbar ∧ StockLevelRoot k p a φ xbar ∧
        (∀ y : ℝ, 0 ≤ y → StockLevelRoot k p a φ y → y = xbar) ∧
        ∃ f : ℝ → ℝ, BoundedClass f ∧ SolvesInf (invT k p a φ) f ∧
          (∀ g : ℝ → ℝ, BoundedClass g → SolvesInf (invT k p a φ) g →
            Set.EqOn g f (Set.Ici 0)) ∧
          ∀ x : ℝ, 0 ≤ x →
            IsLeast (invT k p a φ f x '' Set.Ici x) (invT k p a φ f x (max x xbar))) ∧
    (a * p ≤ k →
      ∃ f : ℝ → ℝ, BoundedClass f ∧ SolvesInf (invT k p a φ) f ∧
        (∀ g : ℝ → ℝ, BoundedClass g → SolvesInf (invT k p a φ) g →
          Set.EqOn g f (Set.Ici 0)) ∧
        ∀ x : ℝ, 0 ≤ x → IsLeast (invT k p a φ f x '' Set.Ici x) (invT k p a φ f x x)) := by
  rw [invT_eq]
  constructor
  · intro hapk
    obtain ⟨_, xbar, hx0, hroot, huniq⟩ := root_core k p a φ hk hp hφ ha0 ha1 hapk
    have hpk : k < p := by nlinarith
    have hakp : a * k ≤ a * p := by nlinarith
    have hh : (k - a * k) + (a * k - a * p) * ∫ s in Set.Ioi xbar, φ s = 0 := by
      have hr := hroot
      unfold StockLevelRoot at hr
      rw [dd_tail hφ hx0] at hr ⊢
      linear_combination hr
    have hmin : ∀ y : ℝ, 0 ≤ y → psiQ k p 0 a φ xbar ≤ psiQ k p 0 a φ y := by
      intro y hy
      have := psi_sub k p a hφ hakp hx0 hy
      rw [hh, mul_zero, add_zero] at this
      exact this
    have hlast : MonotoneOn (psiQ k p 0 a φ) (Set.Ici xbar) := by
      intro y hy z hz hyz
      have hy' : xbar ≤ y := hy
      have := psi_sub k p a hφ hakp (hx0.trans hy') (hx0.trans hz)
      have ht := tail_anti hφ hx0 hy'
      have hnn : 0 ≤ (k - a * k) + (a * k - a * p) * ∫ s in Set.Ioi y, φ s := by
        nlinarith [mul_le_mul_of_nonpos_left ht (by linarith : a * k - a * p ≤ 0)]
      nlinarith [mul_nonneg (sub_nonneg.2 hyz) hnn]
    obtain ⟨f, hfB, hfS, hfU, hfL⟩ := rt_core k p 0 a φ hk hp le_rfl hφ ha0 ha1 xbar hx0 hmin hlast
    exact ⟨xbar, hx0, hroot, huniq, f, hfB, hfS, hfU, hfL⟩
  · intro hapk
    have hak : a * k ≤ k := by nlinarith
    have hlast : MonotoneOn (psiQ k p 0 a φ) (Set.Ici 0) := by
      intro y hy z hz hyz
      rw [psi_repr k p a hφ hy, psi_repr k p a hφ hz]
      refine setIntegral_mono_on (g_int k p a hφ hy) (g_int k p a hφ hz) measurableSet_Ioi
        (fun s hs => mul_le_mul_of_nonneg_right (g_mono_pt hapk hak s hyz) (hφ.pos s hs).le)
    have hmin : ∀ y : ℝ, 0 ≤ y → psiQ k p 0 a φ 0 ≤ psiQ k p 0 a φ y :=
      fun y hy => hlast (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy
    obtain ⟨f, hfB, hfS, hfU, hfL⟩ := rt_core k p 0 a φ hk hp le_rfl hφ ha0 ha1 0 le_rfl hmin hlast
    refine ⟨f, hfB, hfS, hfU, fun x hx => ?_⟩
    have := hfL x hx
    rwa [max_eq_left hx] at this

end BellmanDP.Inventory

open BellmanDP.Inventory


theorem solution (k p a : ℝ) (φ : ℝ → ℝ)
    (hk : 0 < k) (hp : 0 < p) (hφ : DemandDensity φ) (ha0 : 0 < a) (ha1 : a < 1) :
    (k < a * p →
      ∃ xbar : ℝ, 0 ≤ xbar ∧ StockLevelRoot k p a φ xbar ∧
        (∀ y : ℝ, 0 ≤ y → StockLevelRoot k p a φ y → y = xbar) ∧
        ∃ f : ℝ → ℝ, BoundedClass f ∧ SolvesInf (invT k p a φ) f ∧
          (∀ g : ℝ → ℝ, BoundedClass g → SolvesInf (invT k p a φ) g →
            Set.EqOn g f (Set.Ici 0)) ∧
          ∀ x : ℝ, 0 ≤ x →
            IsLeast (invT k p a φ f x '' Set.Ici x) (invT k p a φ f x (max x xbar))) ∧
    (a * p ≤ k →
      ∃ f : ℝ → ℝ, BoundedClass f ∧ SolvesInf (invT k p a φ) f ∧
        (∀ g : ℝ → ℝ, BoundedClass g → SolvesInf (invT k p a φ) g →
          Set.EqOn g f (Set.Ici 0)) ∧
        ∀ x : ℝ, 0 ≤ x → IsLeast (invT k p a φ f x '' Set.Ici x) (invT k p a φ f x x)) := by
  exact goal_core k p a φ hk hp hφ ha0 ha1
