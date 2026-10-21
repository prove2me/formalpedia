-- Prove2me | solution 1 for ContagionGrowth.FluidLimit.eq_24_25
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T19:24:26.522845+00:00
-- url     : https://prove2.me/submissions/b205a630-a1b8-4272-adc9-a810d1f826ec

import Mathlib
import Definitions.Def_ContagionGrowth_FluidLimit_Limit

namespace CGAux

open MeasureTheory ContagionGrowth.FluidLimit

/-- the order-statistic event -/
def Aset (c : ℝ) (θ l : ℕ) : Set (Fin l → ℝ) :=
  {x | ∀ u : ℕ, θ + 1 ≤ u → u ≤ l →
    (Finset.univ.filter (fun i => x i ≤ c * ((u : ℝ) - θ))).card < u}

/-- the box `[0, π]^l` -/
def box (l : ℕ) (π : ℝ) : Set (Fin l → ℝ) := {x | ∀ i, x i ∈ Set.Icc 0 π}

noncomputable def V (c : ℝ) (θ l : ℕ) (π : ℝ) : ℝ := volume.real (box l π ∩ Aset c θ l)

lemma box_eq (l : ℕ) (π : ℝ) : box l π = Set.univ.pi (fun _ => Set.Icc 0 π) := by
  ext x; simp [box, Pi.le_def, forall_and]

lemma box_meas (l : ℕ) (π : ℝ) : MeasurableSet (box l π) := by
  rw [box_eq]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

lemma box_vol (l : ℕ) (π : ℝ) : volume (box l π) = ENNReal.ofReal π ^ l := by
  rw [box_eq, volume_pi_pi]; simp [Real.volume_Icc]

lemma box_ne_top (l : ℕ) (π : ℝ) : volume (box l π) ≠ ⊤ := by
  rw [box_vol]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

lemma box_real (l : ℕ) {π : ℝ} (hπ : 0 ≤ π) : volume.real (box l π) = π ^ l := by
  rw [measureReal_def, box_vol, ENNReal.toReal_pow, ENNReal.toReal_ofReal hπ]

lemma box_mono (l : ℕ) {a b : ℝ} (h : a ≤ b) : box l a ⊆ box l b := by
  intro x hx i; exact ⟨(hx i).1, (hx i).2.trans h⟩

lemma Pord_lt (c : ℝ) {θ l : ℕ} (h : θ < l) (π : ℝ) :
    Pord c θ l π = V c θ l π / π ^ l := by
  simp only [Pord, if_neg (not_le.mpr h)]; rfl

lemma Pord_le (c : ℝ) {θ l : ℕ} (h : l ≤ θ) (π : ℝ) : Pord c θ l π = 1 := by
  simp [Pord, h]

lemma V_nonneg (c : ℝ) (θ l : ℕ) (π : ℝ) : 0 ≤ V c θ l π := measureReal_nonneg

lemma V_le (c : ℝ) (θ l : ℕ) {π : ℝ} (hπ : 0 ≤ π) : V c θ l π ≤ π ^ l := by
  rw [V, ← box_real l hπ]
  exact measureReal_mono Set.inter_subset_left (box_ne_top l π)

lemma V_zero (c : ℝ) (θ l : ℕ) (hl : 1 ≤ l) : V c θ l 0 = 0 := by
  have h1 := V_le c θ l (le_refl (0:ℝ))
  rw [zero_pow (by omega)] at h1
  exact le_antisymm h1 (V_nonneg _ _ _ _)

lemma V_diff (c : ℝ) (θ l : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    V c θ l a ≤ V c θ l b ∧ V c θ l b ≤ V c θ l a + (b ^ l - a ^ l) := by
  have hb : 0 ≤ b := ha.trans hab
  constructor
  · exact measureReal_mono (Set.inter_subset_inter_left _ (box_mono l hab))
      (measure_ne_top_of_subset Set.inter_subset_left (box_ne_top l b))
  · have hsub : box l b ∩ Aset c θ l ⊆ (box l a ∩ Aset c θ l) ∪ (box l b \ box l a) := by
      intro x hx
      by_cases hxa : x ∈ box l a
      · exact Or.inl ⟨hxa, hx.2⟩
      · exact Or.inr ⟨hx.1, hxa⟩
    have h1 : V c θ l b ≤ volume.real ((box l a ∩ Aset c θ l) ∪ (box l b \ box l a)) :=
      measureReal_mono hsub (by
        refine measure_ne_top_of_subset ?_ (box_ne_top l b)
        intro x hx
        rcases hx with hx | hx
        · exact box_mono l hab hx.1
        · exact hx.1)
    have h2 := measureReal_union_le (μ := volume) (box l a ∩ Aset c θ l) (box l b \ box l a)
    have h3 : volume.real (box l b \ box l a) = b ^ l - a ^ l := by
      rw [measureReal_sdiff (box_mono l hab) (box_meas l a) (box_ne_top l b),
        box_real l hb, box_real l ha]
    simp only [V] at *; linarith

lemma V_abs (c : ℝ) (θ l : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |V c θ l b - V c θ l a| ≤ |b ^ l - a ^ l| := by
  rcases le_total a b with hab | hab
  · obtain ⟨h1, h2⟩ := V_diff c θ l ha hab
    have : a ^ l ≤ b ^ l := pow_le_pow_left₀ ha hab l
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · obtain ⟨h1, h2⟩ := V_diff c θ l hb hab
    have : b ^ l ≤ a ^ l := pow_le_pow_left₀ hb hab l
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith

lemma V_cont (c : ℝ) (θ l : ℕ) : ContinuousOn (V c θ l) (Set.Ici 0) := by
  intro x0 hx0
  have hx0' : (0:ℝ) ≤ x0 := hx0
  rw [ContinuousWithinAt, ← tendsto_sub_nhds_zero_iff]
  have hp : Filter.Tendsto (fun x : ℝ => x ^ l - x0 ^ l) (nhdsWithin x0 (Set.Ici 0))
      (nhds 0) := by
    have : Filter.Tendsto (fun x : ℝ => x ^ l - x0 ^ l) (nhds x0) (nhds (x0 ^ l - x0 ^ l)) :=
      ((continuous_pow l).tendsto x0).sub tendsto_const_nhds
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ (by simpa using hp.norm)
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact V_abs c θ l hx0' hx

lemma Pord_nonneg (c : ℝ) (θ l : ℕ) {π : ℝ} (hπ : 0 ≤ π) : 0 ≤ Pord c θ l π := by
  rcases le_or_gt l θ with h | h
  · rw [Pord_le c h]; norm_num
  · rw [Pord_lt c h]; exact div_nonneg (V_nonneg _ _ _ _) (pow_nonneg hπ _)

lemma Pord_le_one (c : ℝ) (θ l : ℕ) {π : ℝ} (hπ : 0 ≤ π) : Pord c θ l π ≤ 1 := by
  rcases le_or_gt l θ with h | h
  · rw [Pord_le c h]
  · rw [Pord_lt c h]
    rcases hπ.lt_or_eq with hp | hp
    · exact div_le_one_of_le₀ (V_le c θ l hπ) (pow_nonneg hπ _)
    · subst hp; rw [zero_pow (by omega), div_zero]; norm_num

/-- `π^l P(π)` -/
lemma Q_eq (c : ℝ) {θ l : ℕ} (h : θ < l) {π : ℝ} (hπ : 0 ≤ π) :
    π ^ l * Pord c θ l π = V c θ l π := by
  rw [Pord_lt c h]
  rcases hπ.lt_or_eq with hp | hp
  · field_simp
  · subst hp; rw [V_zero c θ l (by omega), zero_pow (by omega), zero_mul]

lemma Q_cont (c : ℝ) (θ l : ℕ) :
    ContinuousOn (fun π : ℝ => π ^ l * Pord c θ l π) (Set.Ici 0) := by
  rcases le_or_gt l θ with h | h
  · have : (fun π : ℝ => π ^ l * Pord c θ l π) = fun π => π ^ l := by
      funext π; rw [Pord_le c h, mul_one]
    rw [this]; exact (continuous_pow l).continuousOn
  · exact (V_cont c θ l).congr (fun π hπ => Q_eq c h hπ)

/-- vanishing of `P` beyond the last threshold -/
lemma Pord_vanish (c : ℝ) {θ l : ℕ} (h : θ < l) {π : ℝ} (hle : π ≤ c * ((l : ℝ) - θ)) :
    Pord c θ l π = 0 := by
  rw [Pord_lt c h]
  have : box l π ∩ Aset c θ l = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx hA
    have := hA l (by omega) le_rfl
    have hf : (Finset.univ.filter (fun i => x i ≤ c * ((l : ℝ) - θ))) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro i _; exact (hx i).2.trans hle
    rw [hf, Finset.card_univ, Fintype.card_fin] at this
    exact lt_irrefl _ this
  rw [V, this, measureReal_empty, zero_div]

/-- the summand of `B^α` -/
noncomputable def bterm (α : ℝ) (lam θ : ℕ) (π : ℝ) (l : ℕ) : ℝ :=
  (lam.choose l : ℝ) * π ^ l * (1 - π) ^ (lam - l) * Pord (1 / (α * lam)) θ l π

lemma Balpha_eq (α : ℝ) (hα : 0 < α) (lam θ : ℕ) (hθ : θ ≠ 0) {π : ℝ} (hπ : 0 ≤ π) :
    Balpha α lam θ π = 1 - ∑ l ∈ Finset.range (lam + 1), bterm α lam θ π l := by
  simp only [Balpha, if_neg hθ]
  congr 1
  apply Finset.sum_filter_of_ne
  intro l hl hne
  by_contra hc
  apply hne
  rw [not_lt, Int.ceil_le] at hc
  push_cast at hc
  have hl' : l ≤ lam := by simpa [Nat.lt_succ_iff] using hl
  have hprod : 0 ≤ α * lam * π := by positivity
  rcases le_or_gt l θ with hlθ | hlθ
  · have hlθr : (l : ℝ) ≤ θ := by exact_mod_cast hlθ
    have h0 : α * lam * π = 0 := by linarith
    have hlq : (l : ℝ) = θ := by linarith
    have hlq' : l = θ := by exact_mod_cast hlq
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · linarith
      · have : lam = 0 := by exact_mod_cast h2
        omega
    · rw [h1, zero_pow (by omega)]; ring
  · have hlam : (0 : ℝ) < lam := by
      have : 0 < lam := by omega
      exact_mod_cast this
    rw [Pord_vanish _ hlθ, mul_zero]
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    linarith

lemma bterm_nonneg (α : ℝ) (lam θ : ℕ) {π : ℝ} (h0 : 0 ≤ π) (h1 : π ≤ 1) (l : ℕ) :
    0 ≤ bterm α lam θ π l := by
  unfold bterm
  have := Pord_nonneg (1 / (α * lam)) θ l h0
  have : 0 ≤ 1 - π := by linarith
  positivity

lemma sum_bterm_le (α : ℝ) (lam θ : ℕ) {π : ℝ} (h0 : 0 ≤ π) (h1 : π ≤ 1) :
    ∑ l ∈ Finset.range (lam + 1), bterm α lam θ π l ≤ 1 := by
  have hb : ∑ l ∈ Finset.range (lam + 1), (lam.choose l : ℝ) * π ^ l * (1 - π) ^ (lam - l) = 1 := by
    have := add_pow π (1 - π) lam
    rw [add_sub_cancel, one_pow] at this
    refine Eq.trans ?_ this.symm; apply Finset.sum_congr rfl; intro l _; ring
  rw [← hb]
  apply Finset.sum_le_sum
  intro l _
  unfold bterm
  have := Pord_le_one (1 / (α * lam)) θ l h0
  have : 0 ≤ (lam.choose l : ℝ) * π ^ l * (1 - π) ^ (lam - l) := by
    have : 0 ≤ 1 - π := by linarith
    positivity
  nlinarith

lemma Balpha_bounds (α : ℝ) (hα : 0 < α) (lam θ : ℕ) {π : ℝ} (h0 : 0 ≤ π) (h1 : π ≤ 1) :
    0 ≤ Balpha α lam θ π ∧ Balpha α lam θ π ≤ 1 := by
  by_cases hθ : θ = 0
  · simp [Balpha, hθ]
  · rw [Balpha_eq α hα lam θ hθ h0]
    have := sum_bterm_le α lam θ h0 h1
    have := Finset.sum_nonneg (fun l (_ : l ∈ Finset.range (lam + 1)) => bterm_nonneg α lam θ h0 h1 l)
    constructor <;> linarith

lemma Balpha_cont (α : ℝ) (hα : 0 < α) (lam θ : ℕ) :
    ContinuousOn (Balpha α lam θ) (Set.Icc 0 1) := by
  by_cases hθ : θ = 0
  · have : Balpha α lam θ = fun _ => 1 := by funext π; simp [Balpha, hθ]
    rw [this]; exact continuousOn_const
  · have hc : ContinuousOn (fun π : ℝ => 1 - ∑ l ∈ Finset.range (lam + 1),
        (lam.choose l : ℝ) * (1 - π) ^ (lam - l) * (π ^ l * Pord (1 / (α * lam)) θ l π))
        (Set.Icc 0 1) := by
      apply continuousOn_const.sub
      apply continuousOn_finsetSum
      intro l _
      exact (continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow _)).mul
        ((Q_cont _ θ l).mono Set.Icc_subset_Ici_self)
    refine hc.congr ?_
    intro π hπ
    rw [Balpha_eq α hα lam θ hθ hπ.1]
    congr 1; apply Finset.sum_congr rfl; intro l _; unfold bterm; ring

lemma Jalpha_cont (mu : ℕ × ℕ → ℝ) (α : ℝ) (hα : 0 < α) (hmu0 : ∀ p, 0 ≤ mu p)
    (hsum : Summable fun p : ℕ × ℕ => (p.1 : ℝ) * mu p) (hlb : 0 < lbar mu) :
    ContinuousOn (Jalpha mu α) (Set.Icc 0 1) := by
  unfold Jalpha
  refine continuousOn_tsum (u := fun p : ℕ × ℕ => (p.1 : ℝ) * mu p / lbar mu) ?_
    (hsum.div_const _) ?_
  · intro p
    exact continuousOn_const.mul (Balpha_cont α hα p.1 p.2)
  · intro p x hx
    obtain ⟨b0, b1⟩ := Balpha_bounds α hα p.1 p.2 hx.1 hx.2
    have hw : 0 ≤ (p.1 : ℝ) * mu p / lbar mu := by
      have := hmu0 p; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw b0)]
    nlinarith

lemma Jalpha_nonneg (mu : ℕ × ℕ → ℝ) (α : ℝ) (hα : 0 < α) (hmu0 : ∀ p, 0 ≤ mu p)
    (hlb : 0 < lbar mu) {π : ℝ} (h0 : 0 ≤ π) (h1 : π ≤ 1) : 0 ≤ Jalpha mu α π := by
  unfold Jalpha
  apply tsum_nonneg
  intro p
  have := hmu0 p
  have := (Balpha_bounds α hα p.1 p.2 h0 h1).1
  positivity

end CGAux

namespace CGAux
open MeasureTheory ContagionGrowth.FluidLimit
open scoped Pointwise

lemma box_A_smul (c : ℝ) (θ l : ℕ) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    box l (r * s) ∩ Aset (r * c) θ l = r • (box l s ∩ Aset c θ l) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne']
  have key : ∀ y z : ℝ, r⁻¹ * y ≤ z ↔ y ≤ r * z := fun y z => inv_mul_le_iff₀ hr
  have key0 : ∀ y : ℝ, 0 ≤ r⁻¹ * y ↔ 0 ≤ y := fun y => by
    constructor
    · intro h; have := mul_le_mul_of_nonneg_left h hr.le
      rwa [mul_zero, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at this
    · intro h; exact mul_nonneg (inv_nonneg.mpr hr.le) h
  simp only [Set.mem_inter_iff, box, Aset, Set.mem_setOf_eq, Set.mem_Icc, Pi.smul_apply,
    smul_eq_mul, key, key0, mul_assoc]

lemma V_scale (c : ℝ) (θ l : ℕ) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    V (r * c) θ l (r * s) = r ^ l * V c θ l s := by
  unfold V
  rw [box_A_smul c θ l hr s, measureReal_def, Measure.addHaar_smul, measureReal_def,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin, abs_of_pos (pow_pos hr l)]

lemma Pord_scale (c : ℝ) (θ l : ℕ) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    Pord (r * c) θ l (r * s) = Pord c θ l s := by
  rcases le_or_gt l θ with h | h
  · rw [Pord_le _ h, Pord_le _ h]
  · rw [Pord_lt _ h, Pord_lt _ h, V_scale c θ l hr s, mul_pow,
      mul_div_mul_left _ _ (pow_ne_zero l hr.ne')]

lemma sClosed_eq (m lb α : ℝ) (hlb : 0 < lb) (lam θ l : ℕ) (t : ℝ) :
    sClosed m lb α lam θ l t = m * bterm α lam θ (t / lb) l := by
  unfold sClosed bterm
  have h1 : lb / (α * lam) = lb * (1 / (α * lam)) := by ring
  have h2 : t = lb * (t / lb) := by field_simp
  rw [h1]
  conv_lhs => rw [h2]
  rw [Pord_scale _ θ l hlb, ← h2]
  ring

lemma part1 (mu : ℕ × ℕ → ℝ) (α : ℝ) (hα : 0 < α) (hlb : 0 < lbar mu) (lam θ : ℕ)
    (hθ : 0 < θ) {t : ℝ} (ht : 0 ≤ t) :
    mu (lam, θ) - ∑ l ∈ Finset.range (lam + 1), sClosed (mu (lam, θ)) (lbar mu) α lam θ l t =
      mu (lam, θ) * Balpha α lam θ (t / lbar mu) := by
  rw [Balpha_eq α hα lam θ hθ.ne' (div_nonneg ht hlb.le)]
  simp only [sClosed_eq _ _ _ hlb]
  rw [← Finset.mul_sum]; ring

lemma delta_eq (mu : ℕ × ℕ → ℝ) (α : ℝ) (hα : 0 < α) (hlb : 0 < lbar mu) (lam θ : ℕ)
    {t : ℝ} (ht : 0 ≤ t) : delta mu α lam θ t = mu (lam, θ) * Balpha α lam θ (t / lbar mu) := by
  unfold delta
  by_cases hθ : θ = 0
  · subst hθ; simp [Balpha]
  · rw [if_neg hθ]; exact part1 mu α hα hlb lam θ (Nat.pos_of_ne_zero hθ) ht

end CGAux

open CGAux ContagionGrowth.FluidLimit in
theorem solution (mu : ℕ × ℕ → ℝ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (hmu0 : ∀ p, 0 ≤ mu p)
    (hmu1 : HasSum mu 1) (hsum : Summable fun p : ℕ × ℕ => (p.1 : ℝ) * mu p)
    (hlb : 0 < lbar mu) :
    (∀ lam θ : ℕ, 0 < θ → θ ≤ lam → ∀ t ∈ Set.Ico 0 (lbar mu),
      mu (lam, θ) - ∑ l ∈ Finset.range (lam + 1), sClosed (mu (lam, θ)) (lbar mu) α lam θ l t =
        mu (lam, θ) * Balpha α lam θ (t / lbar mu)) ∧
    ∀ t ∈ Set.Ico 0 (lbar mu),
      ∑' p : ℕ × ℕ, (p.1 : ℝ) * delta mu α p.1 p.2 t - t =
        lbar mu * (Jalpha mu α (t / lbar mu) - t / lbar mu) := by
  refine ⟨fun lam θ hθ _ t ht => part1 mu α hα hlb lam θ hθ ht.1, fun t ht => ?_⟩
  have h1 : ∀ p : ℕ × ℕ, (p.1 : ℝ) * delta mu α p.1 p.2 t =
      lbar mu * ((p.1 : ℝ) * mu p / lbar mu * Balpha α p.1 p.2 (t / lbar mu)) := by
    intro p
    rw [delta_eq mu α hα hlb p.1 p.2 ht.1]
    field_simp
  simp only [h1]
  rw [tsum_mul_left]
  unfold Jalpha
  field_simp
