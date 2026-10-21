-- Prove2me | solution 1 for ContagionGrowth.FluidLimit.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T19:35:59.59901+00:00
-- url     : https://prove2.me/submissions/4dd9391a-0dba-4ead-a053-84fa3320a731

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

lemma meas_card_lt {ι : Type*} [Fintype ι] (s : ℝ) (u : ℕ) (R : Finset ι) :
    MeasurableSet {x : ι → ℝ | (R.filter (fun i => x i ≤ s)).card < u} := by
  have hf : Measurable (fun x : ι → ℝ => (R.filter (fun i => x i ≤ s)).card) := by
    have : (fun x : ι → ℝ => (R.filter (fun i => x i ≤ s)).card) =
        fun x => ∑ i ∈ R, if x i ≤ s then 1 else 0 := by funext x; rw [Finset.card_filter]
    rw [this]
    apply Finset.measurable_sum
    intro i _
    exact Measurable.ite (measurableSet_le (measurable_pi_apply i) measurable_const)
      measurable_const measurable_const
  exact hf (Set.to_countable {m : ℕ | m < u}).measurableSet

lemma Aset_meas (c : ℝ) (θ l : ℕ) : MeasurableSet (Aset c θ l) := by
  unfold Aset
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun u => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
    meas_card_lt _ _ _

/-- the piece of the decomposition indexed by the set `R` of coordinates below `T` -/
def Epiece (c : ℝ) (θ n : ℕ) (T t : ℝ) (R : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {x | (∀ i ∈ R, x i ∈ Set.Icc 0 T) ∧ (∀ i ∉ R, x i ∈ Set.Ioc T t) ∧
    ∀ u : ℕ, θ + 1 ≤ u → u ≤ R.card → (R.filter (fun i => x i ≤ c * ((u : ℝ) - θ))).card < u}

lemma Epiece_R {c : ℝ} {θ n : ℕ} {T t : ℝ} {R : Finset (Fin n)} {x : Fin n → ℝ}
    (hx : x ∈ Epiece c θ n T t R) : R = Finset.univ.filter (fun i => x i ≤ T) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi; exact (hx.1 i hi).2
  · intro hi; by_contra hn; exact absurd (hx.2.1 i hn).1 (not_lt.mpr hi)

lemma union_eq (c : ℝ) (θ n : ℕ) {T t : ℝ} (hT : 0 ≤ T) (hTt : T ≤ t)
    (hc : ∀ u : ℕ, θ + 1 ≤ u → u ≤ n → c * ((u : ℝ) - θ) ≤ T) :
    box n t ∩ Aset c θ n = ⋃ R : Finset (Fin n), Epiece c θ n T t R := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨hb, hA⟩
    set R := Finset.univ.filter (fun i => x i ≤ T) with hR
    refine ⟨R, ?_, ?_, ?_⟩
    · intro i hi
      simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact ⟨(hb i).1, hi⟩
    · intro i hi
      simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
      exact ⟨hi, (hb i).2⟩
    · intro u hu1 hu2
      have hun : u ≤ n := hu2.trans (by simpa using Finset.card_le_univ R)
      have := hA u hu1 hun
      have heq : R.filter (fun i => x i ≤ c * ((u : ℝ) - θ)) =
          Finset.univ.filter (fun i => x i ≤ c * ((u : ℝ) - θ)) := by
        ext i
        simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; exact h.2
        · intro h; exact ⟨h.trans (hc u hu1 hun), h⟩
      rw [heq]; exact this
  · rintro ⟨R, hx⟩
    have hRx := Epiece_R hx
    refine ⟨fun i => ?_, fun u hu1 hu2 => ?_⟩
    · by_cases hi : i ∈ R
      · exact ⟨(hx.1 i hi).1, (hx.1 i hi).2.trans hTt⟩
      · exact ⟨hT.trans (hx.2.1 i hi).1.le, (hx.2.1 i hi).2⟩
    · have heq : Finset.univ.filter (fun i => x i ≤ c * ((u : ℝ) - θ)) =
          R.filter (fun i => x i ≤ c * ((u : ℝ) - θ)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; refine ⟨?_, h⟩
          rw [hRx]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact h.trans (hc u hu1 hu2)
        · intro h; exact h.2
      rw [heq]
      by_cases hu : u ≤ R.card
      · exact hx.2.2 u hu1 hu
      · exact lt_of_le_of_lt (Finset.card_filter_le _ _) (not_le.mp hu)

lemma Epiece_disj (c : ℝ) (θ n : ℕ) (T t : ℝ) :
    Pairwise (Function.onFun Disjoint (Epiece c θ n T t)) := by
  intro R R' hne
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  exact hne ((Epiece_R hx).trans (Epiece_R hx').symm)

lemma card_sub {n : ℕ} (R : Finset (Fin n)) (q : Fin n → Prop) [DecidablePred q] :
    (Finset.univ.filter (fun i : {i // i ∈ R} => q i)).card = (R.filter q).card := by
  apply Finset.card_bij (fun a _ => a.1)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ⟨a.2, ha⟩
  · intro a _ b _ h; exact Subtype.ext h
  · intro b hb
    simp only [Finset.mem_filter] at hb
    exact ⟨⟨b, hb.1⟩, by simp [hb.2], rfl⟩

/-- the `R`-part of a piece, as a set of functions on the subtype -/
def A1 (c : ℝ) (θ : ℕ) (T : ℝ) {n : ℕ} (R : Finset (Fin n)) : Set ({i // i ∈ R} → ℝ) :=
  {y | (∀ i, y i ∈ Set.Icc 0 T) ∧ ∀ u : ℕ, θ + 1 ≤ u → u ≤ R.card →
    (Finset.univ.filter (fun i => y i ≤ c * ((u : ℝ) - θ))).card < u}

lemma A1_vol (c : ℝ) (θ : ℕ) (T : ℝ) {n : ℕ} (R : Finset (Fin n)) :
    volume (A1 c θ T R) = volume (box R.card T ∩ Aset c θ R.card) := by
  set σ : Fin R.card ≃ {i // i ∈ R} := R.equivFin.symm
  have hp := volume_preserving_arrowCongr' σ (MeasurableEquiv.refl ℝ) (MeasurePreserving.id volume)
  rw [← hp.measure_preimage_equiv]
  congr 1
  ext x
  have happ : ∀ i, (MeasurableEquiv.arrowCongr' σ (MeasurableEquiv.refl ℝ) x) i = x (σ.symm i) := by
    intro i; rfl
  simp only [Set.mem_preimage, A1, Set.mem_setOf_eq, happ, Set.mem_inter_iff, box, Aset]
  have hcard : ∀ s : ℝ, (Finset.univ.filter (fun i : {i // i ∈ R} => x (σ.symm i) ≤ s)).card =
      (Finset.univ.filter (fun j : Fin R.card => x j ≤ s)).card := by
    intro s
    apply Finset.card_equiv σ.symm
    intro i; simp
  simp only [hcard]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun j => by simpa using h1 (σ j), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => h1 _, h2⟩

lemma Epiece_vol (c : ℝ) (θ n : ℕ) (T t : ℝ) (R : Finset (Fin n)) :
    volume (Epiece c θ n T t R) =
      volume (box R.card T ∩ Aset c θ R.card) * ENNReal.ofReal (t - T) ^ (n - R.card) := by
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (· ∈ R)
  have hp := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (· ∈ R)
  set B1 : Set ({i // i ∉ R} → ℝ) := Set.univ.pi (fun _ => Set.Ioc T t)
  have hpre : Epiece c θ n T t R = e ⁻¹' (A1 c θ T R ×ˢ B1) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Epiece, A1, B1, Set.mem_setOf_eq, Set.mem_pi,
      Set.mem_univ, true_implies]
    have h1 : ∀ i : {i // i ∈ R}, (e x).1 i = x i := fun i => rfl
    have h2 : ∀ i : {i // i ∉ R}, (e x).2 i = x i := fun i => rfl
    simp only [h1, h2]
    have hcard : ∀ s : ℝ, (Finset.univ.filter (fun i : {i // i ∈ R} => x i ≤ s)).card =
        (R.filter (fun i => x i ≤ s)).card := fun s => card_sub R (fun i => x i ≤ s)
    simp only [hcard]
    constructor
    · rintro ⟨ha, hb, hc⟩
      exact ⟨⟨fun i => ha i i.2, hc⟩, fun i => hb i i.2⟩
    · rintro ⟨⟨ha, hc⟩, hb⟩
      exact ⟨fun i hi => ha ⟨i, hi⟩, fun i hi => hb ⟨i, hi⟩, hc⟩
  rw [hpre, hp.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod]
  congr 1
  · convert A1_vol c θ T R
  rw [volume_pi_pi]
  simp only [Real.volume_Ioc, Finset.prod_const, Finset.card_univ]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]

lemma meas_coord {n : ℕ} (i : Fin n) (S : Set ℝ) (hS : MeasurableSet S) :
    MeasurableSet {x : Fin n → ℝ | x i ∈ S} := measurable_pi_apply i hS

lemma Epiece_meas (c : ℝ) (θ n : ℕ) (T t : ℝ) (R : Finset (Fin n)) :
    MeasurableSet (Epiece c θ n T t R) := by
  have h1 : MeasurableSet {x : Fin n → ℝ | ∀ i ∈ R, x i ∈ Set.Icc 0 T} := by
    have : {x : Fin n → ℝ | ∀ i ∈ R, x i ∈ Set.Icc 0 T} =
        ⋂ i ∈ R, {x : Fin n → ℝ | x i ∈ Set.Icc 0 T} := by ext; simp
    rw [this]; exact Finset.measurableSet_biInter R (fun i _ => meas_coord i _ measurableSet_Icc)
  have h2 : MeasurableSet {x : Fin n → ℝ | ∀ i ∉ R, x i ∈ Set.Ioc T t} := by
    have : {x : Fin n → ℝ | ∀ i ∉ R, x i ∈ Set.Ioc T t} =
        ⋂ i ∈ Rᶜ, {x : Fin n → ℝ | x i ∈ Set.Ioc T t} := by ext; simp
    rw [this]; exact Finset.measurableSet_biInter _ (fun i _ => meas_coord i _ measurableSet_Ioc)
  have h3 : MeasurableSet {x : Fin n → ℝ | ∀ u : ℕ, θ + 1 ≤ u → u ≤ R.card →
      (R.filter (fun i => x i ≤ c * ((u : ℝ) - θ))).card < u} := by
    have : {x : Fin n → ℝ | ∀ u : ℕ, θ + 1 ≤ u → u ≤ R.card →
        (R.filter (fun i => x i ≤ c * ((u : ℝ) - θ))).card < u} =
        ⋂ u ∈ Finset.Icc (θ + 1) R.card, {x : Fin n → ℝ |
          (R.filter (fun i => x i ≤ c * ((u : ℝ) - θ))).card < u} := by
      ext; simp [and_imp]
    rw [this]; exact Finset.measurableSet_biInter _ (fun u _ => meas_card_lt _ _ _)
  exact h1.inter (h2.inter h3)

lemma decomp (c : ℝ) (θ n : ℕ) {T t : ℝ} (hT : 0 ≤ T) (hTt : T ≤ t)
    (hc : ∀ u : ℕ, θ + 1 ≤ u → u ≤ n → c * ((u : ℝ) - θ) ≤ T) :
    V c θ n t = ∑ r ∈ Finset.range (n + 1), (n.choose r : ℝ) * (t - T) ^ (n - r) * V c θ r T := by
  have hfin : ∀ R, volume (Epiece c θ n T t R) ≠ ⊤ := by
    intro R; rw [Epiece_vol]
    exact ENNReal.mul_ne_top (measure_ne_top_of_subset Set.inter_subset_left (box_ne_top _ _))
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  rw [V, union_eq c θ n hT hTt hc, measureReal_def,
    measure_iUnion (Epiece_disj c θ n T t) (Epiece_meas c θ n T t), tsum_fintype,
    ENNReal.toReal_sum (fun R _ => hfin R)]
  have hterm : ∀ R : Finset (Fin n), (volume (Epiece c θ n T t R)).toReal =
      (fun m => (t - T) ^ (n - m) * V c θ m T) R.card := by
    intro R
    rw [Epiece_vol, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith)]
    simp only [V, measureReal_def]; ring
  simp only [hterm]
  have hpc := Finset.sum_powerset_apply_card (fun m => (t - T) ^ (n - m) * V c θ m T)
    (x := (Finset.univ : Finset (Fin n)))
  simp only [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at hpc
  rw [hpc]
  apply Finset.sum_congr rfl
  intro r _
  rw [nsmul_eq_mul]; ring

end CGAux

namespace CGAux
open MeasureTheory ContagionGrowth.FluidLimit

lemma V_vanish (c : ℝ) {θ l : ℕ} (h : θ < l) {π : ℝ} (hle : π ≤ c * ((l : ℝ) - θ)) :
    V c θ l π = 0 := by
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
  rw [V, this, measureReal_empty]

lemma V_low (c : ℝ) {θ r : ℕ} (h : r ≤ θ) {T : ℝ} (hT : 0 ≤ T) : V c θ r T = T ^ r := by
  have : Aset c θ r = Set.univ := by
    ext x; simp only [Aset, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro u hu1 hu2; omega
  rw [V, this, Set.inter_univ, box_real r hT]

lemma QV (c : ℝ) (θ r : ℕ) {T : ℝ} (hT : 0 ≤ T) : T ^ r * Pord c θ r T = V c θ r T := by
  rcases le_or_gt r θ with h | h
  · rw [Pord_le c h, mul_one, V_low c h hT]
  · exact Q_eq c h hT

lemma tHat_gt (lb α : ℝ) (lam θ l : ℕ) (hl : θ < l) :
    tHat lb α lam θ l = lb / (α * lam) * ((l : ℝ) - θ) := by
  unfold tHat; rw [if_neg (not_le.mpr hl)]; ring

end CGAux

open CGAux ContagionGrowth.FluidLimit in
theorem solution (α lb t : ℝ) (lam θ l : ℕ) (hα : 0 < α) (hα1 : α < 1)
    (hlb : 0 < lb) (hlam : 1 ≤ lam) (hl : θ + 1 ≤ l) (hlam_l : l ≤ lam)
    (ht : tHat lb α lam θ l ≤ t) :
    Pord (lb / (α * lam)) θ l t =
      1 / t ^ l * ∑ r ∈ Finset.range l, (l.choose r : ℝ) * (t - tHat lb α lam θ l) ^ (l - r) *
        tHat lb α lam θ l ^ r * Pord (lb / (α * lam)) θ r (tHat lb α lam θ l) := by
  have hθl : θ < l := by omega
  set c := lb / (α * lam) with hcdef
  have hlamr : (0 : ℝ) < lam := by have : 0 < lam := by omega
                                   exact_mod_cast this
  have hc0 : 0 ≤ c := by positivity
  set T := tHat lb α lam θ l with hTdef
  have hTc : T = c * ((l : ℝ) - θ) := tHat_gt lb α lam θ l hθl
  have hlθ : (0 : ℝ) < (l : ℝ) - θ := by
    have : (θ : ℝ) < l := by exact_mod_cast hθl
    linarith
  have hT : 0 < T := by rw [hTc]; positivity
  have ht0 : 0 < t := lt_of_lt_of_le hT ht
  have hcu : ∀ u : ℕ, θ + 1 ≤ u → u ≤ l → c * ((u : ℝ) - θ) ≤ T := by
    intro u _ hu
    rw [hTc]
    apply mul_le_mul_of_nonneg_left _ hc0
    have : (u : ℝ) ≤ l := by exact_mod_cast hu
    linarith
  have hD := decomp c θ l hT.le ht hcu
  rw [Finset.sum_range_succ, V_vanish c hθl hTc.le, mul_zero, add_zero] at hD
  rw [Pord_lt c hθl, hD, div_eq_mul_inv, mul_comm, one_div]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [mul_assoc _ (T ^ r), QV c θ r hT.le]
