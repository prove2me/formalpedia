-- Prove2me | solution 1 for ContagionGrowth.FluidLimit.remark_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T19:19:44.502151+00:00
-- url     : https://prove2.me/submissions/f5e1ac60-915c-4de9-b167-8946fbe1305b

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

open CGAux ContagionGrowth.FluidLimit in
theorem solution (mu : ℕ × ℕ → ℝ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (hmu0 : ∀ p, 0 ≤ mu p)
    (hmu1 : HasSum mu 1) (hsum : Summable fun p : ℕ × ℕ => (p.1 : ℝ) * mu p)
    (hlb : 0 < lbar mu) :
    0 ≤ Jalpha mu α 0 ∧ Jalpha mu α 1 ≤ 1 ∧
    IsLeast {π : ℝ | π ∈ Set.Icc (0 : ℝ) 1 ∧ Jalpha mu α π ≤ π} (piStar mu α) ∧
    (ContinuousOn (Jalpha mu α) (Set.Ico 0 1) → Jalpha mu α (piStar mu α) = piStar mu α) := by
  have hJc := Jalpha_cont mu α hα hmu0 hsum hlb
  have hJ0 : 0 ≤ Jalpha mu α 0 := Jalpha_nonneg mu α hα hmu0 hlb le_rfl zero_le_one
  have hJ1 : Jalpha mu α 1 ≤ 1 := by
    unfold Jalpha
    have hs : Summable fun p : ℕ × ℕ => (p.1 : ℝ) * mu p / lbar mu := hsum.div_const _
    have hle : ∀ p : ℕ × ℕ, (p.1 : ℝ) * mu p / lbar mu * Balpha α p.1 p.2 1 ≤
        (p.1 : ℝ) * mu p / lbar mu := by
      intro p
      obtain ⟨b0, b1⟩ := Balpha_bounds α hα p.1 p.2 zero_le_one le_rfl
      have hw : 0 ≤ (p.1 : ℝ) * mu p / lbar mu := by have := hmu0 p; positivity
      nlinarith
    have hs2 : Summable fun p : ℕ × ℕ => (p.1 : ℝ) * mu p / lbar mu * Balpha α p.1 p.2 1 := by
      refine Summable.of_nonneg_of_le (fun p => ?_) hle hs
      have := (Balpha_bounds α hα p.1 p.2 zero_le_one le_rfl).1
      have := hmu0 p; positivity
    calc (∑' p : ℕ × ℕ, (p.1 : ℝ) * mu p / lbar mu * Balpha α p.1 p.2 1)
        ≤ ∑' p : ℕ × ℕ, (p.1 : ℝ) * mu p / lbar mu := hs2.tsum_le_tsum hle hs
      _ = 1 := by rw [tsum_div_const]; exact div_self hlb.ne'
  set S := {π : ℝ | π ∈ Set.Icc (0 : ℝ) 1 ∧ Jalpha mu α π ≤ π} with hS
  have hSc : IsClosed S := by
    have : S = Set.Icc (0:ℝ) 1 ∩ (fun π => Jalpha mu α π - π) ⁻¹' Set.Iic 0 := by
      ext π; simp [S, sub_nonpos]
    rw [this]
    exact (hJc.sub continuousOn_id).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := ⟨1, ⟨⟨zero_le_one, le_rfl⟩, hJ1⟩⟩
  have hSbdd : BddBelow S := ⟨0, fun x hx => hx.1.1⟩
  have hmem : piStar mu α ∈ S := hSc.csInf_mem hSne hSbdd
  have hleast : IsLeast S (piStar mu α) := ⟨hmem, fun x hx => csInf_le hSbdd hx⟩
  refine ⟨hJ0, hJ1, hleast, fun _ => ?_⟩
  apply le_antisymm hmem.2
  set p := piStar mu α
  have hp0 : 0 ≤ p := hmem.1.1
  have hp1 : p ≤ 1 := hmem.1.2
  rcases hp0.lt_or_eq with hpos | hzero
  · set T := {π : ℝ | π ∈ Set.Icc (0 : ℝ) 1 ∧ π ≤ Jalpha mu α π}
    have hTc : IsClosed T := by
      have : T = Set.Icc (0:ℝ) 1 ∩ (fun π => π - Jalpha mu α π) ⁻¹' Set.Iic 0 := by
        ext π; simp [T, sub_nonpos]
      rw [this]
      exact (continuousOn_id.sub hJc).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hsub : Set.Ico 0 p ⊆ T := by
      intro x hx
      have hx1 : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
      refine ⟨hx1, ?_⟩
      by_contra hc
      push_neg at hc
      have := hleast.2 ⟨hx1, hc.le⟩
      linarith [hx.2]
    have hcl : Set.Icc 0 p ⊆ T := by
      rw [← closure_Ico hpos.ne]; exact hTc.closure_subset_iff.mpr hsub
    exact (hcl ⟨hp0, le_rfl⟩).2
  · rw [← hzero]; exact hJ0
