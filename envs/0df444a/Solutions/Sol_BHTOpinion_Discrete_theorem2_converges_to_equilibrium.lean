-- Prove2me | solution 1 for BHTOpinion.Discrete.theorem2_converges_to_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T06:35:38.4387+00:00
-- url     : https://prove2.me/submissions/a43c813b-d34f-4f9f-9595-436e9b1f033a

import Mathlib
import Definitions.Def_BHTOpinion_Discrete_Model

open Filter Topology

set_option autoImplicit false

namespace BHTAux9b

open BHTOpinion.Discrete

/-- the antisymmetric pair term -/
noncomputable def pt {n : ℕ} (y : Fin n → ℝ) (k l : Fin n) : ℝ :=
  if |y k - y l| < 1 then y l - y k else 0

lemma pt_anti {n : ℕ} (y : Fin n → ℝ) (k l : Fin n) : pt y k l = - pt y l k := by
  unfold pt
  rw [abs_sub_comm (y l) (y k)]
  split_ifs <;> ring

lemma anti_zero {n : ℕ} (D : Finset (Fin n)) (g : Fin n → Fin n → ℝ)
    (h : ∀ a b, g a b = - g b a) : ∑ a ∈ D, ∑ b ∈ D, g a b = 0 := by
  have h1 : ∑ a ∈ D, ∑ b ∈ D, g a b = ∑ a ∈ D, ∑ b ∈ D, g b a := Finset.sum_comm
  have h2 : ∑ a ∈ D, ∑ b ∈ D, g b a = - ∑ a ∈ D, ∑ b ∈ D, g a b := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [h b a]
  linarith

lemma rhs_eq {n : ℕ} (y : Fin n → ℝ) (k : Fin n) : rhs y k = ∑ l, pt y k l := by
  unfold rhs pt
  rw [Finset.sum_filter]

lemma sum_rhs_eq {n : ℕ} (y : Fin n → ℝ) (D : Finset (Fin n)) :
    ∑ k ∈ D, rhs y k = ∑ k ∈ D, ∑ l ∈ Dᶜ, pt y k l := by
  have : ∀ k, rhs y k = ∑ l ∈ D, pt y k l + ∑ l ∈ Dᶜ, pt y k l := by
    intro k
    rw [rhs_eq, Finset.sum_add_sum_compl]
  simp_rw [this, Finset.sum_add_distrib, anti_zero D (pt y) (pt_anti y), zero_add]

/-- Down-set condition at time 0 -/
def Down {n : ℕ} (x : ℝ → Fin n → ℝ) (D : Finset (Fin n)) : Prop :=
  ∀ k ∈ D, ∀ l ∉ D, x 0 k ≤ x 0 l

lemma order_pres {n : ℕ} {x : ℝ → Fin n → ℝ} (hx : IsProperSolution x) (k l : Fin n)
    (h0 : x 0 k ≤ x 0 l) (t : ℝ) (ht : 0 ≤ t) : x t k ≤ x t l := by
  by_contra hc
  push_neg at hc
  have hcont : ContinuousOn (fun s => x s l - x s k) (Set.Icc 0 t) := by
    have hc0 : ContinuousOn x (Set.Icc 0 t) := hx.1.1.mono Set.Icc_subset_Ici_self
    exact ((continuous_apply l).comp_continuousOn hc0).sub
      ((continuous_apply k).comp_continuousOn hc0)
  have hmem : (0 : ℝ) ∈ Set.Icc (x t l - x t k) (x 0 l - x 0 k) := ⟨by linarith, by linarith⟩
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht hcont hmem
  have heq : x s l = x s k := by simp only at hs0; linarith
  have := hx.2.2.2 l k s hs.1 heq t hs.2
  linarith

lemma pt_nonneg {n : ℕ} {x : ℝ → Fin n → ℝ} (hx : IsProperSolution x) (D : Finset (Fin n))
    (hD : Down x D) (τ : ℝ) (hτ : 0 ≤ τ) (k : Fin n) (hk : k ∈ D) (l : Fin n) (hl : l ∈ Dᶜ) :
    0 ≤ pt (x τ) k l := by
  unfold pt
  split_ifs
  · have := order_pres hx k l (hD k hk l (Finset.mem_compl.mp hl)) τ hτ
    linarith
  · exact le_refl _

lemma sum_rhs_nonneg {n : ℕ} {x : ℝ → Fin n → ℝ} (hx : IsProperSolution x) (D : Finset (Fin n))
    (hD : Down x D) (τ : ℝ) (hτ : 0 ≤ τ) : 0 ≤ ∑ k ∈ D, rhs (x τ) k := by
  rw [sum_rhs_eq]
  exact Finset.sum_nonneg (fun k hk => Finset.sum_nonneg (fun l hl => pt_nonneg hx D hD τ hτ k hk l hl))

lemma iint {n : ℕ} {x : ℝ → Fin n → ℝ} (hx : IsSolution x) (k : Fin n) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IntervalIntegrable (fun τ => rhs (x τ) k) MeasureTheory.volume s t :=
  (hx.2.1 s hs k).symm.trans (hx.2.1 t ht k)

lemma diff_eq {n : ℕ} {x : ℝ → Fin n → ℝ} (hx : IsSolution x) (k : Fin n) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) : x t k - x s k = ∫ τ in s..t, rhs (x τ) k := by
  have e1 := hx.2.2 t ht k
  have e2 := hx.2.2 s hs k
  have e3 := intervalIntegral.integral_interval_sub_left (hx.2.1 t ht k) (hx.2.1 s hs k)
  linarith

lemma sum_diff_eq {n : ℕ} {x : ℝ → Fin n → ℝ} (hx : IsSolution x) (D : Finset (Fin n)) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∑ k ∈ D, x t k - ∑ k ∈ D, x s k = ∫ τ in s..t, ∑ k ∈ D, rhs (x τ) k := by
  rw [intervalIntegral.integral_finsetSum (fun k _ => iint hx k hs ht), ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun k _ => diff_eq hx k hs ht)

lemma sum_mono {n : ℕ} {x : ℝ → Fin n → ℝ} (hx : IsProperSolution x) (D : Finset (Fin n))
    (hD : Down x D) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∑ k ∈ D, x s k ≤ ∑ k ∈ D, x t k := by
  have e := sum_diff_eq hx.1 D hs (le_trans hs hst)
  have : 0 ≤ ∫ τ in s..t, ∑ k ∈ D, rhs (x τ) k :=
    intervalIntegral.integral_nonneg hst (fun u hu => sum_rhs_nonneg hx D hD u (le_trans hs hu.1))
  linarith

/-- uniform upper bound -/
lemma upper {n : ℕ} {x : ℝ → Fin n → ℝ} (hx : IsProperSolution x) (k : Fin n) (t : ℝ)
    (ht : 0 ≤ t) : x t k ≤ ∑ m, |x 0 m| := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun m => x 0 m) ⟨k, Finset.mem_univ k⟩
  have h1 : x t k ≤ x t j := order_pres hx k j (hj k (Finset.mem_univ k)) t ht
  have h2 : x t j - x 0 j ≤ 0 := by
    rw [diff_eq hx.1 j (le_refl 0) ht]
    have : 0 ≤ ∫ τ in (0:ℝ)..t, - rhs (x τ) j := by
      apply intervalIntegral.integral_nonneg ht
      intro u hu
      rw [rhs_eq, ← Finset.sum_neg_distrib]
      apply Finset.sum_nonneg
      intro l _
      unfold pt
      split_ifs
      · have := order_pres hx l j (hj l (Finset.mem_univ l)) u hu.1
        linarith
      · simp
    rw [intervalIntegral.integral_neg] at this
    linarith
  have h3 : x 0 j ≤ ∑ m, |x 0 m| :=
    le_trans (le_abs_self _) (Finset.single_le_sum (f := fun m => |x 0 m|)
      (fun m _ => abs_nonneg _) (Finset.mem_univ j))
  linarith

lemma sum_upper {n : ℕ} {x : ℝ → Fin n → ℝ} (hx : IsProperSolution x) (D : Finset (Fin n))
    (t : ℝ) (ht : 0 ≤ t) : ∑ k ∈ D, x t k ≤ D.card * ∑ m, |x 0 m| := by
  have := Finset.sum_le_sum (s := D) (fun k _ => upper hx k t ht)
  simpa using this

lemma sum_conv {n : ℕ} {x : ℝ → Fin n → ℝ} (hx : IsProperSolution x) (D : Finset (Fin n))
    (hD : Down x D) : ∃ a, Tendsto (fun t => ∑ k ∈ D, x t k) atTop (𝓝 a) := by
  set g : ℝ → ℝ := fun t => ∑ k ∈ D, x (max t 0) k with hg
  have hmono : Monotone g := by
    intro s t hst
    exact sum_mono hx D hD (le_max_right s 0) (max_le_max hst (le_refl 0))
  have hbdd : BddAbove (Set.range g) := by
    refine ⟨D.card * ∑ m, |x 0 m|, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact sum_upper hx D _ (le_max_right t 0)
  refine ⟨⨆ t, g t, (tendsto_atTop_ciSup hmono hbdd).congr' ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp [hg, max_eq_left ht]

lemma coord_conv {n : ℕ} {x : ℝ → Fin n → ℝ} (hx : IsProperSolution x) (i : Fin n) :
    ∃ a, Tendsto (fun t => x t i) atTop (𝓝 a) := by
  set L := Finset.univ.filter (fun k => x 0 k ≤ x 0 i) with hL
  have hiL : i ∈ L := by simp [hL]
  have hD1 : Down x L := by
    intro k hk l hl
    simp [hL] at hk hl
    linarith
  have hD2 : Down x (L.erase i) := by
    intro k hk l hl
    rw [Finset.mem_erase] at hk
    have hk' : x 0 k ≤ x 0 i := by simpa [hL] using hk.2
    by_cases hli : l = i
    · rw [hli]; exact hk'
    · have : l ∉ L := fun h => hl (Finset.mem_erase.mpr ⟨hli, h⟩)
      simp [hL] at this
      linarith
  obtain ⟨a1, h1⟩ := sum_conv hx L hD1
  obtain ⟨a2, h2⟩ := sum_conv hx (L.erase i) hD2
  refine ⟨a1 - a2, (h1.sub h2).congr (fun t => ?_)⟩
  rw [← Finset.add_sum_erase L _ hiL]
  ring

lemma gap {n : ℕ} {x : ℝ → Fin n → ℝ} (hx : IsProperSolution x) (xs : Fin n → ℝ)
    (hlim : ∀ m, Tendsto (fun t => x t m) atTop (𝓝 (xs m))) (i j : Fin n)
    (hij : xs i < xs j) : 1 ≤ xs j - xs i := by
  by_contra hc
  push_neg at hc
  set D := Finset.univ.filter (fun k => xs k ≤ xs i) with hDdef
  have hD : Down x D := by
    intro k hk l hl
    simp [hDdef] at hk hl
    by_contra h0
    push_neg at h0
    have hle : ∀ t, 0 ≤ t → x t l ≤ x t k := fun t ht => order_pres hx l k h0.le t ht
    have : xs l ≤ xs k := le_of_tendsto_of_tendsto (hlim l) (hlim k)
      (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht; exact hle t ht)
    linarith
  have hiD : i ∈ D := by simp [hDdef]
  have hjD : j ∈ Dᶜ := by simp [hDdef]; exact hij
  set δ := (xs j - xs i) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hdl : Tendsto (fun t => x t j - x t i) atTop (𝓝 (xs j - xs i)) := (hlim j).sub (hlim i)
  have hev : ∀ᶠ t in atTop, x t j - x t i ∈ Set.Ioo δ 1 :=
    hdl.eventually (Ioo_mem_nhds (by rw [hδ]; linarith) hc)
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp hev
  set T := max T0 0 with hT
  have hT0' : 0 ≤ T := le_max_right _ _
  -- pointwise lower bound
  have hpt : ∀ τ, T ≤ τ → δ ≤ ∑ k ∈ D, rhs (x τ) k := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans hT0' hτ
    have hb := hT0 τ (le_trans (le_max_left _ _) hτ)
    rw [sum_rhs_eq]
    have hi1 : pt (x τ) i j ≤ ∑ l ∈ Dᶜ, pt (x τ) i l :=
      Finset.single_le_sum (f := fun l => pt (x τ) i l)
        (fun l hl => pt_nonneg hx D hD τ hτ0 i hiD l hl) hjD
    have hi2 : ∑ l ∈ Dᶜ, pt (x τ) i l ≤ ∑ k ∈ D, ∑ l ∈ Dᶜ, pt (x τ) k l :=
      Finset.single_le_sum (f := fun k => ∑ l ∈ Dᶜ, pt (x τ) k l)
        (fun k hk => Finset.sum_nonneg (fun l hl => pt_nonneg hx D hD τ hτ0 k hk l hl)) hiD
    have hpij : pt (x τ) i j = x τ j - x τ i := by
      unfold pt
      rw [if_pos]
      rw [abs_sub_comm, abs_lt]
      constructor <;> linarith [hb.1, hb.2]
    linarith [hb.1]
  set B := (D.card : ℝ) * ∑ m, |x 0 m| with hB
  have hST : ∑ k ∈ D, x T k ≤ B := sum_upper hx D T hT0'
  set t := T + (B - ∑ k ∈ D, x T k + 1) / δ with ht
  have hq : 0 ≤ (B - ∑ k ∈ D, x T k + 1) / δ := div_nonneg (by linarith) hδpos.le
  have hTt : T ≤ t := by rw [ht]; linarith
  have ht0 : 0 ≤ t := le_trans hT0' hTt
  have hSt : ∑ k ∈ D, x t k ≤ B := sum_upper hx D t ht0
  have e := sum_diff_eq hx.1 D hT0' ht0
  have hint : ∫ τ in T..t, δ ≤ ∫ τ in T..t, ∑ k ∈ D, rhs (x τ) k := by
    apply intervalIntegral.integral_mono_on hTt
    · exact intervalIntegrable_const
    · have hs := IntervalIntegrable.sum D (fun k _ => iint hx.1 k hT0' ht0)
      simpa only [Finset.sum_fn] using hs
    · intro u hu; exact hpt u hu.1
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have hmul : (t - T) * δ = B - ∑ k ∈ D, x T k + 1 := by
    rw [ht]; field_simp; ring
  linarith

end BHTAux9b

open Filter Topology BHTOpinion.Discrete in
theorem solution {n : ℕ} (x : ℝ → Fin n → ℝ)
    (hx : IsProperSolution x) :
    ∃ xstar ∈ F n, Tendsto x atTop (𝓝 xstar) := by
  choose xs hxs using BHTAux9b.coord_conv hx
  refine ⟨xs, ?_, tendsto_pi_nhds.mpr hxs⟩
  intro i j
  rcases lt_trichotomy (xs i) (xs j) with h | h | h
  · right
    have := BHTAux9b.gap hx xs hxs i j h
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    exact this
  · left; exact h
  · right
    have := BHTAux9b.gap hx xs hxs j i h
    rw [abs_of_pos (by linarith)]
    exact this
