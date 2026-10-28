-- Prove2me | solution 1 for DiscreteEnergy.limits_of_energy_recursions
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T10:57:16.192138+00:00
-- url     : https://prove2.me/submissions/831544ea-9472-4963-8d0c-36bb2c21caa1

import Mathlib

-- carved verbatim out of submission e3454a9c-3502-4c6b-9794-7eebefc4332c, lines 422-557

section
open Filter Topology NNReal
open InnerProductSpace

lemma nfb_telescope (u v : ℕ → ℝ) (h : ∀ n, u (n + 1) + v n ≤ u n) :
    ∀ N, (∑ i ∈ Finset.range N, v i) + u N ≤ u 0 := by
  intro N
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ]; linarith [h N]

lemma nfb_conv_of_incr (u w : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hw0 : ∀ n, 0 ≤ w n)
    (hw : Summable w) (h : ∀ n, u (n + 1) ≤ u n + w n) : ∃ l, Tendsto u atTop (𝓝 l) := by
  set g : ℕ → ℝ := fun n => u n - ∑ i ∈ Finset.range n, w i with hg
  have hanti : Antitone g := by
    apply antitone_nat_of_succ_le
    intro n; simp only [hg, Finset.sum_range_succ]; linarith [h n]
  have hbdd : BddBelow (Set.range g) := by
    refine ⟨-(∑' i, w i), ?_⟩
    rintro _ ⟨n, rfl⟩
    have := hw.sum_le_tsum (Finset.range n) (fun i _ => hw0 i)
    simp only [hg]; linarith [hu n]
  have hgt := tendsto_atTop_ciInf hanti hbdd
  have hst := hw.hasSum.tendsto_sum_nat
  refine ⟨_, (hgt.add hst).congr (fun n => ?_)⟩
  simp only [hg]; ring

lemma nfb_not_summable_shift (α : ℝ) (hα : 1 ≤ α) (c : ℝ) (hc : 0 < c) (h : ℕ → ℝ)
    (N : ℕ) (hh : ∀ n, N ≤ n → c / ((n:ℝ) + α) ≤ h n) (h0 : ∀ n, 0 ≤ h n) :
    ¬ Summable h := by
  intro hs
  have hs' : Summable (fun n => h (n + N)) := (_root_.summable_nat_add_iff N).2 hs
  have hb : Summable (fun n : ℕ => c / α * (1 / (((n + (N + 1) : ℕ)) : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs'
    have h1 := hh (n + N) (by omega)
    refine le_trans ?_ h1
    push_cast
    rw [mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0:ℝ) ≤ n + N := by positivity
    have h5 : (n:ℝ) + N + α ≤ α * ((n:ℝ) + (N + 1)) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h5 hc.le]
  have hb2 : Summable (fun n : ℕ => 1 / (((n + (N + 1) : ℕ)) : ℝ)) := by
    have := hb.mul_left (α / c)
    refine this.congr (fun n => ?_)
    field_simp
  have := (_root_.summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) (N + 1)).1 hb2
  exact Real.not_summable_one_div_natCast this

lemma nfb_lim_zero (α : ℝ) (hα : 1 ≤ α) (G h : ℕ → ℝ) (l : ℝ) (hG : Tendsto G atTop (𝓝 l))
    (hG0 : ∀ n, 0 ≤ G n) (hh0 : ∀ n, 0 ≤ h n) (hs : Summable h)
    (hGh : ∀ n, G n = ((n:ℝ) + α) * h n) : l = 0 := by
  have hl0 : 0 ≤ l := ge_of_tendsto' hG hG0
  by_contra hne
  have hl : 0 < l := lt_of_le_of_ne hl0 (Ne.symm hne)
  have hev : ∀ᶠ n in atTop, l / 2 < G n := hG.eventually (lt_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  apply nfb_not_summable_shift α hα (l / 2) (by linarith) h N _ hh0 hs
  intro n hn
  have := hN n hn
  rw [hGh n] at this
  have hpos : (0:ℝ) < n + α := by positivity
  rw [div_le_iff₀ hpos]; linarith

theorem solution (s α : ℝ) (hs : 0 < s) (hα : 3 < α) (θ dd ez : ℕ → ℝ)
    (hθ : ∀ n, 0 ≤ θ n) (hdd : ∀ n, 0 ≤ dd n) (hez : ∀ n, 0 ≤ ez n)
    (hE : ∀ n : ℕ, 2 * s / (α - 1) * ((n:ℝ) + α + 1) ^ 2 * θ (n + 1) + (α - 1) * ez (n + 1)
        + 2 * s / (α - 1) * ((α - 3) * ((n:ℝ) + 2) + (α - 2) ^ 2) * θ n ≤
        2 * s / (α - 1) * ((n:ℝ) + α) ^ 2 * θ n + (α - 1) * ez n)
    (hS : ∀ n : ℕ, 2 * s * θ (n + 1) + dd (n + 1) ≤
        2 * s * θ n + (((n:ℝ) + 1) / ((n:ℝ) + α + 1)) ^ 2 * dd n) :
    Tendsto (fun n : ℕ => ((n:ℝ) + α) ^ 2 * θ n) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ((n:ℝ) + α) ^ 2 * dd n) atTop (𝓝 0) ∧
    ∃ l, Tendsto ez atTop (𝓝 l) := by
  have hα1 : (0:ℝ) < α - 1 := by linarith
  set e : ℕ → ℝ := fun n => 2 * s / (α - 1) * ((n:ℝ) + α) ^ 2 * θ n + (α - 1) * ez n with he
  have he0 : ∀ n, 0 ≤ e n := fun n => by
    have := hθ n; have := hez n; simp only [he]; positivity
  set c : ℝ := 2 * s * (α - 3) / (α - 1) with hc
  have hc0 : 0 < c := by rw [hc]; apply div_pos _ hα1; nlinarith
  have hEstep : ∀ n : ℕ, e (n + 1) + c * (((n:ℝ) + α) * θ n) ≤ e n := by
    intro n
    have h1 := hE n
    have h2 : c * (((n:ℝ) + α) * θ n) ≤
        2 * s / (α - 1) * ((α - 3) * ((n:ℝ) + 2) + (α - 2) ^ 2) * θ n := by
      rw [hc]
      have hq : 2 * s * (α - 3) / (α - 1) * (((n:ℝ) + α) * θ n) =
          2 * s / (α - 1) * ((α - 3) * ((n:ℝ) + α)) * θ n := by ring
      rw [hq]
      apply mul_le_mul_of_nonneg_right _ (hθ n)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    simp only [he]; push_cast at h1 ⊢
    linarith
  have hsumA : ∀ N, ∑ i ∈ Finset.range N, c * (((i:ℝ) + α) * θ i) ≤ e 0 := by
    intro N
    have := nfb_telescope e _ hEstep N
    linarith [he0 N]
  set a : ℕ → ℝ := fun n => ((n:ℝ) + α) * θ n with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n => by have := hθ n; simp only [ha]; positivity
  have hsa : Summable a := by
    apply summable_of_sum_range_le ha0 (c := e 0 / c)
    intro N
    rw [le_div_iff₀ hc0, Finset.sum_mul]
    have := hsumA N
    simp only [ha]
    calc ∑ i ∈ Finset.range N, ((i:ℝ) + α) * θ i * c
        = ∑ i ∈ Finset.range N, c * (((i:ℝ) + α) * θ i) := by
          apply Finset.sum_congr rfl; intro i _; ring
      _ ≤ e 0 := this
  set G : ℕ → ℝ := fun n => ((n:ℝ) + α) ^ 2 * (2 * s * θ n + dd n) with hG
  have hG0 : ∀ n, 0 ≤ G n := fun n => by
    have := hθ n; have := hdd n; simp only [hG]; positivity
  have hGstep : ∀ n : ℕ, G (n + 1) + (α - 1) * (((n:ℝ) + α) * dd n) ≤ G n + 6 * s * a n := by
    intro n
    have h1 := hS n
    have hT : (0:ℝ) < (n:ℝ) + α + 1 := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg ((n:ℝ) + α + 1))
    have e3 : ((n:ℝ) + α + 1) ^ 2 * (2 * s * θ n + (((n:ℝ) + 1) / ((n:ℝ) + α + 1)) ^ 2 * dd n)
        = ((n:ℝ) + α + 1) ^ 2 * (2 * s * θ n) + ((n:ℝ) + 1) ^ 2 * dd n := by
      field_simp
    rw [e3] at h2
    simp only [hG, ha]; push_cast
    have hdn := hdd n
    have hθn := hθ n
    have k1 : (α - 1) * (((n:ℝ) + α) * dd n) ≤ (α - 1) * (2 * (n:ℝ) + α + 1) * dd n := by
      have : (α - 1) * (((n:ℝ) + α)) ≤ (α - 1) * (2 * (n:ℝ) + α + 1) := by
        apply mul_le_mul_of_nonneg_left _ hα1.le; have : (0:ℝ) ≤ n := by positivity
        linarith
      nlinarith
    have k2 : 2 * s * (2 * (n:ℝ) + 2 * α + 1) * θ n ≤ 6 * s * (((n:ℝ) + α) * θ n) := by
      have : (0:ℝ) ≤ n := by positivity
      have : 2 * s * (2 * (n:ℝ) + 2 * α + 1) ≤ 6 * s * ((n:ℝ) + α) := by nlinarith
      nlinarith
    nlinarith
  set b : ℕ → ℝ := fun n => ((n:ℝ) + α) * dd n with hb
  have hb0 : ∀ n, 0 ≤ b n := fun n => by have := hdd n; simp only [hb]; positivity
  have hsb : Summable b := by
    apply summable_of_sum_range_le hb0 (c := (G 0 + 6 * s * ∑' i, a i) / (α - 1))
    intro N
    rw [le_div_iff₀ hα1, Finset.sum_mul]
    have h1 := nfb_telescope G (fun n => (α - 1) * b n - 6 * s * a n)
      (fun n => by have := hGstep n; simp only [hb]; linarith) N
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
    have h2 := hsa.sum_le_tsum (Finset.range N) (fun i _ => ha0 i)
    have h3 : ∑ i ∈ Finset.range N, b i * (α - 1) = (α - 1) * ∑ i ∈ Finset.range N, b i := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [h3]
    have := hG0 N
    nlinarith
  obtain ⟨lG, hlG⟩ := nfb_conv_of_incr G (fun n => 6 * s * a n) hG0
    (fun n => by have := ha0 n; positivity) (hsa.mul_left _)
    (fun n => by have := hGstep n; have := hb0 n; simp only [hb] at *; nlinarith)
  have hlG0 : lG = 0 := by
    apply nfb_lim_zero α (by linarith) G (fun n => 2 * s * a n + b n) lG hlG hG0
      (fun n => by have := ha0 n; have := hb0 n; positivity) ((hsa.mul_left _).add hsb)
    intro n; simp only [hG, ha, hb]; ring
  rw [hlG0] at hlG
  refine ⟨?_, ?_, ?_⟩
  · have hup : ∀ n : ℕ, ((n:ℝ) + α) ^ 2 * θ n ≤ G n / (2 * s) := by
      intro n
      rw [le_div_iff₀ (by positivity)]
      simp only [hG]
      have := hdd n
      have : (0:ℝ) ≤ ((n:ℝ) + α) ^ 2 * dd n := by positivity
      nlinarith
    have hlim : Tendsto (fun n => G n / (2 * s)) atTop (𝓝 0) := by
      simpa using hlG.div_const (2 * s)
    exact squeeze_zero (fun n => by have := hθ n; positivity) hup hlim
  · have hup : ∀ n : ℕ, ((n:ℝ) + α) ^ 2 * dd n ≤ G n := by
      intro n
      simp only [hG]
      have := hθ n
      have : (0:ℝ) ≤ ((n:ℝ) + α) ^ 2 * (2 * s * θ n) := by positivity
      nlinarith
    exact squeeze_zero (fun n => by have := hdd n; positivity) hup hlG
  · have hanti : Antitone e := by
      apply antitone_nat_of_succ_le
      intro n; have := hEstep n; have := ha0 n
      have : 0 ≤ c * (((n:ℝ) + α) * θ n) := by positivity
      linarith
    have hbdd : BddBelow (Set.range e) := ⟨0, by rintro _ ⟨n, rfl⟩; exact he0 n⟩
    have het := tendsto_atTop_ciInf hanti hbdd
    have hθl : Tendsto (fun n : ℕ => ((n:ℝ) + α) ^ 2 * θ n) atTop (𝓝 0) := by
      have hup : ∀ n : ℕ, ((n:ℝ) + α) ^ 2 * θ n ≤ G n / (2 * s) := by
        intro n
        rw [le_div_iff₀ (by positivity)]
        simp only [hG]
        have := hdd n
        have : (0:ℝ) ≤ ((n:ℝ) + α) ^ 2 * dd n := by positivity
        nlinarith
      have hlim : Tendsto (fun n => G n / (2 * s)) atTop (𝓝 0) := by
        simpa using hlG.div_const (2 * s)
      exact squeeze_zero (fun n => by have := hθ n; positivity) hup hlim
    refine ⟨_, ((het.sub (hθl.const_mul (2 * s / (α - 1)))).div_const (α - 1)).congr (fun n => ?_)⟩
    simp only [he]
    field_simp
    ring

end
