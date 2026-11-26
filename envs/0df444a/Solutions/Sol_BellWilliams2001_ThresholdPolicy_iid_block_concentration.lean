-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.iid_block_concentration
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:57:07.776203+00:00
-- url     : https://prove2.me/submissions/c2de345a-06a4-41d5-a9b8-0b02b0af677a

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

private theorem upper_block {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hm : ∀ j, Measurable (X j))
    (hi : iIndepFun X P) (hId : ∀ j, IdentDistrib (X j) (X 0) P P)
    (hMean : ∫ ω, X 0 ω ∂P = 0)
    (hmom : ∃ a > 0, ∀ u ∈ Ioo (-a) a, Integrable (fun ω => Real.exp (u * X 0 ω)) P)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ j m : ℕ,
      P {ω | δ * m ≤ ∑ i ∈ Finset.range m, X (j+i) ω} ≤ ENNReal.ofReal (ρ^m) := by
  obtain ⟨a,ha,hExp⟩ := hmom
  have hIts : (0:ℝ) ∈ interior (integrableExpSet (X 0) P) := by
    apply mem_interior_iff_mem_nhds.2
    exact Filter.mem_of_superset (Ioo_mem_nhds (neg_lt_zero.mpr ha) ha) hExp
  have hd : HasDerivAt (mgf (X 0) P) 0 0 := by
    simpa [hMean] using hasDerivAt_mgf hIts
  let g (u : ℝ) := Real.exp (-δ*u) * mgf (X 0) P u
  have hg0 : g 0 = 1 := by simp [g]
  have hder : HasDerivAt g (-δ) 0 := by
    have he := ((hasDerivAt_id (0:ℝ)).const_mul (-δ)).exp
    simpa [g, Pi.mul_def] using he.mul hd
  have hsmall : ∀ᶠ u in 𝓝[>] (0:ℝ), g u < 1 := by
    have hh := hder.tendsto_slope_zero_right.eventually_lt_const (neg_lt_zero.mpr hδ)
    filter_upwards [hh, eventually_mem_nhdsWithin (s := Ioi (0:ℝ)) (a := 0)] with u hu hupos
    have hupos' : 0 < u := hupos
    -- The slope is `(g u - g 0) / u`, whose sign is the sign of its numerator.
    have hu' : (g u - g 0) / u < 0 := by simpa [div_eq_inv_mul] using hu
    have := (div_lt_iff₀ hupos').1 hu'
    linarith
  have hIoo : ∀ᶠ u in 𝓝[>] (0:ℝ), u ∈ Ioo (-a) a :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (neg_lt_zero.mpr ha) ha)
  have hposSide : ∀ᶠ u in 𝓝[>] (0:ℝ), u ∈ Ioi (0:ℝ) := eventually_mem_nhdsWithin
  obtain ⟨u,hu,hua,hup⟩ := (hsmall.and (hIoo.and hposSide)).exists
  have hupos : 0 < u := hup
  have hmgf0 : 0 < mgf (X 0) P u := mgf_pos (hExp u hua)
  refine ⟨g u, mul_pos (Real.exp_pos _) hmgf0, hu, fun j m => ?_⟩
  let W (i : ℕ) := X (j+i)
  have hW : iIndepFun W P := hi.precomp (g := fun i => j+i) (fun _ _ h => Nat.add_left_cancel h)
  have hWm (i : ℕ) : Measurable (W i) := hm _
  have hWe (i : ℕ) : Integrable (fun ω => Real.exp (u * W i ω)) P :=
    ((hId (j+i)).comp ((measurable_const_mul u).exp)).integrable_iff.2 (hExp u hua)
  let S : Ω → ℝ := ∑ i ∈ Finset.range m, W i
  have hS : ∀ ω, S ω = ∑ i ∈ Finset.range m, X (j+i) ω := by simp [S,W,Finset.sum_apply]
  have hmgf : mgf S P u = mgf (X 0) P u ^ m := by
    dsimp only [S]
    rw [hW.mgf_sum hWm, Finset.prod_eq_pow_card (fun i _ => mgf_congr_of_identDistrib _ _ (hId (j+i)) u),
      Finset.card_range]
  have hSI := hW.integrable_exp_mul_sum hWm (s := Finset.range m) (fun i _ => hWe i)
  have hb := measure_ge_le_exp_mul_mgf (μ := P) (X := S) (δ * m) hupos.le hSI
  have heq : Real.exp (-u * (δ * m)) * mgf S P u = g u ^ m := by
    dsimp only [g]
    rw [hmgf, mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  rw [heq] at hb
  have hset : {ω | δ * (m : ℝ) ≤ S ω} = {ω | δ * (m : ℝ) ≤ ∑ i ∈ Finset.range m, X (j+i) ω} := by
    ext ω
    simp [hS]
  rw [hset] at hb
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _ : P _ ≠ ⊤)) ▸ ENNReal.ofReal_le_ofReal hb

set_option maxHeartbeats 1000000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hm : ∀ j, Measurable (X j))
    (hi : iIndepFun X P) (hId : ∀ j, IdentDistrib (X j) (X 0) P P)
    (hMean : ∫ ω, X 0 ω ∂P = 0)
    (hmom : ∃ a > 0, ∀ u ∈ Ioo (-a) a, Integrable (fun ω => Real.exp (u * X 0 ω)) P)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ j m : ℕ,
      P {ω | δ * m ≤ |∑ i ∈ Finset.range m, X (j+i) ω|} ≤ ENNReal.ofReal (2 * ρ^m) := by
  obtain ⟨r,hr,hr1,hupper⟩ := upper_block P X hm hi hId hMean hmom δ hδ
  let X' (j : ℕ) (ω : Ω) := -X j ω
  have hm' (j : ℕ) : Measurable (X' j) := (hm j).neg
  have hi' : iIndepFun X' P := hi.comp (fun _ (x : ℝ) => -x) (fun _ => measurable_id.neg)
  have hId' (j : ℕ) : IdentDistrib (X' j) (X' 0) P P := (hId j).comp measurable_id.neg
  have hMean' : ∫ ω, X' 0 ω ∂P = 0 := by simp [X', integral_neg, hMean]
  have hMom' : ∃ a > 0, ∀ u ∈ Ioo (-a) a, Integrable (fun ω => Real.exp (u * X' 0 ω)) P := by
    obtain ⟨a,ha,h⟩ := hmom
    refine ⟨a,ha,fun u hu => ?_⟩
    have hn : -u ∈ Ioo (-a) a := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    simpa only [X', mul_neg, neg_mul] using h (-u) hn
  obtain ⟨s,hs,hs1,hlower⟩ := upper_block P X' hm' hi' hId' hMean' hMom' δ hδ
  let ρ := max r s
  refine ⟨ρ,hr.trans_le (le_max_left _ _),max_lt hr1 hs1,fun j m => ?_⟩
  let U := {ω | δ * (m:ℝ) ≤ ∑ i ∈ Finset.range m, X (j+i) ω}
  let D := {ω | δ * (m:ℝ) ≤ ∑ i ∈ Finset.range m, X' (j+i) ω}
  have hIncluded : {ω | δ * (m:ℝ) ≤ |∑ i ∈ Finset.range m, X (j+i) ω|} ⊆ U ∪ D := by
    intro ω hω
    change δ * (m:ℝ) ≤ |∑ i ∈ Finset.range m, X (j+i) ω| at hω
    rcases le_total 0 (∑ i ∈ Finset.range m, X (j+i) ω) with h | h
    · exact Or.inl (by simpa [U,abs_of_nonneg h] using hω)
    · exact Or.inr (by simpa [D,X',Finset.sum_neg_distrib,abs_of_nonpos h] using hω)
  calc
    _ ≤ P U + P D := (measure_mono hIncluded).trans (measure_union_le U D)
    _ ≤ ENNReal.ofReal (ρ^m) + ENNReal.ofReal (ρ^m) := by
      refine add_le_add ((hupper j m).trans ?_) ((hlower j m).trans ?_)
      · exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hr.le (le_max_left _ _) _)
      · exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hs.le (le_max_right _ _) _)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by dsimp [ρ]; positivity) (by dsimp [ρ]; positivity), two_mul]
