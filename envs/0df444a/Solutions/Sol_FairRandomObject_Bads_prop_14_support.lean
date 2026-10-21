-- Prove2me | solution 1 for FairRandomObject.Bads.prop_14_support
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:37:44.0927+00:00
-- url     : https://prove2.me/submissions/27ca7956-fc75-4093-ab5e-3bd4268aed84

import Mathlib
import Definitions.Def_FairRandomObject_Bads_Setting

set_option autoImplicit false
open MeasureTheory FairRandomObject.Bads

noncomputable def mixM {n : ℕ} {ι : Type} [Fintype ι] (w : ι → ℝ) (z : ι → Fin n → ℝ) :
    Measure (Fin n → ℝ) :=
  Measure.sum (fun i => ENNReal.ofReal (w i) • Measure.dirac (z i))

lemma mix_int {n : ℕ} {ι : Type} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (z : ι → Fin n → ℝ) (g : (Fin n → ℝ) → ℝ) :
    Integrable g (mixM w z) ∧ ∫ x, g x ∂mixM w z = ∑ i, w i * g (z i) := by
  have hc : ∀ i, ENNReal.ofReal (w i) ≠ ⊤ := fun i => ENNReal.ofReal_ne_top
  constructor
  · exact integrable_sum_dirac hc (Summable.of_finite)
  · unfold mixM
    rw [integral_sum_dirac hc, tsum_fintype]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ENNReal.toReal_ofReal (hw i), smul_eq_mul]

lemma mix_norm {n : ℕ} {ι : Type} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (z : ι → Fin n → ℝ) (hz : ∀ i, 0 ≤ z i)
    (hm : ∑ i, w i • z i = eN n) : IsNormalized (mixM w z) := by
  have hmeas : MeasurableSet {x : Fin n → ℝ | ¬ 0 ≤ x} :=
    (isClosed_le continuous_const continuous_id).measurableSet.compl
  refine ⟨⟨?_⟩, ?_, fun j => ⟨?_, ?_⟩⟩
  · unfold mixM
    rw [Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hw1, ENNReal.ofReal_one]
  · unfold mixM
    rw [Measure.sum_apply _ hmeas, tsum_fintype]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [Measure.smul_apply, Measure.dirac_apply' _ hmeas]
    simp [Set.indicator, hz i]
  · exact (mix_int w hw z (fun x => x j)).1
  · rw [(mix_int w hw z (fun x => x j)).2]
    have := congrFun hm j
    simpa [Finset.sum_apply, eN] using this

lemma hull_bound {n : ℕ} (hn : 2 ≤ n) (ϕ : Rule n) (hfs : FairShareBad ϕ)
    (p : (Fin n → ℝ) × ℝ)
    (hp : p ∈ convexHull ℝ {q : (Fin n → ℝ) × ℝ | 0 ≤ q.1 ∧ q.2 ≤ ϕ q.1 ⟨0, by omega⟩ * q.1 ⟨0, by omega⟩})
    (h1 : p.1 = eN n) : p.2 ≤ 1 / n := by
  obtain ⟨ι, _, w, z, hw0, hw1, hzH, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hp
  have h1' : ∑ i, w i • (z i).1 = eN n := by
    rw [← h1, ← hsum]; simp [Prod.fst_sum]
  have h2 : p.2 = ∑ i, w i * (z i).2 := by
    rw [← hsum]; simp [Prod.snd_sum]
  have hnorm := mix_norm w hw0 hw1 (fun i => (z i).1) (fun i => (hzH i).1) h1'
  have hfs' := hfs _ hnorm ⟨0, by omega⟩
  rw [(mix_int w hw0 (fun i => (z i).1) (fun x => ϕ x ⟨0, by omega⟩ * x ⟨0, by omega⟩)).2] at hfs'
  rw [h2]
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) hfs'
  exact mul_le_mul_of_nonneg_left (hzH i).2 (hw0 i)

theorem support_lemma {n : ℕ} (hn : 2 ≤ n) (ϕ : Rule n) (hϕ : IsAPIRule ϕ)
    (hfs : FairShareBad ϕ) :
    ∃ α : Fin n → ℝ, ∀ x : Fin n → ℝ, 0 ≤ x →
      ϕ x ⟨0, by omega⟩ * x ⟨0, by omega⟩ ≤ α ⬝ᵥ (x - eN n) + 1 / n := by
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set f : (Fin n → ℝ) → ℝ := fun x => ϕ x i0 * x i0 with hf
  have hf0 : ∀ x : Fin n → ℝ, 0 ≤ x → 0 ≤ f x := by
    intro x hx
    exact mul_nonneg ((hϕ.2 x hx).1 i0) (hx i0)
  set H : Set ((Fin n → ℝ) × ℝ) := {q | 0 ≤ q.1 ∧ q.2 ≤ f q.1} with hH
  set A : Set ((Fin n → ℝ) × ℝ) := convexHull ℝ H with hA
  have hAconv : Convex ℝ A := convex_convexHull ℝ H
  have he0 : (0 : Fin n → ℝ) ≤ eN n := fun _ => zero_le_one
  -- nonempty interior
  have hint : (interior A).Nonempty := by
    set U : Set ((Fin n → ℝ) × ℝ) := (Set.pi Set.univ (fun _ => Set.Ioi (0:ℝ))) ×ˢ Set.Iio 0 with hU
    have hUo : IsOpen U := (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioi)).prod isOpen_Iio
    have hUH : U ⊆ A := by
      intro q hq
      apply subset_convexHull ℝ H
      refine ⟨fun i => (hq.1 i (Set.mem_univ i)).le, ?_⟩
      have := hf0 q.1 (fun i => (hq.1 i (Set.mem_univ i)).le)
      have := hq.2
      simp only [Set.mem_Iio] at this
      linarith
    refine ⟨(eN n, -1), interior_maximal hUH hUo ?_⟩
    refine ⟨fun i _ => by simp [eN], ?_⟩
    simp
  -- P not in interior
  have hP : ((eN n, 1 / (n:ℝ)) : (Fin n → ℝ) × ℝ) ∉ interior A := by
    intro hPi
    have hcont : Continuous (fun ε : ℝ => ((eN n, 1 / (n:ℝ) + ε) : (Fin n → ℝ) × ℝ)) := by
      fun_prop
    have hnhds : (fun ε : ℝ => ((eN n, 1 / (n:ℝ) + ε) : (Fin n → ℝ) × ℝ)) ⁻¹' interior A ∈ nhds (0:ℝ) := by
      apply hcont.continuousAt.preimage_mem_nhds
      simpa using isOpen_interior.mem_nhds hPi
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
    have hmem : (δ / 2) ∈ Metric.ball (0:ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith
    have := hball hmem
    have hA' : ((eN n, 1 / (n:ℝ) + δ / 2) : (Fin n → ℝ) × ℝ) ∈ A := interior_subset this
    have := hull_bound hn ϕ hfs _ hA' rfl
    simp only at this
    linarith
  obtain ⟨ℓ, hℓ0, hℓ⟩ := geometric_hahn_banach_of_nonempty_interior_point hAconv hP hint
  set L1 : (Fin n → ℝ) →L[ℝ] ℝ := ℓ.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) ℝ) with hL1
  set c : ℝ := ℓ (0, 1) with hc
  have hdec : ∀ (y : Fin n → ℝ) (r : ℝ), ℓ (y, r) = L1 y + c * r := by
    intro y r
    have : ((y, r) : (Fin n → ℝ) × ℝ) = (y, 0) + r • ((0 : Fin n → ℝ), (1:ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul]
    simp [hL1, hc]
    ring
  have key : ∀ x : Fin n → ℝ, 0 ≤ x → ∀ r : ℝ, r ≤ f x →
      L1 x + c * r ≤ L1 (eN n) + c * (1 / n) := by
    intro x hx r hr
    have h1 := hℓ (x, r) (subset_convexHull ℝ H ⟨hx, hr⟩)
    rw [hdec, hdec] at h1
    exact h1
  have hc0 : 0 ≤ c := by
    have := key (eN n) he0 (1 / n - 1) (by
      have := hf0 _ he0
      have h2 : 1 / (n:ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]; exact_mod_cast (by omega : 1 ≤ n)
      linarith)
    nlinarith
  set b : Fin n → Fin n → ℝ := fun i j => if i = j then (1:ℝ) else 0 with hb
  have hLsum : ∀ y : Fin n → ℝ, L1 y = ∑ i, y i * L1 (b i) := by
    intro y
    have := LinearMap.pi_apply_eq_sum_univ (L1 : (Fin n → ℝ) →ₗ[ℝ] ℝ) y
    simpa [hb] using this
  have hcne : c ≠ 0 := by
    intro hc0'
    have hbi : ∀ i, L1 (b i) = 0 := by
      intro i
      have hbnn : ∀ j, |b i j| ≤ 1 := fun j => by
        simp only [hb]; split_ifs <;> simp
      have hx1 : 0 ≤ eN n + (1/2 : ℝ) • b i := fun j => by
        have := hbnn j
        have := (abs_le.mp this).1
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, eN, Pi.zero_apply]
        linarith
      have hx2 : 0 ≤ eN n - (1/2 : ℝ) • b i := fun j => by
        have := hbnn j
        have := (abs_le.mp this).2
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eN, Pi.zero_apply]
        linarith
      have k1 := key _ hx1 (f _) le_rfl
      have k2 := key _ hx2 (f _) le_rfl
      rw [hc0', zero_mul, zero_mul, add_zero, add_zero] at k1 k2
      rw [map_add, map_smul] at k1
      rw [map_sub, map_smul] at k2
      simp only [smul_eq_mul] at k1 k2
      linarith
    apply hℓ0
    refine ContinuousLinearMap.ext (fun p => ?_)
    obtain ⟨y, r⟩ := p
    rw [hdec, hLsum y]
    simp [hbi, hc0']
  have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hcne)
  refine ⟨fun i => -(L1 (b i)) / c, fun x hx => ?_⟩
  have hdot : c * ((fun i => -(L1 (b i)) / c) ⬝ᵥ (x - eN n)) = L1 (eN n) - L1 x := by
    have : L1 (x - eN n) = ∑ i, (x - eN n) i * L1 (b i) := hLsum _
    rw [map_sub] at this
    simp only [dotProduct]
    rw [Finset.mul_sum]
    have h3 : ∀ i, c * (-(L1 (b i)) / c * (x - eN n) i) = -((x - eN n) i * L1 (b i)) := by
      intro i; field_simp
    simp only [h3, Finset.sum_neg_distrib]
    linarith
  have k := key x hx (f x) le_rfl
  have : c * f x ≤ c * ((fun i => -(L1 (b i)) / c) ⬝ᵥ (x - eN n) + 1 / n) := by
    rw [mul_add, hdot]
    linarith
  exact le_of_mul_le_mul_left this hcpos

open Matrix in
theorem solution {n : ℕ} (hn : 2 ≤ n) (ϕ : Rule n) (hϕ : IsAPIRule ϕ)
    (hsym : IsSymmetric ϕ) (hfs : FairShareBad ϕ) :
    ∃ α : Fin n → ℝ, ∀ x : Fin n → ℝ, 0 ≤ x →
      ϕ x ⟨0, by omega⟩ * x ⟨0, by omega⟩ ≤ α ⬝ᵥ (x - eN n) + 1 / n :=
  support_lemma hn ϕ hϕ hfs
