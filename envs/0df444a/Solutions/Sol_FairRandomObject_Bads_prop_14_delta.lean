-- Prove2me | solution 1 for FairRandomObject.Bads.prop_14_delta
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:40:37.371823+00:00
-- url     : https://prove2.me/submissions/de39dadd-3e97-472f-88e7-9bd42ba99902

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

lemma avg_alpha {n : ℕ} (hn : 2 ≤ n) (ϕ : Rule n) (hsym : IsSymmetric ϕ) (α : Fin n → ℝ)
    (hα : ∀ x : Fin n → ℝ, 0 ≤ x →
      ϕ x ⟨0, by omega⟩ * x ⟨0, by omega⟩ ≤ α ⬝ᵥ (x - eN n) + 1 / n) :
    ∃ a β : ℝ, ∀ x : Fin n → ℝ, 0 ≤ x →
      ϕ x ⟨0, by omega⟩ * x ⟨0, by omega⟩ ≤
        1 / n + (a - β) * (x ⟨0, by omega⟩ - 1) + β * ((∑ k, x k) - n) := by
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set G : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter (fun π => π i0 = i0) with hG
  have h1G : (1 : Equiv.Perm (Fin n)) ∈ G := by simp [hG]
  have hNpos : 0 < (G.card : ℝ) := by
    have : 0 < G.card := Finset.card_pos.mpr ⟨_, h1G⟩
    exact_mod_cast this
  set N : ℝ := (G.card : ℝ) with hN
  set ab : Fin n → ℝ := fun k => (∑ π ∈ G, α (π k)) / N with hab
  have hab1 : ∀ x : Fin n → ℝ, 0 ≤ x →
      ϕ x i0 * x i0 ≤ ∑ k, ab k * (x k - 1) + 1 / n := by
    intro x hx
    have per : ∀ π ∈ G, ϕ x i0 * x i0 ≤ ∑ k, α (π k) * (x k - 1) + 1 / n := by
      intro π hπ
      have hπ0 : π i0 = i0 := (Finset.mem_filter.mp hπ).2
      have hπs : π.symm i0 = i0 := by rw [Equiv.symm_apply_eq]; exact hπ0.symm
      have hx' : (0 : Fin n → ℝ) ≤ fun j => x (π.symm j) := fun j => by show (0:ℝ) ≤ x (π.symm j); exact hx _
      have hs := hsym π x hx i0
      rw [hπ0] at hs
      have := hα _ hx'
      rw [hs] at this
      simp only [hπs] at this
      refine this.trans (le_of_eq ?_)
      congr 1
      simp only [dotProduct, Pi.sub_apply, eN]
      rw [← Equiv.sum_comp π (fun i => α i * (x (π.symm i) - 1))]
      simp
    have hsum := Finset.sum_le_sum per
    simp only [Finset.sum_const, nsmul_eq_mul] at hsum
    have e1 : ∑ π ∈ G, (∑ k, α (π k) * (x k - 1) + 1 / (n:ℝ))
        = ∑ k, (∑ π ∈ G, α (π k)) * (x k - 1) + N * (1 / n) := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp only [Finset.sum_mul, Finset.sum_const, nsmul_eq_mul, hN]
    rw [e1] at hsum
    have e2 : N * (∑ k, ab k * (x k - 1) + 1 / n)
        = ∑ k, (∑ π ∈ G, α (π k)) * (x k - 1) + N * (1 / n) := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hab]
      field_simp
    have : N * (ϕ x i0 * x i0) ≤ N * (∑ k, ab k * (x k - 1) + 1 / n) := by
      rw [e2]; exact hsum
    exact le_of_mul_le_mul_left this hNpos
  have hab2 : ab i0 = α i0 := by
    simp only [hab]
    have : ∀ π ∈ G, α (π i0) = α i0 := fun π hπ => by rw [(Finset.mem_filter.mp hπ).2]
    rw [Finset.sum_congr rfl this]
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp
    exact mul_comm _ _
  have hab3 : ∀ k k', k ≠ i0 → k' ≠ i0 → ab k = ab k' := by
    intro k k' hk hk'
    simp only [hab]
    congr 1
    set τ : Equiv.Perm (Fin n) := Equiv.swap k k' with hτ
    have hτ0 : τ i0 = i0 := Equiv.swap_apply_of_ne_of_ne (Ne.symm hk) (Ne.symm hk')
    refine Finset.sum_nbij' (fun π => π * τ) (fun π => π * τ⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro π hπ
      have hπ0 : π i0 = i0 := (Finset.mem_filter.mp hπ).2
      simp [hG, hπ0, hτ0]
    · intro π hπ
      have hπ0 : π i0 = i0 := (Finset.mem_filter.mp hπ).2
      have : τ.symm i0 = i0 := by rw [Equiv.symm_apply_eq]; exact hτ0.symm
      simp [hG, hπ0, this]
    · intro π _; simp
    · intro π _; simp
    · intro π _
      simp [hτ]
  obtain ⟨k1, hk1⟩ : ∃ k1 : Fin n, k1 ≠ i0 := ⟨⟨1, by omega⟩, by simp [hi0, Fin.ext_iff]⟩
  refine ⟨α i0, ab k1, fun x hx => ?_⟩
  refine (hab1 x hx).trans (le_of_eq ?_)
  have hsplit : ∑ k, ab k * (x k - 1)
      = ab k1 * ((∑ k, x k) - n) + (α i0 - ab k1) * (x i0 - 1) := by
    have : ∀ k, ab k * (x k - 1) = ab k1 * (x k - 1) + (ab k - ab k1) * (x k - 1) := by
      intro k; ring
    simp only [this, Finset.sum_add_distrib]
    have h5 : ∑ k, (ab k - ab k1) * (x k - 1) = (α i0 - ab k1) * (x i0 - 1) := by
      rw [Finset.sum_eq_single i0]
      · rw [hab2]
      · intro k _ hk
        rw [hab3 k k1 hk hk1]; ring
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h5, ← Finset.mul_sum, Finset.sum_sub_distrib]
    simp
  rw [hsplit]; ring

lemma const_share {n : ℕ} (hn : 2 ≤ n) (ϕ : Rule n) (hϕ : IsAPIRule ϕ) (hsym : IsSymmetric ϕ)
    (c : ℝ) (hc : 0 ≤ c) :
    ϕ (fun _ => c) ⟨0, by omega⟩ = 1 / n := by
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  have hx : (0 : Fin n → ℝ) ≤ fun _ => c := fun _ => hc
  have heq : ∀ i, ϕ (fun _ => c) i = ϕ (fun _ => c) i0 := by
    intro i
    have := hsym (Equiv.swap i0 i) (fun _ => c) hx i0
    rw [Equiv.swap_apply_left] at this
    exact this
  have hsum : ∑ i, ϕ (fun _ => c) i = 1 := (hϕ.2 _ hx).2
  rw [Finset.sum_congr rfl (fun i _ => heq i)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp
  linarith

theorem solution {n : ℕ} (hn : 2 ≤ n) (ϕ : Rule n) (hϕ : IsAPIRule ϕ)
    (hsym : IsSymmetric ϕ) (hfs : FairShareBad ϕ) :
    ∃ δ : ℝ, 0 ≤ δ ∧ ∀ x : Fin n → ℝ, 0 ≤ x → ∀ i, 0 < x i →
      ϕ x i ≤ 1 / n + δ * (mean x / x i - 1) := by
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  obtain ⟨α, hα⟩ := support_lemma hn ϕ hϕ hfs
  obtain ⟨a, β, hab⟩ := avg_alpha hn ϕ hsym α hα
  have hnpos : (0:ℝ) < n := by positivity
  -- constant profiles
  have hconst : ∀ c : ℝ, 0 ≤ c → c / n ≤ 1 / n + (a - β) * (c - 1) + β * (n * c - n) := by
    intro c hc
    have := hab (fun _ => c) (fun _ => hc)
    rw [const_share hn ϕ hϕ hsym c hc] at this
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    have e : 1 / (n:ℝ) * c = c / n := by ring
    rw [e] at this
    exact this
  have h0 := hconst 0 le_rfl
  have h2 := hconst 2 (by norm_num)
  have hs : a + (n - 1) * β = 1 / n := by
    have e0 : (0:ℝ) / n = 0 := zero_div _
    have e2 : (2:ℝ) / n = 2 * (1 / n) := by ring
    rw [e0] at h0
    rw [e2] at h2
    linarith
  -- reduced inequality T
  have hT : ∀ x : Fin n → ℝ, 0 ≤ x →
      ϕ x i0 * x i0 ≤ x i0 / n + β * ((∑ k, x k) - n * x i0) := by
    intro x hx
    have := hab x hx
    have ha : a = 1 / n - (n - 1) * β := by linarith
    rw [ha] at this
    have e : 1 / (n:ℝ) + (1 / n - (n - 1) * β - β) * (x i0 - 1) + β * (∑ k, x k - n)
        = x i0 / n + β * ((∑ k, x k) - n * x i0) := by
      field_simp
      ring
    linarith
  -- beta nonneg
  have hβ : 0 ≤ β := by
    set x : Fin n → ℝ := fun k => if k = i0 then 0 else 1 with hx
    have hx0 : 0 ≤ x := fun k => by simp only [hx]; split_ifs <;> simp
    have := hT x hx0
    have hxi : x i0 = 0 := by simp [hx]
    have hS : ∑ k, x k = n - 1 := by
      simp only [hx, Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul,
        mul_one, zero_add]
      have : (Finset.univ.filter (fun k : Fin n => ¬ k = i0)).card = n - 1 := by
        rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
        simp [Finset.filter_eq']
      rw [this]
      have : 1 ≤ n := by omega
      push_cast [this]
      ring
    rw [hxi, hS] at this
    have h3 : 0 ≤ β * ((n:ℝ) - 1) := by
      have := hS ▸ this
      nlinarith
    have hn1 : (0:ℝ) < n - 1 := by
      have : (2:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    exact nonneg_of_mul_nonneg_left h3 hn1
  refine ⟨n * β, by positivity, fun x hx i hxi => ?_⟩
  set π : Equiv.Perm (Fin n) := Equiv.swap i0 i with hπ
  have hx' : (0 : Fin n → ℝ) ≤ fun j => x (π.symm j) := fun j => by
    show (0:ℝ) ≤ x (π.symm j); exact hx _
  have hs1 := hsym π x hx i
  have hπi : π i = i0 := by simp [hπ]
  rw [hπi] at hs1
  have hπs : π.symm i0 = i := by rw [Equiv.symm_apply_eq]; exact hπi.symm
  have hTx := hT _ hx'
  rw [hs1] at hTx
  simp only [hπs] at hTx
  rw [Equiv.sum_comp π.symm x] at hTx
  have hmean : mean x = (∑ k, x k) / n := rfl
  rw [hmean]
  have key : ϕ x i * x i ≤ x i / n + β * ((∑ k, x k) - n * x i) := hTx
  have : ϕ x i ≤ 1 / n + β * ((∑ k, x k) / x i - n) := by
    have h1 : ϕ x i * x i ≤ (1 / n + β * ((∑ k, x k) / x i - n)) * x i := by
      have : (1 / (n:ℝ) + β * ((∑ k, x k) / x i - n)) * x i
          = x i / n + β * ((∑ k, x k) - n * x i) := by
        field_simp
      rw [this]; exact key
    exact le_of_mul_le_mul_right h1 hxi
  refine this.trans (le_of_eq ?_)
  field_simp
