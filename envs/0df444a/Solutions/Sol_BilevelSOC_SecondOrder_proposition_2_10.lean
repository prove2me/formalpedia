-- Prove2me | solution 1 for BilevelSOC.SecondOrder.proposition_2_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T20:34:09.874698+00:00
-- url     : https://prove2.me/submissions/12672b1e-8868-4793-96ad-78d6c0e55909

import Definitions.Def_BilevelSOC_SecondOrder_Model
open scoped Topology
open BilevelSOC.SecondOrder Filter Set

/-- A positive sequence can only take values below `δ` at indices beyond `K`. -/
theorem bsoc_small_index (s : ℕ → ℝ) (hs : ∀ k, 0 < s k) :
    ∀ K : ℕ, ∃ δ > 0, ∀ k, s k < δ → K ≤ k := by
  intro K
  induction K with
  | zero => exact ⟨1, one_pos, fun k _ => Nat.zero_le k⟩
  | succ K ih =>
    obtain ⟨δ, hδ, h⟩ := ih
    refine ⟨min δ (s K), lt_min hδ (hs K), fun k hk => ?_⟩
    have h1 := h k (lt_of_lt_of_le hk (min_le_left _ _))
    have h2 : k ≠ K := by
      rintro rfl
      exact lt_irrefl _ (lt_of_lt_of_le hk (min_le_right _ _))
    omega

theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (θ : V → ℝ) (x : V)
    (θ' : V → ℝ) (θ'' : V → V → ℝ)
    (hDiff : SecondOrderDirDiff θ x θ' θ'')
    (hEpi : SecondOrderEpiRegular θ x θ' θ'')
    (U : Set V) (hU : U ∈ 𝓝 x) (L : NNReal)
    (hLip : LipschitzOnWith L θ U)
    (hFirst : ∀ d, 0 ≤ θ' d)
    (hSecond : ∀ d, θ' d = 0 → d ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∀ w, c ≤ θ'' d w) :
    GrowthCondition θ Set.univ x 2 := by
  classical
  refine ⟨mem_univ _, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hk : ∀ k : ℕ, ∃ z, z ∈ Metric.ball x (1 / ((k : ℝ) + 1)) ∧
      θ z < θ x + 1 / ((k : ℝ) + 1) * ‖z - x‖ ^ 2 := by
    intro k
    obtain ⟨z, hz, hz2⟩ := hcon (Metric.ball x (1 / ((k : ℝ) + 1)))
      (Metric.ball_mem_nhds _ (by positivity)) (1 / ((k : ℝ) + 1)) (by positivity)
    rw [Real.rpow_two] at hz2
    exact ⟨z, hz.2, hz2⟩
  choose z0 hz0b hz0 using hk
  have ht0 : ∀ k, 0 < ‖z0 k - x‖ := by
    intro k
    rcases (norm_nonneg (z0 k - x)).lt_or_eq with h | h
    · exact h
    · exfalso
      have := hz0 k
      have hzx : z0 k = x := by rw [← sub_eq_zero, ← norm_eq_zero]; exact h.symm
      rw [hzx, sub_self, norm_zero] at this
      simp at this
  set e0 : ℕ → V := fun k => (‖z0 k - x‖)⁻¹ • (z0 k - x) with he0
  have he0s : ∀ k, e0 k ∈ Metric.sphere (0 : V) 1 := by
    intro k
    simp only [e0, mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (ht0 k).ne'
  obtain ⟨d, hd, φ, hφ, hφd⟩ := (isCompact_sphere (0 : V) 1).tendsto_subseq he0s
  have hdn : ‖d‖ = 1 := by simpa using hd
  have hd0 : d ≠ 0 := by
    intro h; rw [h, norm_zero] at hdn; exact zero_ne_one hdn
  -- the subsequence
  set g : ℕ → V := fun k => z0 (φ k) with hg
  set s : ℕ → ℝ := fun k => ‖z0 (φ k) - x‖ with hs
  set e : ℕ → V := fun k => e0 (φ k) with he
  set a : ℕ → ℝ := fun k => 1 / ((φ k : ℝ) + 1) with ha
  have hspos : ∀ k, 0 < s k := fun k => ht0 (φ k)
  have hge : ∀ k, g k - x = s k • e k := by
    intro k
    simp only [g, s, e, e0, smul_smul]
    rw [mul_inv_cancel₀ (hspos k).ne', one_smul]
  have hbad : ∀ k, θ (g k) < θ x + a k * s k ^ 2 := fun k => hz0 (φ k)
  have hsa : ∀ k, s k < a k := by
    intro k
    have := hz0b (φ k)
    rwa [Metric.mem_ball, dist_eq_norm] at this
  have hinv : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have ha0 : Tendsto a atTop (𝓝 0) := by
    refine squeeze_zero (fun k => by positivity) (fun k => ?_) hinv
    have : (k : ℝ) ≤ φ k := by exact_mod_cast hφ.id_le k
    simp only [a]
    gcongr
  have hs0 : Tendsto s atTop (𝓝 0) :=
    squeeze_zero (fun k => (hspos k).le) (fun k => (hsa k).le) ha0
  have hs0' : Tendsto s atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hs0, Eventually.of_forall hspos⟩
  have hed : Tendsto e atTop (𝓝 d) := hφd
  -- Step 1: θ' d ≤ 0, using the Lipschitz property
  have hgx : Tendsto g atTop (𝓝 x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact hs0
  have hxd : Tendsto (fun k => x + s k • d) atTop (𝓝 x) := by
    have := (hs0.smul_const d).const_add x
    simpa using this
  have hQ : Tendsto (fun k => (θ (x + s k • d) - θ x) / s k) atTop (𝓝 (θ' d)) :=
    ((hDiff d).1).comp hs0'
  have hub : Tendsto (fun k => a k * s k + L * ‖d - e k‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ‖d - e k‖) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := d)).sub hed
      rw [sub_self] at this
      simpa using this.norm
    have := (ha0.mul hs0).add (h1.const_mul (L : ℝ))
    simpa using this
  have hevle : ∀ᶠ k in atTop, (θ (x + s k • d) - θ x) / s k ≤ a k * s k + L * ‖d - e k‖ := by
    filter_upwards [hgx.eventually (mem_of_superset hU subset_rfl),
      hxd.eventually (mem_of_superset hU subset_rfl)] with k hk1 hk2
    have hL := hLip.dist_le_mul _ hk2 _ hk1
    rw [Real.dist_eq, dist_eq_norm] at hL
    have hgk : x + s k • d - g k = s k • (d - e k) := by
      have := hge k
      rw [smul_sub, ← this]; abel
    rw [hgk, norm_smul, Real.norm_of_nonneg (hspos k).le] at hL
    rw [div_le_iff₀ (hspos k)]
    have h1 := hbad k
    have h2 := (abs_le.1 hL).2
    nlinarith [hspos k]
  have hθd : θ' d ≤ 0 := le_of_tendsto_of_tendsto hQ hub hevle
  have hθd0 : θ' d = 0 := le_antisymm hθd (hFirst d)
  obtain ⟨c, hc, hcw⟩ := hSecond d hθd0 hd0
  -- Step 2: the curve through the bad points
  let κ : ℝ → ℕ := fun t => if h : ∃ k, s k = t then h.choose else 0
  have hκ : ∀ k, s (κ (s k)) = s k := by
    intro k
    have h : ∃ j, s j = s k := ⟨k, rfl⟩
    simp only [κ, dif_pos h]
    exact h.choose_spec
  let w : ℝ → V := fun t => if ∃ k, s k = t then
      (2 / t ^ 2) • (g (κ t) - x - t • d) else 0
  have hwk : ∀ k, w (s k) = (2 / s k ^ 2) • (g (κ (s k)) - x - s k • d) := by
    intro k
    have h : ∃ j, s j = s k := ⟨k, rfl⟩
    simp only [w, if_pos h]
  -- large-index property
  have hlarge : ∀ K : ℕ, ∀ᶠ n in atTop, K ≤ κ (s n) := by
    intro K
    obtain ⟨δ, hδ, hδK⟩ := bsoc_small_index s hspos K
    filter_upwards [hs0.eventually (gt_mem_nhds hδ)] with n hn
    exact hδK _ (by rw [hκ n]; exact hn)
  have hw : Tendsto (fun t : ℝ => t • w t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have := (Metric.tendsto_atTop.1 hed) (ε / 2) (by positivity)
    obtain ⟨K, hK⟩ := this
    obtain ⟨δ, hδ, hδK⟩ := bsoc_small_index s hspos K
    have hmem : Ioo (0 : ℝ) δ ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hδ
    filter_upwards [hmem] with t ht
    rw [dist_zero_right]
    by_cases h : ∃ k, s k = t
    · obtain ⟨k, rfl⟩ := h
      rw [hwk k]
      set j := κ (s k) with hj
      have hjK : K ≤ j := hδK j (by rw [hκ k]; exact ht.2)
      have hsj : s j = s k := hκ k
      have : s k • ((2 / s k ^ 2) • (g j - x - s k • d)) = (2 : ℝ) • (e j - d) := by
        rw [hge j, hsj, smul_smul, ← smul_sub, smul_smul]
        congr 1
        field_simp [(hspos k).ne']
      rw [this, norm_smul, Real.norm_two]
      have := hK j hjK
      rw [dist_eq_norm] at this
      linarith
    · simp only [w, if_neg h, smul_zero, norm_zero]
      exact hε
  have hep := hEpi d w hw (c / 4) (by positivity)
  have hep' := hs0'.eventually hep
  have hsmall : ∀ᶠ n in atTop, a (κ (s n)) < c / 4 := by
    obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 ha0) (c / 4) (by positivity)
    filter_upwards [hlarge K] with n hn
    have := hK _ hn
    rw [Real.dist_eq, sub_zero] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  obtain ⟨n, hn1, hn2⟩ := (hep'.and hsmall).exists
  set j := κ (s n) with hj
  set t := s n with ht
  have hsj : s j = t := hκ n
  have hpt : x + t • d + (t ^ 2 / 2) • w t = g j := by
    rw [ht, hwk n, smul_smul]
    have : s n ^ 2 / 2 * (2 / s n ^ 2) = 1 := by
      field_simp [(hspos n).ne']
    rw [this, one_smul]
    abel
  rw [hpt, hθd0] at hn1
  have h1 := hcw (w t)
  have h2 := hbad j
  rw [hsj] at h2
  have htpos : 0 < t := hspos n
  have : θ x + c / 4 * t ^ 2 ≤ θ (g j) := by nlinarith [sq_nonneg t]
  have : c / 4 * t ^ 2 < a j * t ^ 2 := by linarith
  have := lt_of_mul_lt_mul_right this (sq_nonneg t)
  linarith
