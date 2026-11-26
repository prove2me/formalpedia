-- Prove2me | solution 1 for DeepONetUniversal.sensor_hull_compact
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T23:29:51.571951+00:00
-- url     : https://prove2.me/submissions/eda50cf0-2e05-4600-8536-fe41105a0669

import Mathlib
import Definitions.Def_DeepONetUniversal_Basic
import Theorems.Thm_DeepONetUniversal_arzela_ascoli
import Theorems.Thm_DeepONetUniversal_interpolation_error_tendsto_zero

open MeasureTheory Filter Topology DeepONetUniversal

private lemma sensor_mem_Icc' {a b : ℝ} (hab : a < b) {m j : ℕ} (hm : 0 < m) (hj : j ≤ m) :
    sensor a b m j ∈ Set.Icc a b := by
  unfold sensor
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hba : 0 < b - a := sub_pos.mpr hab
  have hj_le : (j : ℝ) ≤ m := Nat.cast_le.mpr hj
  constructor
  · have : 0 ≤ (j : ℝ) * (b - a) / m := by positivity
    linarith
  · have h1 : (j : ℝ) * (b - a) / m ≤ m * (b - a) / m := by gcongr
    rw [mul_div_cancel_left₀ _ hm_pos.ne'] at h1
    linarith

private lemma sensor_succ_sub' (a b : ℝ) {m : ℕ} (hm : 0 < m) (j : ℕ) :
    sensor a b m (j + 1) - sensor a b m j = (b - a) / m := by
  unfold sensor
  push_cast
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  field_simp
  ring

private lemma sensor_zero' (a b : ℝ) (m : ℕ) : sensor a b m 0 = a := by
  simp [sensor]

private lemma sensor_self' (a b : ℝ) {m : ℕ} (hm : 0 < m) : sensor a b m m = b := by
  unfold sensor
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [mul_div_cancel_left₀ _ hm_ne]
  ring

private lemma sensor_mono' {a b : ℝ} (hab : a < b) {m : ℕ} (hm : 0 < m) {i j : ℕ} (hij : i ≤ j) :
    sensor a b m i ≤ sensor a b m j := by
  unfold sensor
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hba : 0 < b - a := sub_pos.mpr hab
  have : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
  gcongr

private lemma interp_eq_affine_on_seg {a b : ℝ} (hab : a < b) {m j : ℕ} (hm : 0 < m) (hj : j < m)
    (u : ℝ → ℝ) {x : ℝ} (hx : x ∈ Set.Icc (sensor a b m j) (sensor a b m (j + 1))) :
    interp a b m u x =
      u (sensor a b m j) +
        (u (sensor a b m (j + 1)) - u (sensor a b m j)) /
          (sensor a b m (j + 1) - sensor a b m j) * (x - sensor a b m j) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hstep : sensor a b m (j + 1) - sensor a b m j ≠ 0 := by
    rw [sensor_succ_sub' a b hm j]
    exact (div_pos hba hm_pos).ne'
  rcases eq_or_lt_of_le hx.2 with rfl | hlt
  · -- x = sensor a b m (j + 1)
    have ht : (sensor a b m (j + 1) - a) * m / (b - a) = (j + 1 : ℕ) := by
      unfold sensor
      push_cast
      field_simp [hba.ne', hm_pos.ne']
      ring
    have hfl : ⌊(sensor a b m (j + 1) - a) * m / (b - a)⌋₊ = j + 1 := by
      rw [ht, Nat.floor_natCast]
    by_cases hj1 : j + 1 < m
    · have hmin : min ⌊(sensor a b m (j + 1) - a) * m / (b - a)⌋₊ (m - 1) = j + 1 := by
        rw [hfl]
        exact min_eq_left (by omega)
      unfold interp
      dsimp only
      rw [hmin, sub_self, mul_zero, add_zero]
      field_simp [hstep]
      ring
    · have hjm : j = m - 1 := by omega
      have hmin : min ⌊(sensor a b m (j + 1) - a) * m / (b - a)⌋₊ (m - 1) = j := by
        rw [hfl]
        rw [hjm]
        exact min_eq_right (by omega)
      unfold interp
      dsimp only
      rw [hmin]
  · -- sensor a b m j ≤ x < sensor a b m (j + 1)
    set t : ℝ := (x - a) * m / (b - a)
    have ht_lo : (j : ℝ) ≤ t := by
      dsimp [t]
      rw [le_div_iff₀ hba]
      have h1 : sensor a b m j ≤ x := hx.1
      unfold sensor at h1
      have h2 : (j : ℝ) * (b - a) / m ≤ x - a := by linarith
      have h3 : (j : ℝ) * (b - a) / m * m ≤ (x - a) * m := by gcongr
      rwa [div_mul_cancel₀ _ hm_pos.ne'] at h3
    have ht_hi : t < (j : ℝ) + 1 := by
      dsimp [t]
      rw [div_lt_iff₀ hba]
      have h1 : x < sensor a b m (j + 1) := hlt
      unfold sensor at h1
      push_cast at h1
      have h2 : x - a < ((j : ℝ) + 1) * (b - a) / m := by linarith
      have h3 : (x - a) * m < ((j : ℝ) + 1) * (b - a) / m * m := by gcongr
      rwa [div_mul_cancel₀ _ hm_pos.ne'] at h3
    have hfl : ⌊t⌋₊ = j := by
      rw [Nat.floor_eq_iff (le_trans (Nat.cast_nonneg j) ht_lo)]
      exact ⟨ht_lo, ht_hi⟩
    have hmin : min ⌊t⌋₊ (m - 1) = j := by
      rw [hfl]
      exact min_eq_left (by omega)
    unfold interp
    dsimp only
    rw [hmin]

private lemma continuousOn_interp {a b : ℝ} (hab : a < b) {m : ℕ} (hm : 0 < m) (u : ℝ → ℝ) :
    ContinuousOn (interp a b m u) (Set.Icc a b) := by
  suffices ∀ k ≤ m, ContinuousOn (interp a b m u) (Set.Icc a (sensor a b m k)) by
    simpa [sensor_self' a b hm] using this m le_rfl
  intro k hk
  induction k with
  | zero =>
    rw [sensor_zero', Set.Icc_self]
    exact continuousOn_singleton _ _
  | succ k ih =>
    have hprev := ih (Nat.le_of_succ_le hk)
    have hseg : ContinuousOn (interp a b m u) (Set.Icc (sensor a b m k) (sensor a b m (k + 1))) := by
      have hcont : Continuous fun x : ℝ =>
          u (sensor a b m k) +
            (u (sensor a b m (k + 1)) - u (sensor a b m k)) /
              (sensor a b m (k + 1) - sensor a b m k) * (x - sensor a b m k) := by
        fun_prop
      exact hcont.continuousOn.congr fun x hx => interp_eq_affine_on_seg hab hm hk u hx
    have hunion : Set.Icc a (sensor a b m (k + 1)) =
        Set.Icc a (sensor a b m k) ∪ Set.Icc (sensor a b m k) (sensor a b m (k + 1)) := by
      rw [Set.Icc_union_Icc_eq_Icc]
      · simpa [sensor_zero'] using sensor_mono' hab hm (Nat.zero_le k)
      · exact sensor_mono' hab hm (Nat.le_succ k)
    rw [hunion]
    exact hprev.union_of_isClosed hseg isClosed_Icc isClosed_Icc

private noncomputable def interpMap {a b : ℝ} (hab : a < b) {m : ℕ} (hm : 0 < m)
    (u : C(Set.Icc a b, ℝ)) : C(Set.Icc a b, ℝ) :=
  ⟨fun x => interp a b m (evalAt u) x.1,
    continuousOn_iff_continuous_domRestrict.mp (continuousOn_interp hab hm (evalAt u))⟩

private lemma interp_convex_bound {a b : ℝ} (hab : a < b) {m : ℕ} (hm : 0 < m)
    (u : ℝ → ℝ) (M : ℝ) (hM : ∀ j ≤ m, |u (sensor a b m j)| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc a b) : |interp a b m u x| ≤ M := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  set j := min ⌊(x - a) * m / (b - a)⌋₊ (m - 1)
  have hj_lt : j < m := by omega
  have hj_succ : j + 1 ≤ m := by omega
  -- Get x ∈ [sensor j, sensor (j+1)]
  set t : ℝ := (x - a) * m / (b - a)
  have ht0 : 0 ≤ t := div_nonneg (mul_nonneg (sub_nonneg.mpr hx.1) hm_pos.le) hba.le
  have hlo : sensor a b m j ≤ x := by
    unfold sensor
    have hjt : (j : ℝ) ≤ t := (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le ht0)
    have h1 : (j : ℝ) * (b - a) / m ≤ t * (b - a) / m := by gcongr
    have h2 : t * (b - a) / m = x - a := by dsimp [t]; field_simp [hba.ne', hm_pos.ne']
    rw [h2] at h1
    linarith
  have hhi : x ≤ sensor a b m (j + 1) := by
    by_cases hfl : ⌊t⌋₊ ≤ m - 1
    · have hj_eq : j = ⌊t⌋₊ := min_eq_left hfl
      rw [hj_eq]
      unfold sensor
      have ht_lt : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
      have h1 : t * (b - a) / m < ((⌊t⌋₊ : ℝ) + 1) * (b - a) / m := by gcongr
      have h2 : t * (b - a) / m = x - a := by dsimp [t]; field_simp [hba.ne', hm_pos.ne']
      rw [h2] at h1
      push_cast
      linarith
    · have hj_eq : j = m - 1 := by
        change min ⌊t⌋₊ (m - 1) = m - 1
        exact min_eq_right (by omega)
      have hj1 : j + 1 = m := by omega
      rw [hj1, sensor_self' a b hm]
      exact hx.2
  have hstep_pos : 0 < sensor a b m (j + 1) - sensor a b m j := by
    rw [sensor_succ_sub' a b hm j]
    exact div_pos hba hm_pos
  set lam : ℝ := (x - sensor a b m j) / (sensor a b m (j + 1) - sensor a b m j)
  have hlam0 : 0 ≤ lam := div_nonneg (sub_nonneg.mpr hlo) hstep_pos.le
  have hlam1 : lam ≤ 1 := (div_le_one hstep_pos).mpr (sub_le_sub_right hhi _)
  have heq : interp a b m u x =
      (1 - lam) * u (sensor a b m j) + lam * u (sensor a b m (j + 1)) := by
    change u (sensor a b m j) + (u (sensor a b m (j + 1)) - u (sensor a b m j)) /
      (sensor a b m (j + 1) - sensor a b m j) * (x - sensor a b m j) =
      (1 - lam) * u (sensor a b m j) + lam * u (sensor a b m (j + 1))
    dsimp only [lam]
    have hne : sensor a b m (j + 1) - sensor a b m j ≠ 0 := hstep_pos.ne'
    field_simp [hne]
    ring
  rw [heq]
  have h1 := hM j (Nat.le_of_lt hj_lt)
  have h2 := hM (j + 1) hj_succ
  calc |(1 - lam) * u (sensor a b m j) + lam * u (sensor a b m (j + 1))|
      ≤ |(1 - lam) * u (sensor a b m j)| + |lam * u (sensor a b m (j + 1))| := abs_add_le _ _
    _ = (1 - lam) * |u (sensor a b m j)| + lam * |u (sensor a b m (j + 1))| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hlam1), abs_of_nonneg hlam0]
    _ ≤ (1 - lam) * M + lam * M := by gcongr
    _ = M := by ring

private lemma interpMap_continuous {a b : ℝ} (hab : a < b) {m : ℕ} (hm : 0 < m) :
    Continuous (interpMap hab hm) := by
  rw [Metric.continuous_iff]
  intro u ε hε
  refine ⟨ε, hε, fun v huv => ?_⟩
  have hdist : ‖v - u‖ < ε := by rwa [← dist_eq_norm]
  rw [dist_eq_norm, ContinuousMap.norm_lt_iff _ hε]
  intro x
  have hdiff : interpMap hab hm v x - interpMap hab hm u x =
      interp a b m (fun t => evalAt v t - evalAt u t) x.1 := by
    simp only [interpMap, ContinuousMap.coe_mk, interp]
    ring
  change |interpMap hab hm v x - interpMap hab hm u x| < ε
  rw [hdiff]
  have hle : |interp a b m (fun t => evalAt v t - evalAt u t) x.1| ≤ ‖v - u‖ := by
    apply interp_convex_bound hab hm _ ‖v - u‖ _ x.2
    intro j hj
    have hs := sensor_mem_Icc' hab hm hj
    simp only [evalAt, dif_pos hs]
    exact ContinuousMap.norm_coe_le_norm (v - u) ⟨sensor a b m j, hs⟩
  exact hle.trans_lt hdist

private lemma interpSet_eq_image {a b : ℝ} (hab : a < b) {m : ℕ} (hm : 0 < m)
    (V : Set C(Set.Icc a b, ℝ)) :
    interpSet a b m V = interpMap hab hm '' V := by
  ext w
  constructor
  · rintro ⟨u, huV, hwu⟩
    exact ⟨u, huV, by ext x; exact (hwu x).symm⟩
  · rintro ⟨u, huV, rfl⟩
    exact ⟨u, huV, fun _ => rfl⟩

theorem solution {a b : ℝ} (hab : a < b) (V : Set C(Set.Icc a b, ℝ))
    (hV : IsCompact V) :
    IsCompact (sensorHull a b V) := by
  -- Every interpSet a b m V (for m ≥ 1) is compact
  have hU_comp : ∀ m : ℕ, 1 ≤ m → IsCompact (interpSet a b m V) := by
    intro m hm
    rw [interpSet_eq_image hab hm]
    exact hV.image (interpMap_continuous hab hm)
  -- Interpolation error κ(m) → 0
  obtain ⟨κ, hκ_bd, hκ_tend⟩ := interpolation_error_tendsto_zero hab V hV
  -- Step 1: sensorHull a b V has compact closure via Arzela-Ascoli
  have hprecomp : IsCompact (closure (sensorHull a b V)) := by
    rw [arzela_ascoli (Set.Icc a b) isCompact_Icc (sensorHull a b V)]
    have hVcl : IsCompact (closure V) := by rwa [hV.isClosed.closure_eq]
    obtain ⟨⟨M, hMV⟩, _⟩ := (arzela_ascoli (Set.Icc a b) isCompact_Icc V).mp hVcl
    constructor
    · -- Uniform boundedness of sensorHull a b V
      refine ⟨M, ?_⟩
      rintro _ ⟨w, hwW, rfl⟩ x
      simp only [sensorHull, Set.mem_iUnion] at hwW
      obtain ⟨m, hm, hw⟩ := hwW
      rcases hw with hwV | ⟨u, huV, hwu⟩
      · exact hMV w ⟨w, hwV, rfl⟩ x
      · dsimp only
        rw [hwu x]
        apply interp_convex_bound hab hm (evalAt u) M _ x.2
        intro j hj
        have hs := sensor_mem_Icc' hab hm hj
        simp only [evalAt, dif_pos hs]
        exact hMV u ⟨u, huV, rfl⟩ ⟨sensor a b m j, hs⟩
    · -- Equicontinuity of sensorHull a b V
      intro ε hε
      obtain ⟨m₀, hm₀⟩ := Metric.tendsto_atTop.mp hκ_tend (ε / 4) (by positivity)
      -- F = V ∪ ⋃_{i ∈ [1, m₀]} interpSet a b i V is a finite union of compact sets, hence compact
      let F : Set C(Set.Icc a b, ℝ) := V ∪ ⋃ i ∈ Finset.Icc 1 m₀, interpSet a b i V
      have hF_comp : IsCompact F :=
        hV.union <| (Finset.finite_toSet _).isCompact_biUnion fun i hi =>
          hU_comp i (Finset.mem_Icc.mp hi).1
      have hF_cl : IsCompact (closure F) := by rwa [hF_comp.isClosed.closure_eq]
      obtain ⟨_, hFeq⟩ := (arzela_ascoli (Set.Icc a b) isCompact_Icc F).mp hF_cl
      obtain ⟨δ, hδpos, hδ⟩ := hFeq (ε / 2) (half_pos hε)
      refine ⟨δ, hδpos, ?_⟩
      rintro _ ⟨w, hwW, rfl⟩ x y hxy
      simp only [sensorHull, Set.mem_iUnion] at hwW
      obtain ⟨m, hm, hw⟩ := hwW
      rcases hw with hwV | ⟨u, huV, hwu⟩
      · have h1 := hδ w ⟨w, Or.inl hwV, rfl⟩ x y hxy
        linarith
      · by_cases hmm₀ : m ≤ m₀
        · have hwF : w ∈ F := Or.inr <| Set.mem_biUnion (Finset.mem_Icc.mpr ⟨hm, hmm₀⟩) ⟨u, huV, hwu⟩
          have h1 := hδ w ⟨w, hwF, rfl⟩ x y hxy
          linarith
        · push Not at hmm₀
          have hκm : κ m < ε / 4 := by
            have := hm₀ m hmm₀.le
            rw [Real.dist_eq, sub_zero] at this
            exact (le_abs_self _).trans_lt this
          have hwx : |u x - w x| ≤ κ m := by
            rw [hwu x]
            simpa [evalAt, dif_pos x.2] using hκ_bd m hm u huV x.1 x.2
          have hwy : |u y - w y| ≤ κ m := by
            rw [hwu y]
            simpa [evalAt, dif_pos y.2] using hκ_bd m hm u huV y.1 y.2
          have huv : |u x - u y| < ε / 2 := hδ u ⟨u, Or.inl huV, rfl⟩ x y hxy
          calc |w x - w y|
              = |(w x - u x) + (u x - u y) + (u y - w y)| := by ring_nf
            _ ≤ |w x - u x| + |u x - u y| + |u y - w y| := by
                linarith [abs_add_le (w x - u x + (u x - u y)) (u y - w y),
                  abs_add_le (w x - u x) (u x - u y)]
            _ = |u x - w x| + |u x - u y| + |u y - w y| := by rw [abs_sub_comm (w x) (u x)]
            _ < ε / 4 + ε / 2 + ε / 4 := by linarith
            _ = ε := by ring
  -- Step 2: sensorHull a b V is closed (sequentially closed in a metric space)
  have hclosed : IsClosed (sensorHull a b V) := by
    rw [← isSeqClosed_iff_isClosed]
    intro seq w₀ hseq htend
    by_cases hbdd : ∃ M : ℕ, ∀ᶠ n in atTop, seq n ∈ V ∪ ⋃ i ∈ Finset.Icc 1 M, interpSet a b i V
    · obtain ⟨M, hM⟩ := hbdd
      let FM : Set C(Set.Icc a b, ℝ) := V ∪ ⋃ i ∈ Finset.Icc 1 M, interpSet a b i V
      have hFM_comp : IsCompact FM :=
        hV.union <| (Finset.finite_toSet _).isCompact_biUnion fun i hi =>
          hU_comp i (Finset.mem_Icc.mp hi).1
      have hw₀FM : w₀ ∈ FM := hFM_comp.isClosed.mem_of_tendsto htend hM
      rcases hw₀FM with hw₀V | hw₀U
      · exact Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨le_rfl, Or.inl hw₀V⟩⟩
      · simp only [Set.mem_iUnion] at hw₀U
        obtain ⟨i, hi, hw₀i⟩ := hw₀U
        exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨(Finset.mem_Icc.mp hi).1, Or.inr hw₀i⟩⟩
    · -- Unbounded indices: extract a subsequence with m_k → ∞ and seq (n_k) ∈ U_{m_k}
      -- In fact, directly show w₀ ∈ closure V = V using Metric.mem_closure_iff!
      have hw₀V : w₀ ∈ V := by
        rw [← hV.isClosed.closure_eq, Metric.mem_closure_iff]
        intro ε hε
        obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hκ_tend (ε / 2) (half_pos hε)
        obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htend (ε / 2) (half_pos hε)
        push Not at hbdd
        have hfreq := hbdd M
        rw [Filter.frequently_atTop] at hfreq
        obtain ⟨n, hnN, hnnot⟩ := hfreq N
        have hwn := hseq n
        simp only [sensorHull, Set.mem_iUnion] at hwn
        obtain ⟨m, hm1, hwm⟩ := hwn
        rcases hwm with hwV | ⟨u, huV, hwu⟩
        · exact (hnnot (Or.inl hwV)).elim
        · have hmM : M < m := by
            by_contra hle
            push Not at hle
            exact hnnot (Or.inr <| Set.mem_biUnion (Finset.mem_Icc.mpr ⟨hm1, hle⟩) ⟨u, huV, hwu⟩)
          have hκm : κ m < ε / 2 := by
            have := hM m hmM.le
            rw [Real.dist_eq, sub_zero] at this
            exact (le_abs_self _).trans_lt this
          have hduw : dist u (seq n) < ε / 2 := by
            rw [ContinuousMap.dist_lt_iff (half_pos hε)]
            intro x
            rw [Real.dist_eq, hwu x]
            have h1 : |evalAt u x.1 - interp a b m (evalAt u) x.1| ≤ κ m :=
              hκ_bd m hm1 u huV x.1 x.2
            simp only [evalAt, dif_pos x.2] at h1
            exact h1.trans_lt hκm
          have hdwn : dist (seq n) w₀ < ε / 2 := hN n hnN
          refine ⟨u, huV, ?_⟩
          calc dist w₀ u = dist u w₀ := dist_comm _ _
            _ ≤ dist u (seq n) + dist (seq n) w₀ := dist_triangle _ _ _
            _ < ε / 2 + ε / 2 := add_lt_add hduw hdwn
            _ = ε := add_halves ε
      exact Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨le_rfl, Or.inl hw₀V⟩⟩
  rwa [hclosed.closure_eq] at hprecomp
