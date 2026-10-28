-- Prove2me | solution 1 for FunctionalInequalities.Energy.LocalSlope.exists_patch_of_isCompact_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:03:25.231643+00:00
-- url     : https://prove2.me/submissions/4b75f019-3ad9-4e77-88e0-440791f303cf

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Recovery
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Density
import Theorems.Thm_FunctionalInequalities_Energy_exists_thickening_pairwise_disjoint_readable

section
noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
section
universe u
section Metric
variable {X : Type*} [MetricSpace X]
/-- Every positive radius bounds the asymptotic Lipschitz constant from above. -/
theorem FunctionalInequalities.Energy.AsymptoticLipschitz.apply_le_secant (f : X → ℝ) {r : ℝ} (hr : 0 < r) (x : X) :
    apply f x ≤ secant f r x :=
  iInf_le_of_le r (iInf_le _ hr)
/-- A uniform bound on the secant quotients bounds the secant supremum. -/
theorem FunctionalInequalities.Energy.AsymptoticLipschitz.secant_le_of_forall {f : X → ℝ} {r : ℝ} {x : X} {c : ℝ≥0∞}
    (h : ∀ y z, dist y x < r → dist z x < r →
      ENNReal.ofReal (dist (f y) (f z) / dist y z) ≤ c) :
    secant f r x ≤ c :=
  iSup_le fun y ↦ iSup_le fun hy ↦ iSup_le fun z ↦ iSup_le fun hz ↦ h y z hy hz
/-- A real Lipschitz-type bound on a ball bounds the secant supremum. -/
theorem FunctionalInequalities.Energy.AsymptoticLipschitz.secant_le_ofReal {f : X → ℝ} {r : ℝ} {x : X} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ y z, dist y x < r → dist z x < r → dist (f y) (f z) ≤ c * dist y z) :
    secant f r x ≤ ENNReal.ofReal c := by
  refine secant_le_of_forall fun y z hy hz ↦ ENNReal.ofReal_le_ofReal ?_
  rcases eq_or_lt_of_le (dist_nonneg (x := y) (y := z)) with h0 | h0
  · simp [← h0, hc]
  · exact (div_le_iff₀ h0).2 (h y z hy hz)
end Metric
end
end
end

noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
universe u
section Gluing
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
omit [InnerProductSpace ℝ V] in
/-- Gluing step.  Finitely many pairwise disjoint compact cores, each carrying a Lipschitz
constant `c n ≤ L + α` for `f`, produce one globally Lipschitz patch with constant `9 L + 8 α`:
it agrees with `f` on the cores, differs from `f` by at most `2 L + 2 α` everywhere, and has
asymptotic Lipschitz constant at most `c n` at every point of the `n`-th core. -/
theorem solution {f : V → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) {α : ℝ≥0}
    (N : ℕ) (Kc : ℕ → Set V) (c : ℕ → ℝ≥0) (hcomp : ∀ n, IsCompact (Kc n))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Kc i) (Kc j))
    (hlipK : ∀ n, LipschitzOnWith (c n) f (Kc n)) (hcle : ∀ n, c n ≤ L + α) :
    ∃ F : V → ℝ, LipschitzWith (9 * L + 8 * α) F ∧
      (∀ x, |F x - f x| ≤ 2 * (L : ℝ) + 2 * (α : ℝ)) ∧
      (∀ n < N, ∀ x ∈ Kc n, F x = f x) ∧
      (∀ n < N, ∀ x ∈ Kc n, FunctionalInequalities.Energy.AsymptoticLipschitz.apply F x ≤ (c n : ℝ≥0∞)) := by
  classical
  obtain ⟨ρ₀, hρ₀, hsep₀⟩ := FunctionalInequalities.Energy.exists_thickening_pairwise_disjoint_readable N Kc hcomp hdisj
  set ρ : ℝ := min ρ₀ 1 with hρdef
  have hρ : 0 < ρ := lt_min hρ₀ one_pos
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  have hsep : ∀ i < N, ∀ j < N, i ≠ j →
      Disjoint (Metric.thickening ρ (Kc i)) (Metric.thickening ρ (Kc j)) := fun i hi j hj hij ↦
    Disjoint.mono (Metric.thickening_mono (min_le_left _ _) _)
      (Metric.thickening_mono (min_le_left _ _) _) (hsep₀ i hi j hj hij)
  have hext : ∀ n, ∃ g : V → ℝ, LipschitzWith (c n) g ∧ Set.EqOn f g (Kc n) :=
    fun n ↦ (hlipK n).extend_real
  choose hfun hfunlip hfuneq using hext
  set S : Finset ℕ := (Finset.range N).filter (fun n ↦ (Kc n).Nonempty) with hSdef
  have hSmem : ∀ n ∈ S, n < N ∧ (Kc n).Nonempty := by
    intro n hn
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hn
    exact hn
  set φ : ℕ → V → ℝ := fun n x ↦ max (1 - Metric.infDist x (Kc n) / ρ) 0 with hφdef
  set w : ℕ → V → ℝ := fun n x ↦ hfun n x - f x with hwdef
  set u : ℕ → V → ℝ := fun n x ↦ φ n x * w n x with hudef
  set F : V → ℝ := fun x ↦ f x + ∑ n ∈ S, u n x with hFdef
  -- the cutoffs
  have hφ0 : ∀ n x, 0 ≤ φ n x := fun n x ↦ le_max_right _ _
  have hφ1 : ∀ n x, φ n x ≤ 1 := by
    intro n x
    refine max_le ?_ zero_le_one
    have : 0 ≤ Metric.infDist x (Kc n) / ρ := div_nonneg Metric.infDist_nonneg hρ.le
    linarith
  have hφmem : ∀ n x, x ∈ Kc n → φ n x = 1 := by
    intro n x hx
    simp [hφdef, Metric.infDist_zero_of_mem hx]
  have hφne : ∀ n x, φ n x ≠ 0 → Metric.infDist x (Kc n) < ρ := by
    intro n x hne
    by_contra hcon
    push Not at hcon
    refine hne ?_
    have hle : 1 - Metric.infDist x (Kc n) / ρ ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hρ, one_mul]
      exact hcon
    simp [hφdef, max_eq_right hle]
  have hφlip : ∀ n y z, |φ n y - φ n z| ≤ dist y z / ρ := by
    intro n y z
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    have h : (1 - Metric.infDist y (Kc n) / ρ) - (1 - Metric.infDist z (Kc n) / ρ) =
        (Metric.infDist z (Kc n) - Metric.infDist y (Kc n)) / ρ := by ring
    have hd : |Metric.infDist z (Kc n) - Metric.infDist y (Kc n)| ≤ dist y z := by
      have h2 := (Metric.lipschitz_infDist_pt (Kc n)).dist_le_mul z y
      rw [Real.dist_eq] at h2
      simpa [dist_comm z y] using h2
    rw [h, abs_div, abs_of_pos hρ]
    exact (div_le_div_iff_of_pos_right hρ).mpr hd
  -- the corrections
  have hwlip : ∀ n y z, |w n y - w n z| ≤ ((c n : ℝ) + L) * dist y z := by
    intro n y z
    have h1 : |hfun n y - hfun n z| ≤ (c n : ℝ) * dist y z := by
      simpa [Real.dist_eq] using (hfunlip n).dist_le_mul y z
    have h2 : |f y - f z| ≤ (L : ℝ) * dist y z := by
      simpa [Real.dist_eq] using hf.dist_le_mul y z
    have he : w n y - w n z = (hfun n y - hfun n z) - (f y - f z) := by
      simp only [hwdef]; ring
    rw [he]
    calc |(hfun n y - hfun n z) - (f y - f z)|
        ≤ |hfun n y - hfun n z| + |f y - f z| := abs_sub _ _
      _ ≤ (c n : ℝ) * dist y z + (L : ℝ) * dist y z := add_le_add h1 h2
      _ = ((c n : ℝ) + L) * dist y z := by ring
  have hwabs : ∀ n, (Kc n).Nonempty → ∀ x,
      |w n x| ≤ ((c n : ℝ) + L) * Metric.infDist x (Kc n) := by
    intro n hne x
    obtain ⟨p, hp, hdp⟩ := (hcomp n).exists_infDist_eq_dist hne x
    have h1 : |hfun n x - hfun n p| ≤ (c n : ℝ) * dist x p := by
      simpa [Real.dist_eq] using (hfunlip n).dist_le_mul x p
    have h2 : |f p - f x| ≤ (L : ℝ) * dist x p := by
      have := hf.dist_le_mul p x
      rw [Real.dist_eq, dist_comm p x] at this
      exact this
    have h3 : hfun n p = f p := (hfuneq n hp).symm
    have he : w n x = (hfun n x - hfun n p) + (f p - f x) := by
      simp only [hwdef, h3]; ring
    rw [he, hdp]
    calc |(hfun n x - hfun n p) + (f p - f x)|
        ≤ |hfun n x - hfun n p| + |f p - f x| := abs_add_le _ _
      _ ≤ (c n : ℝ) * dist x p + (L : ℝ) * dist x p := add_le_add h1 h2
      _ = ((c n : ℝ) + L) * dist x p := by ring
  -- the blocks
  have hublock : ∀ n, (Kc n).Nonempty → ∀ y z,
      |u n y - u n z| ≤ 2 * ((c n : ℝ) + L) * dist y z := by
    intro n hne y z
    have hcL : (0 : ℝ) ≤ (c n : ℝ) + L := by positivity
    have key : ∀ y' z' : V, φ n z' ≠ 0 →
        |u n y' - u n z'| ≤ 2 * ((c n : ℝ) + L) * dist y' z' := by
      intro y' z' hz'
      have hdz : Metric.infDist z' (Kc n) < ρ := hφne n z' hz'
      have hwz : |w n z'| ≤ ((c n : ℝ) + L) * ρ :=
        (hwabs n hne z').trans (by nlinarith [Metric.infDist_nonneg (x := z') (s := Kc n)])
      have he : u n y' - u n z' = φ n y' * (w n y' - w n z') + w n z' * (φ n y' - φ n z') := by
        simp only [hudef]; ring
      rw [he]
      have h1 : |φ n y' * (w n y' - w n z')| ≤ ((c n : ℝ) + L) * dist y' z' := by
        rw [abs_mul, abs_of_nonneg (hφ0 n y')]
        calc φ n y' * |w n y' - w n z'| ≤ 1 * (((c n : ℝ) + L) * dist y' z') := by
              apply mul_le_mul (hφ1 n y') (hwlip n y' z') (abs_nonneg _) zero_le_one
          _ = ((c n : ℝ) + L) * dist y' z' := by ring
      have h2 : |w n z' * (φ n y' - φ n z')| ≤ ((c n : ℝ) + L) * dist y' z' := by
        rw [abs_mul]
        calc |w n z'| * |φ n y' - φ n z'| ≤ (((c n : ℝ) + L) * ρ) * (dist y' z' / ρ) := by
              apply mul_le_mul hwz (hφlip n y' z') (abs_nonneg _) (by positivity)
          _ = ((c n : ℝ) + L) * dist y' z' := by field_simp
      calc |φ n y' * (w n y' - w n z') + w n z' * (φ n y' - φ n z')|
          ≤ |φ n y' * (w n y' - w n z')| + |w n z' * (φ n y' - φ n z')| := abs_add_le _ _
        _ ≤ ((c n : ℝ) + L) * dist y' z' + ((c n : ℝ) + L) * dist y' z' := add_le_add h1 h2
        _ = 2 * ((c n : ℝ) + L) * dist y' z' := by ring
    by_cases hz : φ n z = 0
    · by_cases hy : φ n y = 0
      · simp [hudef, hy, hz]
        positivity
      · have := key z y hy
        rw [abs_sub_comm, dist_comm]
        exact this
    · exact key y z hz
  have huabs : ∀ n, (Kc n).Nonempty → ∀ x, |u n x| ≤ ((c n : ℝ) + L) * ρ := by
    intro n hne x
    by_cases hx : φ n x = 0
    · simp [hudef, hx]
      positivity
    · rw [hudef]
      simp only
      rw [abs_mul, abs_of_nonneg (hφ0 n x)]
      calc φ n x * |w n x| ≤ 1 * (((c n : ℝ) + L) * Metric.infDist x (Kc n)) := by
            apply mul_le_mul (hφ1 n x) (hwabs n hne x) (abs_nonneg _) zero_le_one
        _ ≤ ((c n : ℝ) + L) * ρ := by
            have h1 : Metric.infDist x (Kc n) ≤ ρ := (hφne n x hx).le
            have : (0 : ℝ) ≤ (c n : ℝ) + L := by positivity
            nlinarith
  have hcbound : ∀ n, (c n : ℝ) + L ≤ 2 * (L : ℝ) + α := by
    intro n
    have := hcle n
    have : (c n : ℝ) ≤ (L : ℝ) + α := by exact_mod_cast this
    linarith
  -- at most one active block at each point
  have hunique : ∀ x, ∀ n ∈ S, ∀ n' ∈ S, φ n x ≠ 0 → φ n' x ≠ 0 → n = n' := by
    intro x n hn n' hn' hφn hφn'
    by_contra hne
    obtain ⟨hnN, hnne⟩ := hSmem n hn
    obtain ⟨hn'N, hn'ne⟩ := hSmem n' hn'
    have h1 : x ∈ Metric.thickening ρ (Kc n) :=
      (Metric.mem_thickening_iff_infDist_lt hnne).2 (hφne n x hφn)
    have h2 : x ∈ Metric.thickening ρ (Kc n') :=
      (Metric.mem_thickening_iff_infDist_lt hn'ne).2 (hφne n' x hφn')
    exact Set.disjoint_left.1 (hsep n hnN n' hn'N hne) h1 h2
  have hzero : ∀ x, ∀ n ∈ S, u n x ≠ 0 → φ n x ≠ 0 := by
    intro x n _ hu0 hφ0'
    exact hu0 (by simp [hudef, hφ0'])
  have hcardone : ∀ x, ((S.filter fun n ↦ u n x ≠ 0).card ≤ 1) := by
    intro x
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact hunique x a ha.1 b hb.1 (hzero x a ha.1 ha.2) (hzero x b hb.1 hb.2)
  -- the patch is uniformly close to `f`
  have hclose : ∀ x, |F x - f x| ≤ 2 * (L : ℝ) + 2 * (α : ℝ) := by
    intro x
    have hFx : F x - f x = ∑ n ∈ S, u n x := by simp [hFdef]
    rw [hFx, ← Finset.sum_filter_ne_zero S]
    obtain ⟨a, ha⟩ := Finset.card_le_one_iff_subset_singleton.1 (hcardone x)
    rcases Finset.subset_singleton_iff.1 ha with h | h
    · rw [h]
      simp
      positivity
    · rw [h, Finset.sum_singleton]
      have haS : a ∈ S := by
        have : a ∈ S.filter fun n ↦ u n x ≠ 0 := by rw [h]; exact Finset.mem_singleton_self a
        exact (Finset.mem_filter.1 this).1
      have hne := (hSmem a haS).2
      calc |u a x| ≤ ((c a : ℝ) + L) * ρ := huabs a hne x
        _ ≤ (2 * (L : ℝ) + α) * 1 := by
            apply mul_le_mul (hcbound a) hρ1 hρ.le
            positivity
        _ ≤ 2 * (L : ℝ) + 2 * (α : ℝ) := by
            have : (0 : ℝ) ≤ α := α.coe_nonneg
            linarith
  -- the patch is globally Lipschitz
  have hFlip : LipschitzWith (9 * L + 8 * α) F := by
    refine LipschitzWith.of_dist_le_mul fun y z ↦ ?_
    have hcoe : ((9 * L + 8 * α : ℝ≥0) : ℝ) = 9 * (L : ℝ) + 8 * (α : ℝ) := by push_cast; ring
    rw [Real.dist_eq, hcoe]
    have hFyz : F y - F z = (f y - f z) + ∑ n ∈ S, (u n y - u n z) := by
      simp [hFdef, Finset.sum_sub_distrib]
      ring
    have hsumP : ∑ n ∈ S, (u n y - u n z) =
        ∑ n ∈ S.filter (fun n ↦ u n y ≠ 0 ∨ u n z ≠ 0), (u n y - u n z) := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro n hn hnP
      rw [Finset.mem_filter] at hnP
      push Not at hnP
      obtain ⟨h1, h2⟩ := hnP hn
      rw [h1, h2, sub_zero]
    have hPcard : (S.filter (fun n ↦ u n y ≠ 0 ∨ u n z ≠ 0)).card ≤ 2 := by
      have hsub : S.filter (fun n ↦ u n y ≠ 0 ∨ u n z ≠ 0) ⊆
          (S.filter fun n ↦ u n y ≠ 0) ∪ (S.filter fun n ↦ u n z ≠ 0) := by
        intro n hn
        rw [Finset.mem_filter] at hn
        rcases hn.2 with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hn.1, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hn.1, h⟩)
      calc (S.filter (fun n ↦ u n y ≠ 0 ∨ u n z ≠ 0)).card
          ≤ ((S.filter fun n ↦ u n y ≠ 0) ∪ (S.filter fun n ↦ u n z ≠ 0)).card :=
            Finset.card_le_card hsub
        _ ≤ (S.filter fun n ↦ u n y ≠ 0).card + (S.filter fun n ↦ u n z ≠ 0).card :=
            Finset.card_union_le _ _
        _ ≤ 1 + 1 := add_le_add (hcardone y) (hcardone z)
        _ = 2 := rfl
    have hterm : ∀ n ∈ S.filter (fun n ↦ u n y ≠ 0 ∨ u n z ≠ 0),
        |u n y - u n z| ≤ 2 * (2 * (L : ℝ) + α) * dist y z := by
      intro n hn
      have hnS : n ∈ S := (Finset.mem_filter.1 hn).1
      refine (hublock n (hSmem n hnS).2 y z).trans ?_
      have h1 : (c n : ℝ) + L ≤ 2 * (L : ℝ) + α := hcbound n
      nlinarith [dist_nonneg (x := y) (y := z)]
    have hsumbound : |∑ n ∈ S.filter (fun n ↦ u n y ≠ 0 ∨ u n z ≠ 0), (u n y - u n z)| ≤
        2 * (2 * (2 * (L : ℝ) + α) * dist y z) := by
      calc |∑ n ∈ S.filter (fun n ↦ u n y ≠ 0 ∨ u n z ≠ 0), (u n y - u n z)|
          ≤ ∑ n ∈ S.filter (fun n ↦ u n y ≠ 0 ∨ u n z ≠ 0), |u n y - u n z| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ (S.filter (fun n ↦ u n y ≠ 0 ∨ u n z ≠ 0)).card •
              (2 * (2 * (L : ℝ) + α) * dist y z) :=
            Finset.sum_le_card_nsmul _ _ _ hterm
        _ = ((S.filter (fun n ↦ u n y ≠ 0 ∨ u n z ≠ 0)).card : ℝ) *
              (2 * (2 * (L : ℝ) + α) * dist y z) := by
            rw [nsmul_eq_mul]
        _ ≤ 2 * (2 * (2 * (L : ℝ) + α) * dist y z) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast hPcard
    have hf' : |f y - f z| ≤ (L : ℝ) * dist y z := by
      simpa [Real.dist_eq] using hf.dist_le_mul y z
    rw [hFyz, hsumP]
    calc |(f y - f z) + ∑ n ∈ S.filter (fun n ↦ u n y ≠ 0 ∨ u n z ≠ 0), (u n y - u n z)|
        ≤ |f y - f z| + |∑ n ∈ S.filter (fun n ↦ u n y ≠ 0 ∨ u n z ≠ 0), (u n y - u n z)| :=
          abs_add_le _ _
      _ ≤ (L : ℝ) * dist y z + 2 * (2 * (2 * (L : ℝ) + α) * dist y z) :=
          add_le_add hf' hsumbound
      _ ≤ (9 * (L : ℝ) + 8 * (α : ℝ)) * dist y z := by
          have : (0 : ℝ) ≤ dist y z := dist_nonneg
          nlinarith [α.coe_nonneg, L.coe_nonneg]
  -- the patch agrees with `f` on the cores
  have hFeq : ∀ n < N, ∀ x ∈ Kc n, F x = f x := by
    intro n hn x hx
    have hnS : n ∈ S := by
      rw [hSdef, Finset.mem_filter, Finset.mem_range]
      exact ⟨hn, ⟨x, hx⟩⟩
    have hφn : φ n x = 1 := hφmem n x hx
    have hsum : ∑ m ∈ S, u m x = 0 := by
      refine Finset.sum_eq_zero fun m hm ↦ ?_
      by_cases hmn : m = n
      · subst hmn
        have : w m x = 0 := by simp [hwdef, (hfuneq m hx).symm]
        simp [hudef, this]
      · have : φ m x = 0 := by
          by_contra hcon
          exact hmn (hunique x m hm n hnS hcon (by rw [hφn]; norm_num))
        simp [hudef, this]
    simp [hFdef, hsum]
  -- the asymptotic Lipschitz constant on the cores
  have hFslope : ∀ n < N, ∀ x ∈ Kc n, FunctionalInequalities.Energy.AsymptoticLipschitz.apply F x ≤ (c n : ℝ≥0∞) := by
    intro n hn x hx
    have hnS : n ∈ S := by
      rw [hSdef, Finset.mem_filter, Finset.mem_range]
      exact ⟨hn, ⟨x, hx⟩⟩
    have hne : (Kc n).Nonempty := ⟨x, hx⟩
    have hcL : (0 : ℝ) ≤ (c n : ℝ) + L := by positivity
    -- on a ball of radius `r ≤ ρ` around `x` only the `n`-th block is active
    have hlocal : ∀ r : ℝ, 0 < r → r ≤ ρ → ∀ y : V, dist y x < r →
        F y = hfun n y - (Metric.infDist y (Kc n) / ρ) * w n y := by
      intro r hr0 hrρ y hy
      have hdy : Metric.infDist y (Kc n) < ρ := by
        calc Metric.infDist y (Kc n) ≤ dist y x := Metric.infDist_le_dist_of_mem hx
          _ < r := hy
          _ ≤ ρ := hrρ
      have hφy : φ n y = 1 - Metric.infDist y (Kc n) / ρ := by
        refine max_eq_left ?_
        rw [le_sub_comm, sub_zero, div_le_one hρ]
        exact hdy.le
      have hsum : ∑ m ∈ S, u m y = u n y := by
        refine Finset.sum_eq_single_of_mem n hnS fun m hm hmn ↦ ?_
        have : φ m y = 0 := by
          by_contra hcon
          refine hmn (hunique y m hm n hnS hcon ?_)
          rw [hφy]
          intro hzero'
          rw [sub_eq_zero] at hzero'
          rw [eq_comm, div_eq_one_iff_eq hρ.ne'] at hzero'
          exact absurd hzero' hdy.ne
        simp [hudef, this]
      have hfy : f y = hfun n y - w n y := by simp [hwdef]
      rw [hFdef]
      simp only
      rw [hsum, hudef]
      simp only
      rw [hφy, hfy]
      ring
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    have hεr : (0 : ℝ) < (ε : ℝ) := hε
    have hd : (0 : ℝ) < 2 * ((c n : ℝ) + L) + 1 := by positivity
    set t : ℝ := ((ε : ℝ) * ρ) / (2 * ((c n : ℝ) + L) + 1) with htdef
    have ht0 : 0 < t := div_pos (mul_pos hεr hρ) hd
    have hteq : (2 * ((c n : ℝ) + L) + 1) * t = (ε : ℝ) * ρ := by
      rw [htdef]; field_simp
    set r : ℝ := min ρ t with hrdef
    have hr0 : 0 < r := lt_min hρ ht0
    have hrρ : r ≤ ρ := min_le_left _ _
    have hsmall : 2 * r * ((c n : ℝ) + L) / ρ ≤ (ε : ℝ) := by
      have hb : r ≤ t := min_le_right _ _
      rw [div_le_iff₀ hρ]
      nlinarith [mul_le_mul_of_nonneg_right hb hcL, ht0.le, hcL]
    have hball : ∀ y z : V, dist y x < r → dist z x < r →
        dist (F y) (F z) ≤ ((c n : ℝ) + 2 * r * ((c n : ℝ) + L) / ρ) * dist y z := by
      intro y z hy hz
      rw [hlocal r hr0 hrρ y hy, hlocal r hr0 hrρ z hz]
      set θ : V → ℝ := fun v ↦ Metric.infDist v (Kc n) / ρ with hθ
      have hθ0 : ∀ v : V, 0 ≤ θ v := fun v ↦ div_nonneg Metric.infDist_nonneg hρ.le
      have hθy : θ y ≤ r / ρ := by
        show Metric.infDist y (Kc n) / ρ ≤ r / ρ
        exact (div_le_div_iff_of_pos_right hρ).mpr
          ((Metric.infDist_le_dist_of_mem hx).trans hy.le)
      have hθz : θ z ≤ r / ρ := by
        show Metric.infDist z (Kc n) / ρ ≤ r / ρ
        exact (div_le_div_iff_of_pos_right hρ).mpr
          ((Metric.infDist_le_dist_of_mem hx).trans hz.le)
      have hθlip : |θ y - θ z| ≤ dist y z / ρ := by
        show |Metric.infDist y (Kc n) / ρ - Metric.infDist z (Kc n) / ρ| ≤ dist y z / ρ
        rw [div_sub_div_same, abs_div, abs_of_pos hρ]
        have hdd : |Metric.infDist y (Kc n) - Metric.infDist z (Kc n)| ≤ dist y z := by
          have h2 := (Metric.lipschitz_infDist_pt (Kc n)).dist_le_mul y z
          rw [Real.dist_eq] at h2
          simpa using h2
        exact (div_le_div_iff_of_pos_right hρ).mpr hdd
      have hwz : |w n z| ≤ ((c n : ℝ) + L) * r := by
        refine (hwabs n hne z).trans ?_
        apply mul_le_mul_of_nonneg_left _ hcL
        exact (Metric.infDist_le_dist_of_mem hx).trans hz.le
      have he : (hfun n y - θ y * w n y) - (hfun n z - θ z * w n z) =
          (hfun n y - hfun n z) - (θ y * (w n y - w n z) + w n z * (θ y - θ z)) := by ring
      rw [Real.dist_eq, he]
      have h1 : |hfun n y - hfun n z| ≤ (c n : ℝ) * dist y z := by
        simpa [Real.dist_eq] using (hfunlip n).dist_le_mul y z
      have h2 : |θ y * (w n y - w n z)| ≤ (r / ρ) * (((c n : ℝ) + L) * dist y z) := by
        rw [abs_mul, abs_of_nonneg (hθ0 y)]
        exact mul_le_mul hθy (hwlip n y z) (abs_nonneg _) (div_nonneg hr0.le hρ.le)
      have h3 : |w n z * (θ y - θ z)| ≤ (((c n : ℝ) + L) * r) * (dist y z / ρ) := by
        rw [abs_mul]
        exact mul_le_mul hwz hθlip (abs_nonneg _) (mul_nonneg hcL hr0.le)
      calc |(hfun n y - hfun n z) - (θ y * (w n y - w n z) + w n z * (θ y - θ z))|
          ≤ |hfun n y - hfun n z| + |θ y * (w n y - w n z) + w n z * (θ y - θ z)| :=
            abs_sub _ _
        _ ≤ |hfun n y - hfun n z| + (|θ y * (w n y - w n z)| + |w n z * (θ y - θ z)|) := by
            gcongr
            exact abs_add_le _ _
        _ ≤ (c n : ℝ) * dist y z + ((r / ρ) * (((c n : ℝ) + L) * dist y z) +
              (((c n : ℝ) + L) * r) * (dist y z / ρ)) := by
            gcongr
        _ = ((c n : ℝ) + 2 * r * ((c n : ℝ) + L) / ρ) * dist y z := by field_simp; ring
    have hbd := FunctionalInequalities.Energy.AsymptoticLipschitz.secant_le_ofReal
      (f := F) (r := r) (x := x)
      (by positivity : (0 : ℝ) ≤ (c n : ℝ) + 2 * r * ((c n : ℝ) + L) / ρ)
      (fun y z hy hz ↦ hball y z hy hz)
    refine (FunctionalInequalities.Energy.AsymptoticLipschitz.apply_le_secant F hr0 x).trans (hbd.trans ?_)
    rw [← ENNReal.ofReal_coe_nnreal (p := c n), ← ENNReal.ofReal_coe_nnreal (p := ε),
      ← ENNReal.ofReal_add (c n).coe_nonneg ε.coe_nonneg]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith
  exact ⟨F, hFlip, hclose, hFeq, hFslope⟩
