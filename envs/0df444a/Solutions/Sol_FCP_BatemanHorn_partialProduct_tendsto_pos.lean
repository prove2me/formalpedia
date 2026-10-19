-- Prove2me | solution 1 for FCP.BatemanHorn.partialProduct_tendsto_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T06:57:33.966496+00:00
-- url     : https://prove2.me/submissions/2b1c5247-68fe-4099-91b5-3183458c0e41

import Mathlib
import Definitions.Def_FCP_BatemanHorn

set_option autoImplicit false

section BHGeo

section Gwrap


open Metric MeasureTheory Set

namespace BHL

/-- The `r`-thickening of a Lipschitz image of the unit cube `[0,1]^m` inside `ℝ^d`,
`m + 1 ≤ d`, has volume `O(r)` (grid covering by `(⌈1/r⌉+1)^m` balls of radius `O(r)`). -/
theorem vol_cthickening_lipschitz_image {ι ι' : Type} [Fintype ι] [Fintype ι']
    (f : (ι' → ℝ) → (ι → ℝ)) (Lf : NNReal) (hf : LipschitzOnWith Lf f (Icc 0 1))
    (hdim : Fintype.card ι' + 1 ≤ Fintype.card ι) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      volume (cthickening r (f '' Icc 0 1)) ≤ ENNReal.ofReal (K * r) := by
  classical
  set m := Fintype.card ι' with hm
  set d := Fintype.card ι with hd
  refine ⟨3 ^ m * (2 * ((Lf : ℝ) + 2)) ^ d, by positivity, ?_⟩
  intro r hr hr1
  set N : ℕ := ⌈1 / r⌉₊ with hN
  have hNr : 1 / r ≤ N := Nat.le_ceil _
  have hNpos : (0:ℝ) < N := lt_of_lt_of_le (by positivity) hNr
  have hNr' : 1 ≤ (N:ℝ) * r := by
    rw [div_le_iff₀ hr] at hNr; linarith
  let g : (ι' → Fin (N+1)) → (ι' → ℝ) := fun k i => ((k i : ℕ) : ℝ) / N
  have hg : ∀ k, g k ∈ Icc (0 : ι' → ℝ) 1 := by
    intro k
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [Pi.zero_apply, g]; exact div_nonneg (Nat.cast_nonneg _) hNpos.le
    · simp only [Pi.one_apply, g]
      rw [div_le_one hNpos]; exact_mod_cast Nat.lt_succ_iff.1 (k i).2
  have hnear : ∀ u ∈ Icc (0 : ι' → ℝ) 1, ∃ k, dist u (g k) ≤ r := by
    intro u hu
    have hle : ∀ i, u i * N ≤ (N:ℝ) := fun i => mul_le_of_le_one_left hNpos.le (hu.2 i)
    refine ⟨fun i => ⟨⌊u i * N⌋₊, Nat.lt_succ_of_le (Nat.floor_le_of_le (hle i))⟩, ?_⟩
    rw [dist_pi_le_iff hr.le]
    intro i
    have h0 : 0 ≤ u i * N := mul_nonneg (hu.1 i) hNpos.le
    have h1 := Nat.floor_le h0
    have h2 := Nat.lt_floor_add_one (u i * N)
    rw [Real.dist_eq, abs_le]
    simp only [g]
    have ha : (⌊u i * N⌋₊ : ℝ) / N ≤ u i := by rw [div_le_iff₀ hNpos]; exact h1
    have hb : u i - (⌊u i * N⌋₊ : ℝ) / N ≤ 1 / N := by
      rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hNpos]; linarith
    have hc : 1 / (N:ℝ) ≤ r := by rw [div_le_iff₀ hNpos]; linarith
    constructor <;> linarith
  have hcov : cthickening r (f '' Icc 0 1) ⊆
      ⋃ k : ι' → Fin (N+1), closedBall (f (g k)) (((Lf:ℝ) + 2) * r) := by
    intro y hy
    have hy' := cthickening_subset_thickening' (by linarith : 0 < 2 * r) (by linarith) _ hy
    rw [mem_thickening_iff] at hy'
    obtain ⟨_, ⟨u, hu, rfl⟩, hyu⟩ := hy'
    obtain ⟨k, hk⟩ := hnear u hu
    refine mem_iUnion.2 ⟨k, ?_⟩
    rw [mem_closedBall]
    have hL := hf.dist_le_mul u hu (g k) (hg k)
    calc dist y (f (g k)) ≤ dist y (f u) + dist (f u) (f (g k)) := dist_triangle _ _ _
      _ ≤ 2 * r + Lf * r := by
          have h1 := hyu.le
          have h2 := hL.trans (mul_le_mul_of_nonneg_left hk Lf.2)
          linarith
      _ = ((Lf:ℝ) + 2) * r := by ring
  obtain ⟨e, he⟩ : ∃ e, d = m + 1 + e := ⟨d - m - 1, by omega⟩
  have hN3 : ((N:ℝ) + 1) * r ≤ 3 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 1 / r by positivity)
    rw [← hN] at this
    have h1r : 1 / r * r = 1 := by field_simp
    nlinarith
  calc volume (cthickening r (f '' Icc 0 1))
      ≤ volume (⋃ k : ι' → Fin (N+1), closedBall (f (g k)) (((Lf:ℝ) + 2) * r)) :=
        measure_mono hcov
    _ ≤ ∑ k : ι' → Fin (N+1), volume (closedBall (f (g k)) (((Lf:ℝ) + 2) * r)) :=
        measure_iUnion_fintype_le _ _
    _ = ∑ _k : ι' → Fin (N+1), ENNReal.ofReal ((2 * (((Lf:ℝ) + 2) * r)) ^ d) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        exact Real.volume_pi_closedBall _ (by positivity)
    _ = ENNReal.ofReal (((N:ℝ) + 1) ^ m * (2 * (((Lf:ℝ) + 2) * r)) ^ d) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← ENNReal.ofReal_natCast]
        push_cast
        rfl
    _ ≤ ENNReal.ofReal (3 ^ m * (2 * ((Lf : ℝ) + 2)) ^ d * r) := by
        apply ENNReal.ofReal_le_ofReal
        have hre : r ^ e ≤ 1 := pow_le_one₀ hr.le hr1
        calc ((N:ℝ) + 1) ^ m * (2 * (((Lf:ℝ) + 2) * r)) ^ d
            = (((N:ℝ) + 1) * r) ^ m * (2 * ((Lf : ℝ) + 2)) ^ d * (r * r ^ e) := by
              have key : ∀ A B : ℝ, B ^ m * (A * r) ^ d = (B * r) ^ m * A ^ d * (r * r ^ e) := by
                intro A B; rw [he]; ring
              rw [show 2 * (((Lf:ℝ) + 2) * r) = (2 * ((Lf:ℝ) + 2)) * r by ring, key]
          _ ≤ 3 ^ m * (2 * ((Lf : ℝ) + 2)) ^ d * (r * 1) := by
              gcongr
          _ = 3 ^ m * (2 * ((Lf : ℝ) + 2)) ^ d * r := by ring

end BHL

end Gwrap

section LCwrap


open Metric MeasureTheory Set ZSpan Submodule

namespace BHL

section LC

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A segment from a point of `S` to a point outside `S` meets the frontier of `S`. -/
lemma exists_frontier_mem_segment {S : Set E} {a y : E} (ha : a ∈ S) (hy : y ∉ S) :
    ∃ z ∈ frontier S, dist a z ≤ dist a y ∧ dist y z ≤ dist a y := by
  have hc : IsPreconnected (segment ℝ a y) := (convex_segment a y).isPreconnected
  by_contra hne
  have hsub : segment ℝ a y ⊆ interior S ∪ (closure S)ᶜ := by
    intro z hz
    have hzf : z ∉ frontier S := by
      intro hzf
      have h := dist_add_dist_of_mem_segment hz
      exact hne ⟨z, hzf, by linarith [dist_nonneg (x := z) (y := y)],
        by rw [dist_comm y z]; linarith [dist_nonneg (x := a) (y := z)]⟩
    by_cases hzc : z ∈ closure S
    · left
      by_contra hzi
      exact hzf ⟨hzc, hzi⟩
    · right; exact hzc
  have hdisj : Disjoint (interior S) (closure S)ᶜ :=
    Set.disjoint_compl_right_iff_subset.2 interior_subset_closure
  rcases hc.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl hdisj hsub with h | h
  · exact hy (interior_subset (h (right_mem_segment ℝ a y)))
  · exact h (left_mem_segment ℝ a y) (subset_closure ha)

lemma abs_toReal_sub_le {a b c : ENNReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    (h1 : a ≤ b + c) (h2 : b ≤ a + c) : |a.toReal - b.toReal| ≤ c.toReal := by
  have h1' := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hb, hc⟩) h1
  have h2' := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ha, hc⟩) h2
  rw [ENNReal.toReal_add hb hc] at h1'
  rw [ENNReal.toReal_add ha hc] at h2'
  rw [abs_le]; constructor <;> linarith

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- Lattice point count with a boundary error: `#(S ∩ L) · covol L` differs from `μ S`
by at most the measure of the `D`-thickening of the frontier of `S`. -/
theorem card_inter_lattice_error : ∃ D : ℝ, 0 ≤ D ∧ ∀ S : Set E, Bornology.IsBounded S →
    MeasurableSet S →
    |(Nat.card (S ∩ L : Set E) : ℝ) * ZLattice.covolume L μ - μ.real S| ≤
      μ.real (cthickening D (frontier S)) := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let b' := b.ofZLatticeBasis ℝ L
  have hspan : span ℤ (range b') = L := b.ofZLatticeBasis_span ℝ
  obtain ⟨D, hD⟩ := isBounded_iff_forall_norm_le.1 (fundamentalDomain_isBounded b')
  refine ⟨max D 0, le_max_right _ _, fun S hSb hSm => ?_⟩
  set F0 := fundamentalDomain b' with hF0
  have hF0m : MeasurableSet F0 := fundamentalDomain_measurableSet b'
  let fl : E → E := fun x => (floor b' x : E)
  have hfl_mem : ∀ x, fl x ∈ L := fun x => hspan ▸ (floor b' x).2
  have hfract : ∀ x, x - fl x ∈ F0 := fun x => fract_mem_fundamentalDomain b' x
  have hfl_iff : ∀ x, ∀ l ∈ L, (fl x = l ↔ x - l ∈ F0) := by
    intro x l hl
    constructor
    · rintro rfl; exact hfract x
    · intro h
      have h1 : fract b' (x - l) = x - l := fract_eq_self.2 h
      have h2 : fract b' (x - l) = fract b' x := by
        rw [fract_eq_fract]
        simpa [hspan] using hl
      have h3 : fract b' x = x - fl x := fract_apply b' x
      have : x - l = x - fl x := by rw [← h1, h2, h3]
      exact (sub_right_injective this).symm
  -- finiteness
  have hL : IsClosed (L : Set E) := @AddSubgroup.isClosed_of_discrete _ _ _ _ _
    L.toAddSubgroup (inferInstanceAs (DiscreteTopology L))
  have hfin : (S ∩ (L : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hSb hL
  set T := hfin.toFinset with hT
  set U : Set E := ⋃ l ∈ T, (fun x => x + (-l)) ⁻¹' F0 with hU
  have hUeq : ∀ x, x ∈ U ↔ fl x ∈ S := by
    intro x
    simp only [hU, mem_iUnion, mem_preimage, hT, Set.Finite.mem_toFinset, mem_inter_iff,
      SetLike.mem_coe, exists_prop, ← sub_eq_add_neg]
    constructor
    · rintro ⟨l, ⟨hlS, hlL⟩, hx⟩
      rw [(hfl_iff x l hlL).2 hx]; exact hlS
    · intro h
      exact ⟨fl x, ⟨h, hfl_mem x⟩, hfract x⟩
  have hUm : MeasurableSet U := by
    refine Finset.measurableSet_biUnion _ fun l _ => ?_
    exact hF0m.preimage (measurable_add_const _)
  have hvolF0 : ZLattice.covolume L μ = μ.real F0 :=
    ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain b μ)
  have hF0fin : μ F0 ≠ ⊤ := (fundamentalDomain_isBounded b').measure_lt_top.ne
  have hμU : μ U = T.card * μ F0 := by
    rw [hU, measure_biUnion_finset]
    · rw [Finset.sum_congr rfl (fun l _ => measure_preimage_add_right μ (-l) F0),
        Finset.sum_const, nsmul_eq_mul]
    · intro l hl l' hl' hne
      refine Set.disjoint_left.2 fun x hx hx' => hne ?_
      simp only [hT, Set.Finite.coe_toFinset, mem_inter_iff, SetLike.mem_coe] at hl hl'
      simp only [mem_preimage, ← sub_eq_add_neg] at hx hx'
      rw [← (hfl_iff x l hl.2).2 hx, ← (hfl_iff x l' hl'.2).2 hx']
    · exact fun l _ => hF0m.preimage (measurable_add_const _)
  have hcard : (Nat.card (S ∩ L : Set E) : ℝ) = T.card := by
    rw [hT, Nat.card_eq_card_finite_toFinset hfin]
  -- the two differences lie in the thickening
  set C := cthickening (max D 0) (frontier S) with hC
  have hfr : ∀ x, ‖x - fl x‖ ≤ max D 0 := fun x => (hD _ (hfract x)).trans (le_max_left _ _)
  have hUS : U \ S ⊆ C := by
    intro x ⟨hxU, hxS⟩
    rw [hUeq] at hxU
    obtain ⟨z, hz, -, h2⟩ := exists_frontier_mem_segment hxU hxS
    refine mem_cthickening_of_dist_le x z _ _ hz (h2.trans ?_)
    rw [dist_comm, dist_eq_norm]; exact hfr x
  have hSU : S \ U ⊆ C := by
    intro x ⟨hxS, hxU⟩
    rw [hUeq] at hxU
    obtain ⟨z, hz, h1, -⟩ := exists_frontier_mem_segment hxS hxU
    refine mem_cthickening_of_dist_le x z _ _ hz (h1.trans ?_)
    rw [dist_eq_norm]; exact hfr x
  have hCfin : μ C ≠ ⊤ := (hSb.closure.subset frontier_subset_closure).cthickening.measure_lt_top.ne
  have hSfin : μ S ≠ ⊤ := hSb.measure_lt_top.ne
  have hUfin : μ U ≠ ⊤ := by
    rw [hμU]; exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hF0fin
  have h1 : μ U ≤ μ S + μ C := by
    calc μ U ≤ μ S + μ (U \ S) := by
          rw [← measure_union disjoint_sdiff_right (hUm.diff hSm)]
          exact measure_mono (fun x hx => by by_cases h : x ∈ S <;> simp [h, hx])
      _ ≤ μ S + μ C := by gcongr
  have h2 : μ S ≤ μ U + μ C := by
    calc μ S ≤ μ U + μ (S \ U) := by
          rw [← measure_union disjoint_sdiff_right (hSm.diff hUm)]
          exact measure_mono (fun x hx => by by_cases h : x ∈ U <;> simp [h, hx])
      _ ≤ μ U + μ C := by gcongr
  have key := abs_toReal_sub_le hUfin hSfin hCfin h1 h2
  rw [hcard, hvolF0]
  have : μ.real U = T.card * μ.real F0 := by
    rw [measureReal_def, hμU, ENNReal.toReal_mul, ENNReal.toReal_natCast, measureReal_def]
  rw [← this]
  exact key

end LC

end BHL

end LCwrap

section BHZsec

open Metric MeasureTheory Set Finset Module NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding NumberField.Units dirichletUnitTheorem
  NumberField.mixedEmbedding.fundamentalCone

open scoped Classical

namespace BHZ

variable (K : Type) [Field K] [NumberField K]

lemma dist_normAtAllPlaces_le (x y : mixedSpace K) :
    dist (normAtAllPlaces x) (normAtAllPlaces y) ≤ dist x y := by
  rw [dist_pi_le_iff dist_nonneg]
  intro w
  rw [normAtAllPlaces_apply, normAtAllPlaces_apply, Real.dist_eq, dist_eq_norm]
  have h1 := normAtPlace_add_le w (x - y) y
  have h2 := normAtPlace_add_le w (y - x) x
  rw [sub_add_cancel] at h1 h2
  have h3 : normAtPlace w (y - x) = normAtPlace w (x - y) := by rw [← normAtPlace_neg, neg_sub]
  have h4 : normAtPlace w (x - y) ≤ ‖x - y‖ := by
    rw [norm_eq_sup'_normAtPlace]
    exact Finset.le_sup' (fun w => normAtPlace w (x - y)) (Finset.mem_univ w)
  rw [abs_le]; constructor <;> linarith

lemma cthickening_preimage_subset (Z : Set (realSpace K)) (r : ℝ) :
    cthickening r (normAtAllPlaces ⁻¹' Z) ⊆ normAtAllPlaces ⁻¹' cthickening r Z := by
  intro x hx
  rw [mem_cthickening_iff] at hx
  rw [Set.mem_preimage, mem_cthickening_iff]
  refine le_trans ?_ hx
  rw [le_infEDist]
  intro y hy
  calc infEDist (normAtAllPlaces x) Z
      ≤ edist (normAtAllPlaces x) (normAtAllPlaces y) := infEDist_le_edist_of_mem hy
    _ ≤ edist x y := by
      rw [edist_dist, edist_dist]
      exact ENNReal.ofReal_le_ofReal (dist_normAtAllPlaces_le K x y)

lemma frontier_normLeOne_subset :
    frontier (normLeOne K) ⊆
      normAtAllPlaces ⁻¹' (compactSet K \ expMapBasis '' interior (paramSet K)) := by
  intro x ⟨hc, hi⟩
  exact ⟨closure_normLeOne_subset K hc, fun h => hi (subset_interior_normLeOne K h)⟩

open scoped Classical in
/-- Extend a vector on the places `≠ w₀` by `0` at `w₀`. -/
noncomputable def ext (u : {w : InfinitePlace K // w ≠ w₀} → ℝ) : realSpace K :=
  fun w => if h : w = w₀ then 0 else u ⟨w, h⟩

/-- The boundary pieces of `compactSet K`, each parametrised by the unit cube. -/
noncomputable def face : Option (Option ({w : InfinitePlace K // w ≠ w₀} × Bool)) →
    ({w : InfinitePlace K // w ≠ w₀} → ℝ) → realSpace K
  | none => fun _ => 0
  | some none => fun u => expMapBasis (ext K u)
  | some (some (i, b)) => fun u =>
      u i • expMapBasis (ext K (Function.update u i (if b then 1 else 0)))

lemma contDiff_ext : ContDiff ℝ 1 (ext K) := by
  classical
  refine contDiff_pi.2 fun w => ?_
  by_cases h : w = w₀
  · have : (fun u => ext K u w) = fun _ => (0:ℝ) := by
      funext u; simp only [ext, dif_pos h]
    rw [this]; exact contDiff_const
  · have : (fun u => ext K u w) = fun u => u ⟨w, h⟩ := by
      funext u; simp only [ext, dif_neg h]
    rw [this]; exact contDiff_apply ℝ ℝ _

lemma contDiff_expMapBasis : ContDiff ℝ 1 (fun x : realSpace K => expMapBasis x) := by
  have : (fun x : realSpace K => expMapBasis x) = fun x => fun w =>
      Real.exp ((w.mult : ℝ)⁻¹ * ((completeBasis K).equivFunL.symm x) w) := by
    funext x w; rfl
  rw [this]
  exact contDiff_pi.2 fun w => Real.contDiff_exp.comp
    (contDiff_const.mul ((contDiff_apply ℝ ℝ w).comp (completeBasis K).equivFunL.symm.contDiff))

lemma contDiff_update {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (c : ℝ) :
    ContDiff ℝ 1 (fun u : ι → ℝ => Function.update u i c) := by
  refine contDiff_pi.2 fun j => ?_
  by_cases h : j = i
  · subst h
    have : (fun u : ι → ℝ => Function.update u j c j) = fun _ => c := by
      funext u; exact Function.update_self _ _ _
    rw [this]; exact contDiff_const
  · have : (fun u : ι → ℝ => Function.update u i c j) = fun u => u j := by
      funext u; exact Function.update_of_ne h _ _
    rw [this]; exact contDiff_apply ℝ ℝ j

lemma contDiff_face (j : Option (Option ({w : InfinitePlace K // w ≠ w₀} × Bool))) :
    ContDiff ℝ 1 (face K j) := by
  classical
  rcases j with _ | _ | ⟨i, b⟩
  · exact contDiff_const
  · exact (contDiff_expMapBasis K).comp (contDiff_ext K)
  · exact (contDiff_apply ℝ ℝ i).smul
      ((contDiff_expMapBasis K).comp ((contDiff_ext K).comp (contDiff_update i _)))

lemma face_lipschitz (j : Option (Option ({w : InfinitePlace K // w ≠ w₀} × Bool))) :
    ∃ L, LipschitzOnWith L (face K j) (Icc 0 1) :=
  (contDiff_face K j).contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_Icc 0 1) isCompact_Icc

lemma Z_subset : compactSet K \ expMapBasis '' interior (paramSet K) ⊆
    ⋃ j, face K j '' Icc 0 1 := by
  classical
  rintro x ⟨hx, hxi⟩
  obtain ⟨c, hc, _, ⟨v, hv, rfl⟩, rfl⟩ := hx
  have hv0 : v w₀ = 0 := by simpa using hv w₀ (mem_univ _)
  have hvw : ∀ w, w ≠ w₀ → v w ∈ Icc (0:ℝ) 1 := fun w hw => by
    simpa [hw] using hv w (mem_univ _)
  set u : {w : InfinitePlace K // w ≠ w₀} → ℝ := fun i => v i with hu_def
  have hu : u ∈ Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 :=
    ⟨fun i => (hvw i i.2).1, fun i => (hvw i i.2).2⟩
  have hext : ext K u = v := by
    funext w
    by_cases h : w = w₀
    · simp only [ext, dif_pos h]; rw [h, hv0]
    · simp only [ext, dif_neg h, hu_def]
  rw [mem_iUnion]
  by_cases hc0 : c = 0
  · exact ⟨none, u, hu, by simp [face, hc0]⟩
  by_cases hc1 : c = 1
  · exact ⟨some none, u, hu, by simp [face, hext, hc1]⟩
  by_cases hside : ∃ i : {w : InfinitePlace K // w ≠ w₀}, v i = 0 ∨ v i = 1
  · obtain ⟨i, hi⟩ := hside
    obtain ⟨b, hb⟩ : ∃ b : Bool, (if b then (1:ℝ) else 0) = u i := by
      rcases hi with h | h
      · exact ⟨false, by simp [hu_def, h]⟩
      · exact ⟨true, by simp [hu_def, h]⟩
    have hu' : Function.update u i c ∈ Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 := by
      refine ⟨fun j => ?_, fun j => ?_⟩ <;> by_cases hj : j = i
      · subst hj; simp [hc.1]
      · rw [Function.update_of_ne hj]; exact hu.1 j
      · subst hj; simp [hc.2]
      · rw [Function.update_of_ne hj]; exact hu.2 j
    refine ⟨some (some (i, b)), Function.update u i c, hu', ?_⟩
    simp only [face, Function.update_self, Function.update_idem, hb, Function.update_eq_self, hext]
  · exfalso
    push Not at hside
    have hcpos : 0 < c := lt_of_le_of_ne hc.1 (Ne.symm hc0)
    have hclt : c < 1 := lt_of_le_of_ne hc.2 hc1
    apply hxi
    refine ⟨fun w => if w = w₀ then Real.log c else v w, ?_, ?_⟩
    · rw [interior_paramSet]
      intro w _
      by_cases hw : w = w₀
      · simp only [hw, if_true]; exact Real.log_neg hcpos hclt
      · simp only [hw, if_false]
        exact ⟨lt_of_le_of_ne (hvw w hw).1 (Ne.symm (hside ⟨w, hw⟩).1),
          lt_of_le_of_ne (hvw w hw).2 (hside ⟨w, hw⟩).2⟩
    · rw [expMapBasis_apply'']
      simp only [if_true, Real.exp_log hcpos]
      congr 2
      funext w
      by_cases hw : w = w₀
      · simp only [hw, if_true]; exact hv0.symm
      · simp only [hw, if_false]

/-- The `r`-thickening of the frontier of `normLeOne K` has volume `O(r)`. -/
theorem vol_cthickening_frontier : ∃ A : ℝ, 0 ≤ A ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
    volume (cthickening r (frontier (normLeOne K))) ≤ ENNReal.ofReal (A * r) := by
  have hdim : Fintype.card {w : InfinitePlace K // w ≠ w₀} + 1 ≤ Fintype.card (InfinitePlace K) :=
    Fintype.card_subtype_lt (p := fun w => w ≠ w₀) (x := w₀) (by simp)
  choose Lj hLj using face_lipschitz K
  choose Kj hKj0 hKj using fun j => BHL.vol_cthickening_lipschitz_image (face K j) (Lj j) (hLj j) hdim
  set B : Set (realSpace K) := ⋃ j, face K j '' Icc 0 1 with hB
  have hBb : Bornology.IsBounded B := by
    refine (isCompact_iUnion fun j => ?_).isBounded
    exact isCompact_Icc.image_of_continuousOn (contDiff_face K j).continuous.continuousOn
  obtain ⟨R0, hR0⟩ := isBounded_iff_forall_norm_le.1 (hBb.cthickening (δ := 1))
  set R : ℝ := max R0 0 with hR_def
  have hR : 0 ≤ R := le_max_right _ _
  set a := nrRealPlaces K
  set b := nrComplexPlaces K
  set c0 : ℝ := 2 ^ a * (2 * Real.pi) ^ b * R ^ b with hc0
  have hc0n : 0 ≤ c0 := mul_nonneg (by positivity) (pow_nonneg hR _)
  refine ⟨c0 * ∑ j, 2 * Kj j, mul_nonneg hc0n (Finset.sum_nonneg fun j _ => by
    have := hKj0 j; linarith), fun r hr hr2 => ?_⟩
  set T : Set (realSpace K) := (⋃ j, cthickening (2 * r) (face K j '' Icc 0 1)) ∩
    {x | ∀ w, 0 ≤ x w} with hT
  have hO : IsClosed {x : realSpace K | ∀ w, 0 ≤ x w} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun w => isClosed_le continuous_const (continuous_apply w)
  have hTm : MeasurableSet T :=
    (MeasurableSet.iUnion fun j => isClosed_cthickening.measurableSet).inter hO.measurableSet
  have hsub1 : cthickening r (frontier (normLeOne K)) ⊆ normAtAllPlaces ⁻¹' T := by
    intro x hx
    have hx1 : normAtAllPlaces x ∈ cthickening r B :=
      cthickening_subset_of_subset r (Z_subset K) (cthickening_preimage_subset K _ r
        (cthickening_subset_of_subset r (frontier_normLeOne_subset K) hx))
    have hx2 := cthickening_subset_thickening' (by linarith : 0 < 2 * r) (by linarith) B hx1
    rw [hB, thickening_iUnion, mem_iUnion] at hx2
    obtain ⟨j, hj⟩ := hx2
    exact ⟨mem_iUnion.2 ⟨j, thickening_subset_cthickening _ _ hj⟩,
      fun w => normAtPlace_nonneg w x⟩
  have hTR : ∀ x ∈ T, ∀ w, x w ≤ R := by
    intro x hx w
    obtain ⟨j, hj⟩ := mem_iUnion.1 hx.1
    have hx1 : x ∈ cthickening 1 B :=
      cthickening_mono (by linarith) _ (cthickening_subset_of_subset _
        (subset_iUnion (fun j => face K j '' Icc 0 1) j) hj)
    calc x w ≤ ‖x w‖ := Real.le_norm_self _
      _ ≤ ‖x‖ := norm_le_pi_norm x w
      _ ≤ R0 := hR0 x hx1
      _ ≤ R := le_max_left _ _
  have hS : 0 ≤ ∑ j, Kj j * (2 * r) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hKj0 j) (by linarith)
  calc volume (cthickening r (frontier (normLeOne K)))
      ≤ volume (normAtAllPlaces ⁻¹' T) := measure_mono hsub1
    _ = 2 ^ a * ENNReal.ofReal (2 * Real.pi) ^ b *
          ∫⁻ x in normAtAllPlaces '' (normAtAllPlaces ⁻¹' T),
            ∏ w : {w // IsComplex w}, ENNReal.ofReal (x w.1) :=
        volume_eq_two_pow_mul_two_pi_pow_mul_integral Set.preimage_image_preimage
          (hTm.preimage (continuous_normAtAllPlaces K).measurable)
    _ = 2 ^ a * ENNReal.ofReal (2 * Real.pi) ^ b *
          ∫⁻ x in T, ∏ w : {w // IsComplex w}, ENNReal.ofReal (x w.1) := by
        rw [normAtAllPlaces_image_preimage_of_nonneg (fun x hx => hx.2)]
    _ ≤ 2 ^ a * ENNReal.ofReal (2 * Real.pi) ^ b *
          ∫⁻ _x in T, ENNReal.ofReal R ^ b := by
        refine mul_le_mul_of_nonneg_left (setLIntegral_mono' hTm fun x hx => ?_) zero_le
        have := Finset.prod_le_pow_card (Finset.univ : Finset {w : InfinitePlace K // IsComplex w})
          (fun w => ENNReal.ofReal (x w.1)) (ENNReal.ofReal R)
          (fun w _ => ENNReal.ofReal_le_ofReal (hTR x hx w.1))
        simpa [b, nrComplexPlaces] using this
    _ = 2 ^ a * ENNReal.ofReal (2 * Real.pi) ^ b * (ENNReal.ofReal R ^ b * volume T) := by
        rw [setLIntegral_const]
    _ ≤ 2 ^ a * ENNReal.ofReal (2 * Real.pi) ^ b *
          (ENNReal.ofReal R ^ b * ∑ j, ENNReal.ofReal (Kj j * (2 * r))) := by
        gcongr
        calc volume T ≤ volume (⋃ j, cthickening (2 * r) (face K j '' Icc 0 1)) :=
              measure_mono Set.inter_subset_left
          _ ≤ ∑ j, volume (cthickening (2 * r) (face K j '' Icc 0 1)) :=
              measure_iUnion_fintype_le _ _
          _ ≤ ∑ j, ENNReal.ofReal (Kj j * (2 * r)) :=
              Finset.sum_le_sum fun j _ => hKj j (2 * r) (by linarith) (by linarith)
    _ = ENNReal.ofReal (2 ^ a * (2 * Real.pi) ^ b * (R ^ b * ∑ j, Kj j * (2 * r))) := by
        rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 ^ a * (2 * Real.pi) ^ b),
          ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 ^ a),
          ENNReal.ofReal_mul (pow_nonneg hR b : (0:ℝ) ≤ R ^ b),
          ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hKj0 j) (by linarith)),
          ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ 2 * Real.pi), ENNReal.ofReal_pow hR,
          ENNReal.ofReal_pow (zero_le_two : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    _ = ENNReal.ofReal ((c0 * ∑ j, 2 * Kj j) * r) := by
        show _ = ENNReal.ofReal ((2 ^ a * (2 * Real.pi) ^ b * R ^ b * ∑ j, 2 * Kj j) * r)
        congr 1
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring

end BHZ

end BHZsec

section BHAsec

open Metric MeasureTheory Set Ideal NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone NumberField.Units Submodule

open scoped Classical Pointwise nonZeroDivisors

namespace BHA

lemma cthickening_smul_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ)
    (hc : 0 < c) (D : ℝ) (hD : 0 < D) (F : Set E) :
    cthickening D (c • F) ⊆ c • cthickening (2 * D / c) F := by
  intro x hx
  have hx' := cthickening_subset_thickening' (by linarith : 0 < 2 * D) (by linarith) _ hx
  obtain ⟨z, hz, hd⟩ := mem_thickening_iff.1 hx'
  obtain ⟨f, hf, rfl⟩ := Set.mem_smul_set.1 hz
  refine Set.mem_smul_set.2 ⟨c⁻¹ • x, ?_, smul_inv_smul₀ hc.ne' x⟩
  refine thickening_subset_cthickening _ _ (mem_thickening_iff.2 ⟨f, hf, ?_⟩)
  have h1 : dist (c⁻¹ • x) f = c⁻¹ * dist x (c • f) := by
    have := dist_smul₀ c⁻¹ x (c • f)
    rw [inv_smul_smul₀ hc.ne', Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc)] at this
    exact this
  rw [h1, div_eq_inv_mul]
  exact mul_lt_mul_of_pos_left hd (inv_pos.2 hc)

variable (K : Type) [Field K] [NumberField K]

/-- Lattice points of a full lattice in the cone `{x ∈ fundamentalCone | norm x ≤ t}`:
power-saving error term. -/
theorem lattice_count_cone (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    ∃ E0 : ℝ, 0 ≤ E0 ∧ ∀ t : ℝ, 1 ≤ t →
      |(Nat.card ({x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ t} ∩
          (L : Set (mixedSpace K)) : Set (mixedSpace K)) : ℝ) * ZLattice.covolume L -
        t * volume.real (normLeOne K)| ≤
        E0 * t ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
  obtain ⟨D, hD0, hLC⟩ := BHL.card_inter_lattice_error (volume : Measure (mixedSpace K)) L
  obtain ⟨A, hA0, hA⟩ := BHZ.vol_cthickening_frontier K
  set n := Module.finrank ℚ K with hn
  have hn1 : 1 ≤ n := Module.finrank_pos
  have hdim : Module.finrank ℝ (mixedSpace K) = n := mixedEmbedding.finrank K
  set D' := max D 1 with hD'
  have hD'pos : 0 < D' := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨R1, hR1⟩ := isBounded_iff_forall_norm_le.1 (isBounded_normLeOne K).closure
  set R := max R1 0 with hR_def
  have hR : 0 ≤ R := le_max_right _ _
  set V0 := volume.real (closedBall (0 : mixedSpace K) (4 * D' * R + D')) with hV0
  have hV0n : 0 ≤ V0 := measureReal_nonneg
  have hE0 : 0 ≤ 2 * A * D' + V0 := by
    have := mul_nonneg (mul_nonneg zero_le_two hA0) hD'pos.le; linarith
  refine ⟨2 * A * D' + V0, hE0, fun t ht => ?_⟩
  have htpos : 0 < t := by linarith
  set c := t ^ ((n:ℝ)⁻¹) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos htpos _
  have hc1 : 1 ≤ c := Real.one_le_rpow ht (by positivity)
  have hcn : c ^ n = t := Real.rpow_inv_natCast_pow htpos.le (by omega)
  have hcn1 : c ^ (n - 1) = t ^ (1 - 1 / (n:ℝ)) := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul htpos.le, Nat.cast_sub hn1]
    congr 1
    have : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
    simp
  have hS : {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ t} = c • normLeOne K := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_smul_set_iff_inv_smul_mem₀ hcpos.ne', mem_normLeOne,
      smul_mem_iff_mem (inv_ne_zero hcpos.ne'), mixedEmbedding.norm_smul,
      abs_of_pos (inv_pos.2 hcpos), inv_pow, ← hn, hcn, inv_mul_le_iff₀ htpos, mul_one]
  have hSb : Bornology.IsBounded (c • normLeOne K) := (isBounded_normLeOne K).smul₀ c
  have hSm : MeasurableSet (c • normLeOne K) := (measurableSet_normLeOne K).const_smul₀ c
  have h1 := hLC _ hSb hSm
  have hvol : volume.real (c • normLeOne K) = t * volume.real (normLeOne K) := by
    rw [measureReal_def, Measure.addHaar_smul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), hdim, abs_of_pos (pow_pos hcpos _), hcn,
      measureReal_def]
  rw [hS, ← hvol]
  refine h1.trans ?_
  have hfr : frontier (c • normLeOne K) = c • frontier (normLeOne K) := by
    have h := (Homeomorph.smulOfNeZero c hcpos.ne').image_frontier (normLeOne K)
    change (fun x => c • x) '' frontier (normLeOne K) =
      frontier ((fun x => c • x) '' normLeOne K) at h
    rw [Set.image_smul, Set.image_smul] at h
    exact h.symm
  rw [hfr]
  have hFb : Bornology.IsBounded (c • frontier (normLeOne K)) :=
    ((isBounded_normLeOne K).closure.subset frontier_subset_closure).smul₀ c
  have hthick : volume.real (cthickening D (c • frontier (normLeOne K))) ≤
      volume.real (cthickening D' (c • frontier (normLeOne K))) :=
    measureReal_mono (cthickening_mono (le_max_left _ _) _) hFb.cthickening.measure_lt_top.ne
  refine hthick.trans ?_
  rw [← hcn1]
  have hpow1 : 1 ≤ c ^ (n - 1) := one_le_pow₀ hc1
  by_cases hbig : 2 * D' / c ≤ 1 / 2
  · have hsub := cthickening_smul_subset c hcpos D' hD'pos (frontier (normLeOne K))
    have hρ : 0 < 2 * D' / c := div_pos (by linarith) hcpos
    have hv : volume (c • cthickening (2 * D' / c) (frontier (normLeOne K))) ≤
        ENNReal.ofReal (c ^ n * (A * (2 * D' / c))) := by
      rw [Measure.addHaar_smul, hdim, abs_of_pos (pow_pos hcpos _),
        ENNReal.ofReal_mul (pow_pos hcpos _).le]
      exact mul_le_mul_of_nonneg_left (hA _ hρ hbig) zero_le
    have hval : c ^ n * (A * (2 * D' / c)) = 2 * A * D' * c ^ (n - 1) := by
      have : c ^ n = c * c ^ (n - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [this]; field_simp
    have hnn : 0 ≤ c ^ n * (A * (2 * D' / c)) :=
      mul_nonneg (pow_pos hcpos _).le (mul_nonneg hA0 hρ.le)
    calc volume.real (cthickening D' (c • frontier (normLeOne K)))
        ≤ c ^ n * (A * (2 * D' / c)) :=
          ENNReal.toReal_le_of_le_ofReal hnn ((measure_mono hsub).trans hv)
      _ = 2 * A * D' * c ^ (n - 1) := hval
      _ ≤ (2 * A * D' + V0) * c ^ (n - 1) := by
          have := pow_pos hcpos (n - 1); nlinarith
  · push Not at hbig
    have hc4 : c < 4 * D' := by
      rw [lt_div_iff₀ hcpos] at hbig; linarith
    have hsub : cthickening D' (c • frontier (normLeOne K)) ⊆
        closedBall (0 : mixedSpace K) (4 * D' * R + D') := by
      have h2 : c • frontier (normLeOne K) ⊆ closedBall (0 : mixedSpace K) (4 * D' * R) := by
        intro y hy
        obtain ⟨f, hf, rfl⟩ := Set.mem_smul_set.1 hy
        rw [mem_closedBall, dist_zero_right, _root_.norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
        have hf1 : ‖f‖ ≤ R := (hR1 f (frontier_subset_closure hf)).trans (le_max_left _ _)
        calc c * ‖f‖ ≤ c * R := mul_le_mul_of_nonneg_left hf1 hcpos.le
          _ ≤ 4 * D' * R := mul_le_mul_of_nonneg_right hc4.le hR
      refine (cthickening_subset_of_subset _ h2).trans ?_
      rw [cthickening_closedBall hD'pos.le (by positivity), add_comm]
    calc volume.real (cthickening D' (c • frontier (normLeOne K))) ≤ V0 :=
          measureReal_mono hsub measure_closedBall_lt_top.ne
      _ ≤ V0 * c ^ (n - 1) := le_mul_of_one_le_right hV0n hpow1
      _ ≤ (2 * A * D' + V0) * c ^ (n - 1) := by
          have := mul_nonneg (mul_nonneg zero_le_two hA0) hD'pos.le
          have := pow_pos hcpos (n - 1); nlinarith

/-- Copy of Mathlib's private `tendsto_norm_le_and_mk_eq_div_atTop_aux₁`. -/
theorem card_class_eq {C : ClassGroup (𝓞 K)} {J : (Ideal (𝓞 K))⁰} (hJ : ClassGroup.mk0 J = C⁻¹)
    (s : ℝ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C}
      = Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
        absNorm (I : Ideal (𝓞 K)) ≤ s * absNorm (J : Ideal (𝓞 K))} := by
  simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
  refine Nat.card_congr ?_
  refine ((Equiv.dvd J).subtypeEquiv fun I ↦ ?_).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : (Ideal (𝓞 K))⁰ ↦ J ∣ I) _)
  rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem _)]
  simp_rw [Equiv.dvd_apply, Submonoid.coe_mul, ← Submonoid.mul_def, _root_.map_mul, hJ,
    inv_mul_eq_one, Nat.cast_mul, mul_comm s, eq_comm, and_comm, and_congr_left_iff]
  exact fun _ ↦
    (mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors J))).symm

theorem class_count (C : ClassGroup (𝓞 K)) : ∃ κ C' : ℝ, 0 < κ ∧ ∀ s : ℝ, 1 ≤ s →
    |(Nat.card {I : (Ideal (𝓞 K))⁰ //
        absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C} : ℝ) - κ * s| ≤
      C' * s ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C⁻¹
  set L := mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J) with hL
  obtain ⟨E0, hE00, hE0⟩ := lattice_count_cone K L
  set NJ : ℝ := (absNorm (J : Ideal (𝓞 K)) : ℝ) with hNJ_def
  have hNJ : 1 ≤ NJ := Nat.one_le_cast.2 (absNorm_pos_of_nonZeroDivisors J)
  set w : ℝ := (torsionOrder K : ℝ) with hw_def
  have hw : 0 < w := Nat.cast_pos.2 (Nat.pos_of_ne_zero (torsionOrder_ne_zero K))
  set cv := ZLattice.covolume L with hcv_def
  have hcv : 0 < cv := ZLattice.covolume_pos L volume
  set V := volume.real (normLeOne K) with hV_def
  have hV : 0 < V := by
    rw [hV_def, measureReal_def, volume_normLeOne]
    refine ENNReal.toReal_pos ?_ ?_
    · refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ ?_)) ?_
      · exact ENNReal.coe_ne_zero.2 NNReal.pi_pos.ne'
      · exact (ENNReal.ofReal_pos.2 (regulator_pos K)).ne'
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
        (ENNReal.pow_ne_top ENNReal.coe_ne_top)) ENNReal.ofReal_ne_top
  set e := 1 - 1 / (Module.finrank ℚ K : ℝ) with he
  refine ⟨V * NJ / (w * cv), E0 * NJ ^ e / (w * cv), by positivity, fun s hs => ?_⟩
  set N := (Nat.card {I : (Ideal (𝓞 K))⁰ //
        absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C} : ℝ) with hN_def
  have hequiv : {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ s * NJ} ≃
      (({x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ s * NJ} ∩
          (L : Set (mixedSpace K)) : Set (mixedSpace K))) :=
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun x => x ∈ idealSet K J)
      (fun x => mixedEmbedding.norm x ≤ s * NJ)).trans (Equiv.subtypeEquivRight fun x => by
        simp only [idealSet, Set.mem_inter_iff, Set.mem_ofPred_eq, SetLike.mem_coe, hL]
        tauto)
  have hcount : N * w = (Nat.card (({x | x ∈ fundamentalCone K ∧
      mixedEmbedding.norm x ≤ s * NJ} ∩ (L : Set (mixedSpace K)) : Set (mixedSpace K))) : ℝ) := by
    rw [hN_def, hw_def, card_class_eq K hJ s, ← Nat.card_congr hequiv, ← Nat.cast_mul,
      card_isPrincipal_dvd_norm_le K J (s * NJ)]
  have hb := hE0 (s * NJ) (one_le_mul_of_one_le_of_one_le hs hNJ)
  rw [← hcount] at hb
  have hwc : 0 < w * cv := mul_pos hw hcv
  have hrw : N - V * NJ / (w * cv) * s = (N * w * cv - s * NJ * V) / (w * cv) := by
    field_simp
  rw [hrw, abs_div, abs_of_pos hwc, div_le_iff₀ hwc]
  calc |N * w * cv - s * NJ * V| ≤ E0 * (s * NJ) ^ e := hb
    _ = E0 * NJ ^ e / (w * cv) * s ^ e * (w * cv) := by
        rw [Real.mul_rpow (by linarith) (by linarith)]
        field_simp

theorem idealCountErrorPos : ∃ c C : ℝ, 0 < c ∧ ∀ x : ℝ, 1 ≤ x →
    |(Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ x} : ℝ) - c * x| ≤
      C * x ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
  choose κ Cc hκ hCc using class_count K
  set e := 1 - 1 / (Module.finrank ℚ K : ℝ) with he
  refine ⟨∑ C, κ C, 1 + ∑ C, Cc C, Finset.sum_pos (fun C _ => hκ C) Finset.univ_nonempty,
    fun s hs => ?_⟩
  have hs0 : 0 ≤ s := by linarith
  have he0 : 0 ≤ e := by
    have : (1:ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    rw [he, sub_nonneg, div_le_one (by linarith)]; exact this
  have hse : 1 ≤ s ^ e := Real.one_le_rpow hs he0
  have h0 : (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ s} : ℝ) =
      (Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s} : ℝ) + 1 := by
    have e1 : Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ s} =
        Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ ⌊s⌋₊} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun I => (Nat.le_floor_iff hs0).symm)
    have e2 : Nat.card {I : (Ideal (𝓞 K))⁰ // (absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s} =
        Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ ⌊s⌋₊} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun I => (Nat.le_floor_iff hs0).symm)
    rw [e1, e2, Ideal.card_norm_le_eq_card_norm_le_add_one, Nat.cast_add, Nat.cast_one]
  have h1 : (Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s} : ℝ) =
      ∑ C, (Nat.card {I : (Ideal (𝓞 K))⁰ //
        absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C} : ℝ) := by
    have : Fintype {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s} := by
      simp_rw [← Nat.le_floor_iff hs0]
      refine @Fintype.ofFinite _ (finite_setOfPred_absNorm_le₀ ⌊s⌋₊)
    let e := fun C : ClassGroup (𝓞 K) ↦ Equiv.subtypeSubtypeEquivSubtypeInter
      (fun I : (Ideal (𝓞 K))⁰ ↦ absNorm I.1 ≤ s) (fun I ↦ ClassGroup.mk0 I = C)
    simp_rw [← Nat.card_congr (e _), Nat.card_eq_fintype_card, Fintype.subtype_card]
    rw [Fintype.card, Finset.card_eq_sum_card_fiberwise (f := fun I ↦ ClassGroup.mk0 I.1)
      (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _), Nat.cast_sum]
  rw [h0, h1]
  have hsplit : ∑ C, (Nat.card {I : (Ideal (𝓞 K))⁰ //
        absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C} : ℝ) + 1 - (∑ C, κ C) * s =
      1 + ∑ C, ((Nat.card {I : (Ideal (𝓞 K))⁰ //
        absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C} : ℝ) - κ C * s) := by
    rw [Finset.sum_sub_distrib, Finset.sum_mul]; ring
  rw [hsplit]
  calc |1 + ∑ C, ((Nat.card {I : (Ideal (𝓞 K))⁰ //
        absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C} : ℝ) - κ C * s)|
      ≤ |(1:ℝ)| + |∑ C, ((Nat.card {I : (Ideal (𝓞 K))⁰ //
        absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C} : ℝ) - κ C * s)| := abs_add_le _ _
    _ ≤ 1 + ∑ C, |((Nat.card {I : (Ideal (𝓞 K))⁰ //
        absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C} : ℝ) - κ C * s)| := by
        rw [abs_one]; gcongr; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ 1 + ∑ C, Cc C * s ^ e := by gcongr with C; exact hCc C s hs
    _ ≤ s ^ e + (∑ C, Cc C) * s ^ e := by rw [Finset.sum_mul]; linarith
    _ = (1 + ∑ C, Cc C) * s ^ e := by ring

end BHA

end BHAsec

end BHGeo

open Polynomial Filter Topology Asymptotics FCP.BatemanHorn
open scoped Nat

namespace BHGlue

/-- Roots of `f` modulo the prime `p`, as a finset. -/
noncomputable def rootsMod (f : ℤ[X]) (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  Finset.univ.filter (fun x => (f.map (Int.castRingHom (ZMod p))).eval x = 0)

lemma omegaP_eq_card (polys : Finset ℤ[X]) (p : ℕ) [Fact p.Prime] :
    omegaP polys p = (polys.biUnion (fun f => rootsMod f p)).card := by
  unfold omegaP
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [rootsMod]

lemma omegaP_single (f : ℤ[X]) (p : ℕ) [Fact p.Prime] :
    omegaP {f} p = (rootsMod f p).card := by
  rw [omegaP_eq_card]; simp

lemma omegaP_lt (polys : Finset ℤ[X]) (h_schinzel : SchinzelCondition polys)
    (p : ℕ) [hp : Fact p.Prime] : omegaP polys p < p := by
  obtain ⟨n, hn⟩ := h_schinzel p hp.out
  rw [omegaP_eq_card]
  have hsub : polys.biUnion (fun f => rootsMod f p) ⊆ Finset.univ.erase (n : ZMod p) := by
    intro x hx
    simp only [Finset.mem_biUnion, rootsMod, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨f, hf, hx⟩ := hx
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
    rintro rfl
    rw [eval_intCast_map] at hx
    have : (p : ℤ) ∣ f.eval n := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (by simpa using hx)
    exact hn (this.trans (Finset.dvd_prod_of_mem _ hf))
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card] at h1
  have := hp.out.one_lt
  omega

lemma rootsMod_card_le (f : ℤ[X]) (p : ℕ) [Fact p.Prime]
    (hlc : ¬ (p : ℤ) ∣ f.leadingCoeff) : (rootsMod f p).card ≤ f.natDegree := by
  set F := f.map (Int.castRingHom (ZMod p))
  have hF : F ≠ 0 := by
    intro h0
    apply hlc
    have : F.coeff f.natDegree = 0 := by rw [h0]; simp
    rw [coeff_map] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (by simpa using this)
  have hsub : rootsMod f p ⊆ F.roots.toFinset := by
    intro x hx
    simp only [rootsMod, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp [Multiset.mem_toFinset, mem_roots hF, IsRoot, hx, F]
  calc (rootsMod f p).card ≤ F.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card F.roots := Multiset.toFinset_card_le _
    _ ≤ F.natDegree := card_roots' F
    _ ≤ f.natDegree := natDegree_map_le

lemma rootsMod_disjoint (f g : ℤ[X]) (p : ℕ) [Fact p.Prime] (hdeg : f.natDegree ≠ 0)
    (hres : ¬ (p : ℤ) ∣ resultant f g) : Disjoint (rootsMod f p) (rootsMod g p) := by
  obtain ⟨a, b, -, -, e⟩ := exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl (Or.inl hdeg)
  rw [Finset.disjoint_left]
  intro x hxf hxg
  simp only [rootsMod, Finset.mem_filter, Finset.mem_univ, true_and] at hxf hxg
  have e' := congrArg (fun q : ℤ[X] => (q.map (Int.castRingHom (ZMod p))).eval x) e
  simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, hxf, hxg, zero_mul,
    add_zero, map_C, eval_C] at e'
  apply hres
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (by simpa using e'.symm)

lemma resultant_ne_zero_of_distinct (f g : ℤ[X]) (hf : BunyakovskyCondition f)
    (hg : BunyakovskyCondition g) (hfg : f ≠ g) : resultant f g ≠ 0 := by
  obtain ⟨hlf, hdf, hif⟩ := hf
  obtain ⟨hlg, hdg, hig⟩ := hg
  have hpf : f.IsPrimitive := hif.isPrimitive (by omega)
  have hpg : g.IsPrimitive := hig.isPrimitive (by omega)
  set phiQ := algebraMap ℤ ℚ
  have hFi : Irreducible (f.map phiQ) := (hpf.irreducible_iff_irreducible_map_fraction_map).1 hif
  have hndvd : ¬ (f.map phiQ ∣ g.map phiQ) := by
    intro hd
    have hd' : f ∣ g := (hpf.dvd_iff_fraction_map_dvd_fraction_map (K := ℚ)).2 hd
    obtain ⟨c, hc⟩ := hd'
    have hcu : IsUnit c := by
      rcases hig.isUnit_or_isUnit hc with h | h
      · exact absurd h hif.not_isUnit
      · exact h
    obtain ⟨u, hu, rfl⟩ := Polynomial.isUnit_iff.1 hcu
    have hlc := congrArg leadingCoeff hc
    rw [leadingCoeff_mul, leadingCoeff_C] at hlc
    rcases Int.isUnit_iff.1 hu with rfl | rfl
    · apply hfg; rw [hc]; simp
    · rw [hlc] at hlg; nlinarith
  have hcop : IsCoprime (f.map phiQ) (g.map phiQ) := (hFi.coprime_iff_not_dvd).2 hndvd
  have hne := Polynomial.resultant_ne_zero _ _ hcop
  have hinj : Function.Injective phiQ := RingHom.injective_int phiQ
  rw [show (f.map phiQ).resultant (g.map phiQ) = (f.map phiQ).resultant (g.map phiQ) f.natDegree g.natDegree by
    rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj],
    resultant_map_map] at hne
  intro h0
  exact hne (by rw [h0, map_zero])

lemma log_one_sub_add_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have hx : |x| < 1 := by rw [abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
    div_one] at h
  rw [abs_of_nonneg h0] at h
  have h2 : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg x]
  calc |Real.log (1 - x) + x| = |x + Real.log (1 - x)| := by rw [add_comm]
    _ ≤ x ^ 2 / (1 - x) := h
    _ ≤ 2 * x ^ 2 := h2

/-- The per-prime error: for `2 ≤ p`, `ω ≤ D`, `2 * D ≤ p`,
`|(-k) * log (1 - 1/p) + log (1 - ω/p) + (ω - k)/p| ≤ (2k + 2D²)/p²`. -/
lemma factor_err (k D ω p : ℝ) (hk : 0 ≤ k) (hω0 : 0 ≤ ω) (hωD : ω ≤ D) (hp : 2 ≤ p)
    (hDp : 2 * D ≤ p) :
    |-k * Real.log (1 - 1 / p) + Real.log (1 - ω / p) + (ω - k) / p| ≤
      (2 * k + 2 * D ^ 2) * (p ^ 2)⁻¹ := by
  have hp0 : 0 < p := by linarith
  have e1 := log_one_sub_add_le (1 / p) (by positivity) (by rw [div_le_iff₀ hp0]; linarith)
  have e2 := log_one_sub_add_le (ω / p) (by positivity) (by rw [div_le_iff₀ hp0]; linarith)
  have hrw : -k * Real.log (1 - 1 / p) + Real.log (1 - ω / p) + (ω - k) / p =
      -k * (Real.log (1 - 1 / p) + 1 / p) + (Real.log (1 - ω / p) + ω / p) := by
    field_simp; ring
  rw [hrw]
  have hD0 : 0 ≤ D := le_trans hω0 hωD
  have hωp : (ω / p) ^ 2 ≤ D ^ 2 * (p ^ 2)⁻¹ := by
    rw [div_pow, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hω0 hωD 2) (by positivity)
  calc |-k * (Real.log (1 - 1 / p) + 1 / p) + (Real.log (1 - ω / p) + ω / p)|
      ≤ |-k * (Real.log (1 - 1 / p) + 1 / p)| + |Real.log (1 - ω / p) + ω / p| := abs_add_le _ _
    _ = k * |Real.log (1 - 1 / p) + 1 / p| + |Real.log (1 - ω / p) + ω / p| := by
        rw [abs_mul, abs_neg, abs_of_nonneg hk]
    _ ≤ k * (2 * (1 / p) ^ 2) + 2 * (ω / p) ^ 2 := by gcongr
    _ ≤ (2 * k + 2 * D ^ 2) * (p ^ 2)⁻¹ := by
        rw [one_div, inv_pow]; nlinarith [hωp, inv_nonneg.2 (sq_nonneg p)]

/-- Glue: if for each polynomial the sum `∑_{p<N} (ω_p(f) - 1)/p` converges, the partial
Euler products converge to a positive limit. -/
theorem glue (polys : Finset ℤ[X])
    (h_bunyakovsky : ∀ f ∈ polys, BunyakovskyCondition f)
    (h_schinzel : SchinzelCondition polys)
    (hroot : ∀ f ∈ polys, ∃ L : ℝ, Tendsto (fun N : ℕ =>
        ∑ p ∈ Nat.primesBelow N, ((omegaP {f} p : ℝ) - 1) / p) atTop (𝓝 L)) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (partialProduct polys) atTop (𝓝 C) := by
  classical
  choose! L hL using hroot
  set B : ℤ := ∏ f ∈ polys, (f.leadingCoeff * ∏ g ∈ polys.erase f, resultant f g) with hB
  have hB0 : B ≠ 0 := by
    rw [hB, Finset.prod_ne_zero_iff]
    intro f hf
    refine mul_ne_zero (ne_of_gt (h_bunyakovsky f hf).1) ?_
    rw [Finset.prod_ne_zero_iff]
    intro g hg
    exact resultant_ne_zero_of_distinct f g (h_bunyakovsky f hf)
      (h_bunyakovsky g (Finset.mem_of_mem_erase hg)) (Finset.ne_of_mem_erase hg).symm
  set D : ℕ := ∑ f ∈ polys, f.natDegree with hD
  set P0 : ℕ := B.natAbs + 2 * D + 2 with hP0
  have good : ∀ p : ℕ, p.Prime → P0 ≤ p → ¬ (p : ℤ) ∣ B := by
    intro p hp hle hdvd
    have h1 : p ∣ B.natAbs := Int.natCast_dvd.mp hdvd
    have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hB0) h1
    omega
  have good_lc : ∀ p : ℕ, p.Prime → P0 ≤ p → ∀ f ∈ polys, ¬ (p : ℤ) ∣ f.leadingCoeff := by
    intro p hp hle f hf hd
    exact good p hp hle ((dvd_mul_of_dvd_left hd _).trans (Finset.dvd_prod_of_mem _ hf))
  have good_res : ∀ p : ℕ, p.Prime → P0 ≤ p → ∀ f ∈ polys, ∀ g ∈ polys, f ≠ g →
      ¬ (p : ℤ) ∣ resultant f g := by
    intro p hp hle f hf g hg hfg hd
    refine good p hp hle ((dvd_mul_of_dvd_right ?_ _).trans (Finset.dvd_prod_of_mem _ hf))
    exact hd.trans (Finset.dvd_prod_of_mem _ (Finset.mem_erase.2 ⟨hfg.symm, hg⟩))
  have hsplit : ∀ p : ℕ, p.Prime → P0 ≤ p →
      (omegaP polys p : ℝ) = ∑ f ∈ polys, (omegaP {f} p : ℝ) ∧ (omegaP polys p : ℝ) ≤ D := by
    intro p hp hle
    have := Fact.mk hp
    constructor
    · rw [omegaP_eq_card, Finset.card_biUnion]
      · push_cast
        refine Finset.sum_congr rfl (fun f _ => ?_)
        rw [omegaP_single]
      · intro f hf g hg hfg
        exact rootsMod_disjoint f g p (by have := (h_bunyakovsky f hf).2.1; omega)
          (good_res p hp hle f hf g hg hfg)
    · rw [omegaP_eq_card, hD]
      exact_mod_cast (Finset.card_biUnion_le).trans
        (Finset.sum_le_sum (fun f hf => rootsMod_card_le f p (good_lc p hp hle f hf)))
  set k : ℝ := (polys.card : ℝ) with hk
  have hpos : ∀ p : ℕ, p.Prime → 0 < 1 - (1 : ℝ) / p ∧ 0 < 1 - (omegaP polys p : ℝ) / p := by
    intro p hp
    have := Fact.mk hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hlt : (omegaP polys p : ℝ) < p := by exact_mod_cast omegaP_lt polys h_schinzel p
    constructor
    · rw [sub_pos, div_lt_one hp0]; linarith
    · rw [sub_pos, div_lt_one hp0]; exact hlt
  set X : ℕ → ℝ := fun p => -k * Real.log (1 - 1 / p) + Real.log (1 - (omegaP polys p : ℝ) / p)
    with hX
  have hfac : ∀ p : ℕ, p.Prime →
      (1 - (1 : ℝ) / p) ^ (-polys.card : ℤ) * (1 - (omegaP polys p : ℝ) / p) = Real.exp (X p) := by
    intro p hp
    obtain ⟨h1, h2⟩ := hpos p hp
    rw [hX]
    simp only
    rw [Real.exp_add, Real.exp_log h2, show -k * Real.log (1 - 1 / p) =
      Real.log ((1 - (1 : ℝ) / p) ^ (-polys.card : ℤ)) by rw [Real.log_zpow, hk]; push_cast; ring,
      Real.exp_log (zpow_pos h1 _)]
  set E : ℕ → ℝ := fun n => if n.Prime then
      X n + ∑ f ∈ polys, ((omegaP {f} n : ℝ) - 1) / n else 0 with hE
  set T : ℤ[X] → ℕ → ℝ := fun f N => ∑ p ∈ Nat.primesBelow N, ((omegaP {f} p : ℝ) - 1) / p
    with hT
  have hprod : ∀ N, partialProduct polys N =
      Real.exp (∑ n ∈ Finset.range N, E n - ∑ f ∈ polys, T f N) := by
    intro N
    have hS : ∑ n ∈ Finset.range N, E n =
        ∑ p ∈ Nat.primesBelow N, X p + ∑ f ∈ polys, T f N := by
      rw [hE, ← Finset.sum_filter, ← Nat.primesBelow_eq_filter_range, Finset.sum_add_distrib,
        Finset.sum_comm]
    rw [hS, add_sub_cancel_right, Real.exp_sum]
    unfold partialProduct
    refine Finset.prod_congr rfl (fun p hp => hfac p (Finset.mem_filter.1 hp).2)
  have hEsum : Summable E := by
    refine Summable.of_norm_bounded_eventually_nat (g := fun n : ℕ =>
      (2 * k + 2 * (D : ℝ) ^ 2) * ((n : ℝ) ^ 2)⁻¹)
      ((Real.summable_nat_pow_inv.mpr one_lt_two).mul_left _) ?_
    filter_upwards [eventually_ge_atTop P0] with n hn
    by_cases hnp : n.Prime
    · obtain ⟨hω, hωD⟩ := hsplit n hnp hn
      have hEn : E n = -k * Real.log (1 - 1 / n) + Real.log (1 - (omegaP polys n : ℝ) / n) +
          ((omegaP polys n : ℝ) - k) / n := by
        rw [hE]
        simp only [hnp, if_true]
        rw [hX]
        simp only
        rw [← Finset.sum_div, Finset.sum_sub_distrib, ← hω, Finset.sum_const, nsmul_eq_mul,
          mul_one, hk]
      rw [hEn, Real.norm_eq_abs]
      have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hnp.two_le
      have hDn : 2 * (D : ℝ) ≤ n := by
        have : 2 * D ≤ n := by omega
        exact_mod_cast this
      exact factor_err k D _ n (by positivity) (by positivity) hωD h2 hDn
    · rw [hE]
      simp only [hnp, if_false, norm_zero]
      positivity
  have hlim : Tendsto (fun N => ∑ n ∈ Finset.range N, E n - ∑ f ∈ polys, T f N) atTop
      (𝓝 (∑' n, E n - ∑ f ∈ polys, L f)) :=
    hEsum.hasSum.tendsto_sum_nat.sub (tendsto_finsetSum polys (fun f hf => hL f hf))
  refine ⟨Real.exp (∑' n, E n - ∑ f ∈ polys, L f), Real.exp_pos _, ?_⟩
  have := (Real.continuous_exp.tendsto _).comp hlim
  refine this.congr (fun N => ?_)
  simp only [Function.comp_apply]
  rw [hprod N]



/-- Discrete partial summation: bounded `∑ c n log n` forces `∑ c n` to converge. -/
lemma conv_of_bounded_log_weighted (c : ℕ → ℝ) (hc0 : c 0 = 0) (hc1 : c 1 = 0) (M : ℝ)
    (hM : ∀ N, |∑ n ∈ Finset.range N, c n * Real.log n| ≤ M) :
    ∃ L, Tendsto (fun N => ∑ n ∈ Finset.range N, c n) atTop (𝓝 L) := by
  set w : ℕ → ℝ := fun n => (Real.log (max (n : ℝ) 2))⁻¹ with hw
  set A : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N, c n * Real.log n with hA
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hlogpos : ∀ n : ℕ, 0 < Real.log (max (n : ℝ) 2) :=
    fun n => Real.log_pos (lt_of_lt_of_le (by norm_num) (le_max_right _ _))
  have hw0 : ∀ n, 0 ≤ w n := fun n => inv_nonneg.2 (hlogpos n).le
  have hwanti : ∀ n, w (n + 1) ≤ w n := by
    intro n
    simp only [hw]
    apply inv_anti₀ (hlogpos n)
    apply Real.log_le_log (lt_of_lt_of_le (by norm_num) (le_max_right _ _))
    push_cast
    exact max_le_max (by linarith) le_rfl
  have hcw : ∀ n, w n • (c n * Real.log n) = c n := by
    intro n
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp [hc0, hc1]
    · have hm : max (n : ℝ) 2 = n := max_eq_left (by exact_mod_cast h)
      have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast h)
      simp only [hw, hm, smul_eq_mul]
      field_simp
  have hparts : ∀ N, ∑ n ∈ Finset.range N, c n =
      w (N - 1) * A N - ∑ i ∈ Finset.range (N - 1), (w (i + 1) - w i) * A (i + 1) := by
    intro N
    have := Finset.sum_range_by_parts w (fun n => c n * Real.log n) N
    simp only [smul_eq_mul] at this ⊢
    rw [← this]
    exact Finset.sum_congr rfl (fun n _ => by rw [← smul_eq_mul]; exact (hcw n).symm)
  have hwlim : Tendsto w atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => max (n : ℝ) 2) atTop atTop :=
      tendsto_atTop_mono (fun n => le_max_left _ _) tendsto_natCast_atTop_atTop
    exact (Real.tendsto_log_atTop.comp h1).inv_tendsto_atTop
  have htel : Summable (fun i => w i - w (i + 1)) := by
    refine summable_of_sum_range_le (c := w 0) (fun i => sub_nonneg.2 (hwanti i)) (fun n => ?_)
    rw [Finset.sum_range_sub']
    linarith [hw0 n]
  have hd : Summable (fun i => (w (i + 1) - w i) * A (i + 1)) := by
    refine Summable.of_norm_bounded_eventually_nat (htel.mul_left M)
      (Filter.Eventually.of_forall (fun i => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hwanti i)), mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _) (sub_nonneg.2 (hwanti i))
  have hfirst : Tendsto (fun N => w (N - 1) * A N) atTop (𝓝 0) := by
    have hw1 : Tendsto (fun N => w (N - 1)) atTop (𝓝 0) := hwlim.comp (tendsto_sub_atTop_nat 1)
    refine squeeze_zero_norm (a := fun N => M * w (N - 1)) (fun N => ?_) (by simpa using hw1.const_mul M)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hM N) (hw0 _)
  have hsecond : Tendsto (fun N => ∑ i ∈ Finset.range (N - 1), (w (i + 1) - w i) * A (i + 1))
      atTop (𝓝 (∑' i, (w (i + 1) - w i) * A (i + 1))) :=
    hd.hasSum.tendsto_sum_nat.comp (tendsto_sub_atTop_nat 1)
  refine ⟨0 - ∑' i, (w (i + 1) - w i) * A (i + 1), ?_⟩
  exact (hfirst.sub hsecond).congr (fun N => (hparts N).symm)

/-- Root-sum convergence from a Nagell-type estimate for `f` and Mertens' estimate. -/
lemma rootSum_conv (f : ℤ[X])
    (H1 : ∃ M, ∀ N : ℕ, |∑ p ∈ Nat.primesBelow N, (omegaP {f} p : ℝ) * Real.log p / p
      - Real.log N| ≤ M)
    (H2 : ∃ M, ∀ N : ℕ, |∑ p ∈ Nat.primesBelow N, Real.log p / p - Real.log N| ≤ M) :
    ∃ L : ℝ, Tendsto (fun N : ℕ =>
        ∑ p ∈ Nat.primesBelow N, ((omegaP {f} p : ℝ) - 1) / p) atTop (𝓝 L) := by
  obtain ⟨M1, hM1⟩ := H1
  obtain ⟨M2, hM2⟩ := H2
  set c : ℕ → ℝ := fun n => if n.Prime then ((omegaP {f} n : ℝ) - 1) / n else 0 with hc
  have hsum : ∀ N, ∑ n ∈ Finset.range N, c n =
      ∑ p ∈ Nat.primesBelow N, ((omegaP {f} p : ℝ) - 1) / p := by
    intro N
    rw [hc, ← Finset.sum_filter, ← Nat.primesBelow_eq_filter_range]
  obtain ⟨L, hL⟩ := conv_of_bounded_log_weighted c (by simp [hc, Nat.not_prime_zero])
    (by simp [hc, Nat.not_prime_one]) (M1 + M2) (fun N => by
      have hrw : ∑ n ∈ Finset.range N, c n * Real.log n =
          (∑ p ∈ Nat.primesBelow N, (omegaP {f} p : ℝ) * Real.log p / p - Real.log N) -
          (∑ p ∈ Nat.primesBelow N, Real.log p / p - Real.log N) := by
        rw [sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib, Nat.primesBelow_eq_filter_range,
          Finset.sum_filter]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        by_cases hn : n.Prime
        · simp only [hc, hn, if_true]; ring
        · simp only [hc, hn, if_false, zero_mul]
      rw [hrw]
      exact (abs_sub _ _).trans (add_le_add (hM1 N) (hM2 N)))
  exact ⟨L, hL.congr hsum⟩



lemma log_factorial_eq_sum (n : ℕ) : Real.log ((n ! : ℕ) : ℝ) =
    ∑ p ∈ Nat.primesLE n, ((n !).factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    exact Nat.mem_primesLE.2 ⟨(Nat.Prime.dvd_factorial hpp).1 hd, hpp⟩
  · intro p _; simp

lemma fact_val_ge (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n) : n / p ≤ (n !).factorization p := by
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p n))]
  have h1 : 1 ∈ Finset.Ico 1 (Nat.log p n + 1) := by
    have := Nat.log_pos hp.one_lt hpn
    simp only [Finset.mem_Ico]; omega
  have := Finset.single_le_sum (f := fun i => n / p ^ i) (fun i _ => Nat.zero_le _) h1
  simpa using this

lemma real_div_sub_one_le (n p : ℕ) (hp : 0 < p) : (n : ℝ) / p - 1 ≤ ((n / p : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := n) hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h' : (n : ℝ) < ((n / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
  rw [sub_le_iff_le_add, div_le_iff₀ hp']
  nlinarith

lemma log_div_bound (p : ℕ) (hp : 2 ≤ p) :
    Real.log p / (p * (p - 1)) ≤ 4 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  have hx : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hx0 : (0 : ℝ) < p := by linarith
  have hl := Real.log_le_rpow_div hx0.le (show (0 : ℝ) < 1 / 2 by norm_num)
  set a := (p : ℝ) ^ (1 / 2 : ℝ)
  set b := (p : ℝ) ^ (3 / 2 : ℝ)
  have ha : 0 < a := Real.rpow_pos_of_pos hx0 _
  have hb : 0 < b := Real.rpow_pos_of_pos hx0 _
  have hab : a * b = (p : ℝ) ^ 2 := by
    rw [← Real.rpow_add hx0]; norm_num
  have hl' : Real.log p ≤ 2 * a := by
    rw [show a / (1 / 2 : ℝ) = 2 * a by ring] at hl; exact hl
  rw [div_le_iff₀ (by nlinarith), mul_comm 4, mul_assoc, inv_mul_eq_div]
  rw [le_div_iff₀ hb]
  nlinarith

/-- Mertens' first theorem in the form needed: `∑_{p ≤ n} log p / p = log n + O(1)`. -/
lemma mertens_le (n : ℕ) (hn : 1 ≤ n) :
    |∑ p ∈ Nat.primesLE n, Real.log p / p - Real.log n| ≤
      1 + 4 * (∑' m : ℕ, ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹) + Real.log 4 := by
  set S := ∑ p ∈ Nat.primesLE n, Real.log p / p with hS
  set K := ∑' m : ℕ, ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹ with hK
  have hsum : Summable (fun m : ℕ => ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.2 (by norm_num)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmem : ∀ p ∈ Nat.primesLE n, p.Prime ∧ p ≤ n := fun p hp =>
    ⟨(Nat.mem_primesLE.1 hp).2, (Nat.mem_primesLE.1 hp).1⟩
  have hlogp : ∀ p ∈ Nat.primesLE n, 0 ≤ Real.log p := fun p hp =>
    Real.log_nonneg (by exact_mod_cast (hmem p hp).1.one_lt.le)
  have hF := log_factorial_eq_sum n
  -- upper bound for log n!
  have hFup : Real.log ((n ! : ℕ) : ℝ) ≤ n * Real.log n := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos n)
    exact_mod_cast Nat.factorial_le_pow n
  have hFlo : n * Real.log n - n ≤ Real.log ((n ! : ℕ) : ℝ) := by
    have := Stirling.le_log_factorial_stirling (n := n) (by omega)
    have h1 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have h2 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    linarith
  have htheta : ∑ p ∈ Nat.primesLE n, Real.log p ≤ Real.log 4 * n := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    exact Chebyshev.theta_le_log4_mul_x hn0.le
  -- lower estimate of log n! by n S - θ
  have hA : (n : ℝ) * S - Real.log 4 * n ≤ Real.log ((n ! : ℕ) : ℝ) := by
    rw [hF, hS, Finset.mul_sum]
    have : ∑ i ∈ Nat.primesLE n, (n : ℝ) * (Real.log i / i) - ∑ p ∈ Nat.primesLE n, Real.log p ≤
        ∑ p ∈ Nat.primesLE n, ((n !).factorization p : ℝ) * Real.log p := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum (fun p hp => ?_)
      obtain ⟨hpp, hpn⟩ := hmem p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have h1 := real_div_sub_one_le n p hpp.pos
      have h2 : ((n / p : ℕ) : ℝ) ≤ ((n !).factorization p : ℝ) := by
        exact_mod_cast fact_val_ge n p hpp hpn
      have : (n : ℝ) * (Real.log p / p) - Real.log p = ((n : ℝ) / p - 1) * Real.log p := by
        field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right (h1.trans h2) (hlogp p hp)
    linarith
  -- upper estimate of log n! by n S + n K'
  have hB : Real.log ((n ! : ℕ) : ℝ) ≤ (n : ℝ) * S + n * (4 * K) := by
    rw [hF, hS, Finset.mul_sum]
    have hK' : ∑ p ∈ Nat.primesLE n, Real.log p / (p * (p - 1)) ≤ 4 * K := by
      calc ∑ p ∈ Nat.primesLE n, Real.log p / (p * (p - 1))
          ≤ ∑ p ∈ Nat.primesLE n, 4 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
            Finset.sum_le_sum (fun p hp => log_div_bound p (hmem p hp).1.two_le)
        _ = 4 * ∑ p ∈ Nat.primesLE n, ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by rw [Finset.mul_sum]
        _ ≤ 4 * K := by
            gcongr
            exact hsum.sum_le_tsum _ (fun i _ => by positivity)
    have : ∑ p ∈ Nat.primesLE n, ((n !).factorization p : ℝ) * Real.log p ≤
        ∑ i ∈ Nat.primesLE n, (n : ℝ) * (Real.log i / i) +
          n * ∑ p ∈ Nat.primesLE n, Real.log p / (p * (p - 1)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun p hp => ?_)
      obtain ⟨hpp, hpn⟩ := hmem p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      have h1 : ((n !).factorization p : ℝ) ≤ (n : ℝ) / (p - 1) := by
        have := Nat.factorization_factorial_le_div_pred hpp n
        have h3 : ((n / (p - 1) : ℕ) : ℝ) ≤ (n : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
        rw [Nat.cast_sub hpp.one_le, Nat.cast_one] at h3
        exact (by exact_mod_cast this : ((n !).factorization p : ℝ) ≤ ((n / (p - 1) : ℕ) : ℝ)).trans h3
      have heq : (n : ℝ) / (p - 1) * Real.log p =
          (n : ℝ) * (Real.log p / p) + n * (Real.log p / (p * (p - 1))) := by
        have : (p : ℝ) - 1 ≠ 0 := by linarith
        have : (p : ℝ) ≠ 0 := by linarith
        field_simp
        ring
      rw [← heq]
      exact mul_le_mul_of_nonneg_right h1 (hlogp p hp)
    have := mul_le_mul_of_nonneg_left hK' hn0.le
    linarith
  have hK0 : 0 ≤ K := tsum_nonneg (fun m => by positivity)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]
  constructor
  · -- S ≥ log n - 1 - 4K
    have : (n : ℝ) * (Real.log n - 1 - 4 * K) ≤ n * S := by nlinarith
    have := le_of_mul_le_mul_left this hn0
    linarith
  · have : (n : ℝ) * S ≤ n * (Real.log n + Real.log 4) := by nlinarith
    have := le_of_mul_le_mul_left this hn0
    linarith

lemma mertens_below : ∃ M, ∀ N : ℕ,
    |∑ p ∈ Nat.primesBelow N, Real.log p / p - Real.log N| ≤ M := by
  refine ⟨1 + 4 * (∑' m : ℕ, ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹) + Real.log 4 + Real.log 2, fun N => ?_⟩
  have hK0 : 0 ≤ ∑' m : ℕ, ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹ := tsum_nonneg (fun m => by positivity)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rcases Nat.lt_or_ge N 2 with h | h
  · interval_cases N <;> simp <;> positivity
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hn : 1 ≤ n := by omega
    have hm := mertens_le n hn
    have hpb : Nat.primesBelow (n + 1) = Nat.primesLE n := rfl
    rw [hpb]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hd1 : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log n := by
      rw [sub_nonneg]; apply Real.log_le_log hn0; push_cast; linarith
    have hd2 : Real.log ((n + 1 : ℕ) : ℝ) - Real.log n ≤ Real.log 2 := by
      rw [← Real.log_div (by positivity) hn0.ne']
      apply Real.log_le_log (by positivity)
      rw [div_le_iff₀ hn0]; push_cast
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [abs_le] at hm ⊢
    constructor <;> linarith [hm.1, hm.2]


/-- The Nagell-Landau estimate (the remaining child): for an irreducible integer polynomial,
`∑_{p<N} ω_p(f) log p / p = log N + O(1)`. -/
def NagellEstimate : Prop := ∀ f : ℤ[X], BunyakovskyCondition f → ∃ M : ℝ, ∀ N : ℕ,
    |∑ p ∈ Nat.primesBelow N, (omegaP {f} p : ℝ) * Real.log p / p - Real.log N| ≤ M

theorem parent_of_nagell (hN : NagellEstimate)
    (polys : Finset ℤ[X]) (h_nonempty : polys.Nonempty)
    (h_bunyakovsky : ∀ f ∈ polys, BunyakovskyCondition f)
    (h_schinzel : SchinzelCondition polys) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (partialProduct polys) atTop (𝓝 C) :=
  glue polys h_bunyakovsky h_schinzel
    (fun f hf => rootSum_conv f (hN f (h_bunyakovsky f hf)) mertens_below)



/-- A1a: ideal counting with a power-saving error term (Landau; Lang ANT Thm VI.3). -/
def IdealCountError : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∃ c C : ℝ, ∀ x : ℝ, 1 ≤ x →
    |(Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I ≤ x} : ℝ) - c * x| ≤
      C * x ^ (1 - 1 / (Module.finrank ℚ K : ℝ))

/-- A1b: Mertens' theorem for number fields restricted to degree-one primes. -/
def MertensDegOne : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∃ M : ℝ, ∀ N : ℕ,
    |∑ p ∈ Nat.primesBelow N,
        (Nat.card {P : Ideal (NumberField.RingOfIntegers K) // P.IsPrime ∧ Ideal.absNorm P = p} : ℝ) * Real.log p / p
      - Real.log N| ≤ M

/-- A2: Dedekind-Kummer link between roots mod p and degree-one primes. -/
def RootsEqDegOnePrimes : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (f : ℤ[X]) (α : K), BunyakovskyCondition f →
    aeval α f = 0 → Module.finrank ℚ K = f.natDegree → ∃ B : ℕ, ∀ p : ℕ, p.Prime → B < p →
      omegaP {f} p = Nat.card {P : Ideal (NumberField.RingOfIntegers K) // P.IsPrime ∧ Ideal.absNorm P = p}

theorem nagell_of (hM : MertensDegOne) (hR : RootsEqDegOnePrimes) : NagellEstimate := by
  intro f hf
  obtain ⟨hlc, hdeg, hirr⟩ := hf
  set F : ℚ[X] := f.map (algebraMap ℤ ℚ) with hF
  have hprim : f.IsPrimitive := hirr.isPrimitive (by omega)
  have hFirr : Irreducible F := (hprim.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).1 hirr
  haveI : Fact (Irreducible F) := ⟨hFirr⟩
  letI : NumberField (AdjoinRoot F) :=
    { to_charZero := inferInstance
      to_finiteDimensional := (AdjoinRoot.powerBasis hFirr.ne_zero).finite }
  have hfin : Module.finrank ℚ (AdjoinRoot F) = f.natDegree := by
    rw [(AdjoinRoot.powerBasis hFirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hF,
      natDegree_map_eq_of_injective (IsFractionRing.injective ℤ ℚ)]
  have hroot : aeval (AdjoinRoot.root F) f = 0 := by
    have hz : algebraMap ℤ (AdjoinRoot F) = (AdjoinRoot.of F).comp (algebraMap ℤ ℚ) :=
      RingHom.ext_int _ _
    rw [aeval_def, hz, ← eval₂_map, ← hF, AdjoinRoot.eval₂_root]
  obtain ⟨B, hB⟩ := hR (AdjoinRoot F) f (AdjoinRoot.root F) ⟨hlc, hdeg, hirr⟩ hroot hfin
  obtain ⟨M, hM⟩ := hM (AdjoinRoot F)
  set c : ℕ → ℝ := fun p =>
    (Nat.card {P : Ideal (NumberField.RingOfIntegers (AdjoinRoot F)) // P.IsPrime ∧ Ideal.absNorm P = p} : ℝ) with hc
  set g : ℕ → ℝ := fun p => ((omegaP {f} p : ℝ) - c p) * Real.log p / p with hg
  refine ⟨M + ∑ p ∈ Finset.range (B + 1), |g p|, fun N => ?_⟩
  have hsplit : ∑ p ∈ Nat.primesBelow N, (omegaP {f} p : ℝ) * Real.log p / p - Real.log N =
      (∑ p ∈ Nat.primesBelow N, c p * Real.log p / p - Real.log N) +
        ∑ p ∈ Nat.primesBelow N, g p := by
    rw [hg]; simp only
    rw [add_comm, ← add_sub_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun p _ => by ring)
  have hgz : ∀ p ∈ Nat.primesBelow N, B < p → g p = 0 := by
    intro p hp hBp
    have hpp := (Nat.mem_primesBelow.1 hp).2
    rw [hg]; simp only
    rw [hB p hpp hBp, hc]; simp
  have htail : |∑ p ∈ Nat.primesBelow N, g p| ≤ ∑ p ∈ Finset.range (B + 1), |g p| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [← Finset.sum_filter_of_ne (p := fun p => p ≤ B) (fun p hp hne => by
      by_contra h; push_neg at h; exact hne (by rw [hgz p hp h, abs_zero]))]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun _ _ _ => abs_nonneg _)
    rw [Finset.mem_range]; have := (Finset.mem_filter.1 hp).2; omega
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add (hM N) htail)


/-- The parent statement, modulo the two remaining children. -/
theorem parent_of_children (hM : MertensDegOne) (hR : RootsEqDegOnePrimes)
    (polys : Finset ℤ[X]) (h_nonempty : polys.Nonempty)
    (h_bunyakovsky : ∀ f ∈ polys, BunyakovskyCondition f)
    (h_schinzel : SchinzelCondition polys) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (partialProduct polys) atTop (𝓝 C) :=
  parent_of_nagell (nagell_of hM hR) polys h_nonempty h_bunyakovsky h_schinzel

end BHGlue

section A2
open Polynomial FCP.BatemanHorn NumberField Ideal UniqueFactorizationMonoid

namespace BHA2

/-- Degree-one primes over `p` are the primes over `p` with inertia degree one. -/
lemma isPrime_absNorm_iff {K : Type} [Field K] [NumberField K] {p : ℕ} [hpf : Fact p.Prime]
    (P : Ideal (𝓞 K)) :
    (P.IsPrime ∧ Ideal.absNorm P = p) ↔
      (P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) ∧ P.inertiaDeg ℤ = 1) := by
  have hp := hpf.out
  have hmax : (span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  constructor
  · rintro ⟨hPr, hN⟩
    have hbot : P ≠ ⊥ := by
      rintro rfl
      rw [Ideal.absNorm_bot] at hN
      exact hp.ne_zero hN.symm
    have hmem : ((p : ℕ) : 𝓞 K) ∈ P := by
      have := Ideal.absNorm_mem P
      rwa [hN] at this
    have hle : span {(p : ℤ)} ≤ P.under ℤ := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P
      simpa using hmem
    have hunder : P.under ℤ = span {(p : ℤ)} :=
      (hmax.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top hle).symm
    haveI : P.LiesOver (span {(p : ℤ)}) := ⟨hunder.symm⟩
    haveI : P.IsMaximal := hPr.isMaximal hbot
    refine ⟨⟨hPr, inferInstance⟩, ?_⟩
    have h1 := Ideal.absNorm_eq_pow_inertiaDeg' (R := 𝓞 K) P hp
    rw [hN] at h1
    have h2 : (span {(p : ℤ)}).inertiaDeg' P = 1 := by
      have := (Nat.pow_right_injective hp.two_le) (h1.symm.trans (pow_one p).symm)
      exact this
    rw [← Ideal.inertiaDeg'_eq_inertiaDeg (span {(p : ℤ)}) P]
    exact h2
  · rintro ⟨⟨hPr, hLO⟩, hdeg⟩
    refine ⟨hPr, ?_⟩
    have hbot : P ≠ ⊥ := by
      rintro rfl
      have := hLO.over
      rw [Ideal.under_bot] at this
      exact (Ideal.span_singleton_eq_bot.not.mpr (by exact_mod_cast hp.ne_zero)) this
    haveI : P.IsMaximal := hPr.isMaximal hbot
    rw [Ideal.absNorm_eq_pow_inertiaDeg' (R := 𝓞 K) P hp,
      Ideal.inertiaDeg'_eq_inertiaDeg (span {(p : ℤ)}) P, hdeg, pow_one]

/-- Monic degree-one factors of `g` over a field correspond to the distinct roots of `g`. -/
lemma card_deg_one_factors {F : Type} [Field F] [DecidableEq F] (g : F[X]) (hg : g ≠ 0) :
    Nat.card {Q : (normalizedFactors g).toFinset // Q.1.natDegree = 1} = g.roots.toFinset.card := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr
    { toFun := fun Q => ⟨-(Q.1.1.coeff 0), ?_⟩
      invFun := fun a => ⟨⟨X - C a.1, ?_⟩, natDegree_X_sub_C a.1⟩
      left_inv := ?_
      right_inv := ?_ }
  · obtain ⟨⟨Q, hQ⟩, hQd⟩ := Q
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hg] at hQ
    have hQe : Q = X - C (-(Q.coeff 0)) := by
      rw [map_neg, sub_neg_eq_add]; exact hQ.2.1.eq_X_add_C hQd
    rw [Multiset.mem_toFinset, mem_roots hg, ← dvd_iff_isRoot, ← hQe]
    exact hQ.2.2
  · obtain ⟨a, ha⟩ := a
    rw [Multiset.mem_toFinset, mem_roots hg, ← dvd_iff_isRoot] at ha
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hg]
    exact ⟨irreducible_X_sub_C a, monic_X_sub_C a, ha⟩
  · rintro ⟨⟨Q, hQ⟩, hQd⟩
    have hQ' := hQ
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hg] at hQ'
    have hQe : Q = X - C (-(Q.coeff 0)) := by
      rw [map_neg, sub_neg_eq_add]; exact hQ'.2.1.eq_X_add_C hQd
    apply Subtype.ext; apply Subtype.ext
    exact hQe.symm
  · rintro ⟨a, ha⟩
    apply Subtype.ext
    simp


section count

variable {K : Type} [Field K] [NumberField K]

lemma card_degOne_eq_roots (θ : 𝓞 K) (p : ℕ) [hpf : Fact p.Prime]
    (hp : ¬ p ∣ RingOfIntegers.exponent θ) :
    Nat.card {P : Ideal (𝓞 K) // P.IsPrime ∧ Ideal.absNorm P = p} =
      ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))).roots.toFinset.card := by
  have hg : (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) ≠ 0 :=
    ((minpoly.monic θ.isIntegral).map _).ne_zero
  rw [← card_deg_one_factors _ hg]
  have e1 : {P : Ideal (𝓞 K) // P.IsPrime ∧ Ideal.absNorm P = p} ≃
      {P : primesOver (span {(p : ℤ)}) (𝓞 K) // (P.1).inertiaDeg ℤ = 1} :=
    { toFun := fun P => ⟨⟨P.1, ((isPrime_absNorm_iff P.1).1 P.2).1⟩,
        ((isPrime_absNorm_iff P.1).1 P.2).2⟩
      invFun := fun P => ⟨P.1.1, (isPrime_absNorm_iff P.1.1).2 ⟨P.1.2, P.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e1]
  refine Nat.card_congr ((Ideal.primesOverSpanEquivMonicFactorsMod hp).subtypeEquiv ?_)
  intro P
  conv_lhs => rw [← (Ideal.primesOverSpanEquivMonicFactorsMod hp).symm_apply_apply P]
  rw [Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp]

lemma omegaP_eq_card_roots (f : ℤ[X]) (p : ℕ) [Fact p.Prime] (hd : 1 ≤ f.natDegree)
    (hlc : (Int.castRingHom (ZMod p)) f.leadingCoeff ≠ 0) :
    omegaP {f} p =
      ((integralNormalization f).map (Int.castRingHom (ZMod p))).roots.toFinset.card := by
  unfold omegaP
  rw [← Set.ncard_coe_finset]
  set ψp := Int.castRingHom (ZMod p) with hψp
  set u := ψp f.leadingCoeff with hu
  have hf0 : f ≠ 0 := by rintro rfl; simp at hd
  have hG : (integralNormalization f).map ψp ≠ 0 :=
    ((monic_integralNormalization hf0).map ψp).ne_zero
  have hkey : ∀ x : ZMod p, ((integralNormalization f).map ψp).eval (u * x) =
      u ^ (f.natDegree - 1) * (f.map ψp).eval x := by
    intro x
    rw [eval_map, eval_map]
    exact integralNormalization_eval₂_leadingCoeff_mul hd ψp x
  have hset : (↑((integralNormalization f).map ψp).roots.toFinset : Set (ZMod p)) =
      (fun x => u * x) '' {n : ZMod p | ∃ g ∈ ({f} : Finset ℤ[X]), (g.map ψp).eval n = 0} := by
    ext a
    rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hG, IsRoot.def]
    simp only [Set.mem_image, Set.mem_setOf_eq, Finset.mem_singleton, exists_eq_left]
    constructor
    · intro ha
      refine ⟨u⁻¹ * a, ?_, by rw [← mul_assoc, mul_inv_cancel₀ hlc, one_mul]⟩
      have := hkey (u⁻¹ * a)
      rw [← mul_assoc, mul_inv_cancel₀ hlc, one_mul, ha] at this
      exact (mul_eq_zero.1 this.symm).resolve_left (pow_ne_zero _ hlc)
    · rintro ⟨x, hx, rfl⟩
      rw [hkey, hx, mul_zero]
  rw [hset, Set.ncard_image_of_injective _ (mul_right_injective₀ hlc)]

lemma natDegree_minpoly_smul (f : ℤ[X]) (hf : BunyakovskyCondition f) (α : K)
    (hα : aeval α f = 0) :
    (minpoly ℚ (algebraMap ℤ K f.leadingCoeff * α)).natDegree = f.natDegree := by
  obtain ⟨hlc, hdeg, hirr⟩ := hf
  set F : ℚ[X] := f.map (algebraMap ℤ ℚ) with hF
  have hprim : f.IsPrimitive := hirr.isPrimitive (by omega)
  have hFirr : Irreducible F := (hprim.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).1 hirr
  have hαF : aeval α F = 0 := by rw [hF, aeval_map_algebraMap]; exact hα
  have hmα : (minpoly ℚ α).natDegree = f.natDegree := by
    rw [← minpoly.eq_of_irreducible hFirr hαF, natDegree_mul_C, hF,
      natDegree_map_eq_of_injective (IsFractionRing.injective ℤ ℚ)]
    exact inv_ne_zero (leadingCoeff_ne_zero.2 hFirr.ne_zero)
  have hsm : algebraMap ℤ K f.leadingCoeff * α = ((f.leadingCoeff : ℚ)) • α := by
    rw [Algebra.smul_def]; simp
  have hs : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  rw [hsm, IsIntegrallyClosed.minpoly_smul (by exact_mod_cast hlc.ne') hs, natDegree_scaleRoots,
    hmα]

lemma minpoly_eq_integralNormalization (f : ℤ[X]) (hf : BunyakovskyCondition f) (α : K)
    (hα : aeval α f = 0) (θ : 𝓞 K) (hθ : (θ : K) = algebraMap ℤ K f.leadingCoeff * α) :
    minpoly ℤ θ = integralNormalization f := by
  have hf0 : f ≠ 0 := by rintro rfl; simp [BunyakovskyCondition] at hf
  have hmon := monic_integralNormalization hf0
  have hzK : aeval (θ : K) (integralNormalization f) = 0 := by
    rw [hθ]; exact integralNormalization_aeval_eq_zero hα (fun x hx => by simpa using hx)
  have hz : aeval θ (integralNormalization f) = 0 := by
    have : algebraMap (𝓞 K) K (aeval θ (integralNormalization f)) = 0 := by
      rw [← aeval_algebraMap_apply]; exact hzK
    exact (FaithfulSMul.algebraMap_injective (𝓞 K) K) (this.trans (map_zero _).symm)
  have hdvd : minpoly ℤ θ ∣ integralNormalization f := minpoly.isIntegrallyClosed_dvd θ.isIntegral hz
  have hdeg : (minpoly ℤ θ).natDegree = f.natDegree := by
    rw [← RingOfIntegers.minpoly_coe,
      ← (minpoly.monic (RingOfIntegers.isIntegral_coe θ)).natDegree_map (algebraMap ℤ ℚ),
      ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (RingOfIntegers.isIntegral_coe θ)]
    have : (algebraMap (𝓞 K) K θ) = algebraMap ℤ K f.leadingCoeff * α := hθ
    rw [this, natDegree_minpoly_smul f hf α hα]
  exact (eq_of_monic_of_dvd_of_natDegree_le (p := minpoly ℤ θ) (minpoly.monic θ.isIntegral)
    hmon hdvd ((natDegree_integralNormalization).trans_le hdeg.ge)).symm

lemma exponent_ne_zero' (θ : 𝓞 K)
    (hθ : (minpoly ℚ (θ : K)).natDegree = Module.finrank ℚ K) :
    RingOfIntegers.exponent θ ≠ 0 := by
  have hint : IsIntegral ℚ (θ : K) := Algebra.IsIntegral.isIntegral _
  have htopF : IntermediateField.adjoin ℚ {(θ : K)} = ⊤ := IntermediateField.eq_of_le_of_finrank_eq le_top
      (by rw [IntermediateField.adjoin.finrank hint, IntermediateField.finrank_top', hθ])
  have htop : Algebra.adjoin ℚ {(θ : K)} = ⊤ :=
    (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic hint.isAlgebraic).1 htopF
  set B := PowerBasis.ofAdjoinEqTop hint htop with hB
  have hBgen : B.gen = (θ : K) := PowerBasis.ofAdjoinEqTop_gen hint htop
  have hBint : IsIntegral ℤ B.gen := by rw [hBgen]; exact RingOfIntegers.isIntegral_coe θ
  have hdi : IsIntegral ℤ (Algebra.discr ℚ B.basis) :=
    Algebra.discr_isIntegral ℚ (fun i => by rw [PowerBasis.coe_basis]; exact hBint.pow _)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hdi
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact Algebra.discr_not_zero_of_basis ℚ B.basis (by rw [← hy, map_zero])
  have h1 : ∀ b : 𝓞 K, ((y : ℤ) : 𝓞 K) * b ∈ Algebra.adjoin ℤ {θ} := by
    intro b
    have hm := Algebra.discr_mul_isIntegral_mem_adjoin ℚ (R := ℤ) hBint
      (RingOfIntegers.isIntegral_coe b)
    rw [hBgen, ← hy] at hm
    let ψp := IsScalarTower.toAlgHom ℤ (𝓞 K) K
    have hmap : Algebra.adjoin ℤ {(θ : K)} = (Algebra.adjoin ℤ {θ}).map ψp := by
      rw [AlgHom.map_adjoin, Set.image_singleton]; rfl
    rw [hmap, Subalgebra.mem_map] at hm
    obtain ⟨x, hx, hxe⟩ := hm
    have : x = ((y : ℤ) : 𝓞 K) * b := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [show algebraMap (𝓞 K) K x = ψp x from rfl, hxe, Algebra.smul_def]
      simp
    rw [← this]; exact hx
  have hyc : ((y : ℤ) : 𝓞 K) ∈ conductor ℤ θ := (mem_conductor_iff).2 h1
  have hmc : ((y.natAbs : ℕ) : 𝓞 K) ∈ conductor ℤ θ := by
    have hc : ((y.natAbs : ℕ) : 𝓞 K) = (((y.natAbs : ℤ)) : 𝓞 K) := (Int.cast_natCast _).symm
    rcases Int.natAbs_eq y with h | h
    · rw [hc, ← h]; exact hyc
    · rw [hc, show ((y.natAbs : ℤ)) = -y by omega, Int.cast_neg]; exact neg_mem hyc
  rw [RingOfIntegers.exponent_eq_sInf]
  have hne : ({d : ℕ | 0 < d ∧ (d : 𝓞 K) ∈ conductor ℤ θ}).Nonempty :=
    ⟨y.natAbs, Int.natAbs_pos.2 hy0, hmc⟩
  exact (Nat.sInf_mem hne).1.ne'

end count

theorem rootsEqDegOnePrimes : ∀ (K : Type) [Field K] [NumberField K] (f : ℤ[X]) (α : K),
    BunyakovskyCondition f → aeval α f = 0 → Module.finrank ℚ K = f.natDegree →
      ∃ B : ℕ, ∀ p : ℕ, p.Prime → B < p →
        omegaP {f} p = Nat.card {P : Ideal (𝓞 K) // P.IsPrime ∧ Ideal.absNorm P = p} := by
  intro K _ _ f α hf hα hfin
  have hf0 : f ≠ 0 := by rintro rfl; simp [BunyakovskyCondition] at hf
  have hint : IsIntegral ℤ (algebraMap ℤ K f.leadingCoeff * α) :=
    ⟨_, monic_integralNormalization hf0,
      integralNormalization_aeval_eq_zero hα (fun x hx => by simpa using hx)⟩
  let θ : 𝓞 K := ⟨_, hint⟩
  have hθ : (θ : K) = algebraMap ℤ K f.leadingCoeff * α := rfl
  have hmin := minpoly_eq_integralNormalization f hf α hα θ hθ
  have hexp : RingOfIntegers.exponent θ ≠ 0 :=
    exponent_ne_zero' θ (by rw [hθ, natDegree_minpoly_smul f hf α hα, hfin])
  refine ⟨max (RingOfIntegers.exponent θ) f.leadingCoeff.natAbs, fun p hp hBp => ?_⟩
  haveI := Fact.mk hp
  have hpe : ¬ p ∣ RingOfIntegers.exponent θ := fun h =>
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hexp) h).not_gt (lt_of_le_of_lt (le_max_left _ _) hBp)
  have hlcp : (Int.castRingHom (ZMod p)) f.leadingCoeff ≠ 0 := by
    rw [eq_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h
    have h2 := Int.ofNat_dvd_left.1 h
    exact (Nat.le_of_dvd (Int.natAbs_pos.2 hf.1.ne') h2).not_gt
      (lt_of_le_of_lt (le_max_right _ _) hBp)
  rw [card_degOne_eq_roots θ p hpe, hmin, omegaP_eq_card_roots f p hf.2.1 hlcp]

end BHA2

end A2

/-- The parent statement, modulo the single remaining child `MertensDegOne`. -/
theorem BHGlue.parent_of_mertens (hM : BHGlue.MertensDegOne)
    (polys : Finset ℤ[X]) (h_nonempty : polys.Nonempty)
    (h_bunyakovsky : ∀ f ∈ polys, BunyakovskyCondition f)
    (h_schinzel : SchinzelCondition polys) :
    ∃ C : ℝ, 0 < C ∧ Filter.Tendsto (partialProduct polys) Filter.atTop (nhds C) :=
  BHGlue.parent_of_children hM BHA2.rootsEqDegOnePrimes polys h_nonempty h_bunyakovsky h_schinzel

section MertSec

open Finset

namespace BHMert

lemma rpow_step (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (N : ℕ) :
    δ * ((N : ℝ) + 1) ^ (δ - 1) ≤ ((N : ℝ) + 1) ^ δ - (N : ℝ) ^ δ := by
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hb := rpow_one_add_le_one_add_mul_self (s := -1 / ((N : ℝ) + 1))
    (by rw [neg_div, neg_le_neg_iff, div_le_one hN1]; linarith [(N.cast_nonneg : (0:ℝ) ≤ N)])
    hδ0.le hδ1
  have h1 : 1 + -1 / ((N : ℝ) + 1) = (N : ℝ) / ((N : ℝ) + 1) := by
    field_simp; ring
  rw [h1, Real.div_rpow (N.cast_nonneg) hN1.le] at hb
  have hp : 0 < ((N : ℝ) + 1) ^ δ := Real.rpow_pos_of_pos hN1 δ
  rw [div_le_iff₀ hp] at hb
  have h2 : ((N : ℝ) + 1) ^ (δ - 1) = ((N : ℝ) + 1) ^ δ / ((N : ℝ) + 1) :=
    Real.rpow_sub_one hN1.ne' δ
  rw [h2]
  have : (1 + δ * (-1 / ((N : ℝ) + 1))) * ((N : ℝ) + 1) ^ δ =
      ((N : ℝ) + 1) ^ δ - δ * (((N : ℝ) + 1) ^ δ / ((N : ℝ) + 1)) := by
    field_simp
    ring
  linarith

lemma sum_rpow_le (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (N : ℕ) :
    ∑ d ∈ Icc 1 N, (d : ℝ) ^ (δ - 1) ≤ (N : ℝ) ^ δ / δ := by
  induction N with
  | zero => simp [Real.zero_rpow hδ0.ne']
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega)]
    have := rpow_step δ hδ0 hδ1 N
    push_cast
    rw [le_div_iff₀ hδ0] at ih ⊢
    rw [add_mul]
    nlinarith

/-- Abel's inequality: partial sums of `L` dominated by `B j`, `w` nonincreasing and
nonnegative. -/
lemma abel_ineq (L w : ℕ → ℝ) (B : ℝ) (N : ℕ)
    (hP : ∀ j, j ≤ N → ∑ d ∈ Icc 1 j, L d ≤ B * j)
    (hw : ∀ d, 1 ≤ d → w (d + 1) ≤ w d) (hw0 : ∀ d, 0 ≤ w d) :
    ∑ d ∈ Icc 1 N, L d * w d ≤ B * ∑ d ∈ Icc 1 N, w d := by
  set Q : ℕ → ℝ := fun j => ∑ d ∈ Icc 1 j, (L d - B) with hQ
  have hQle : ∀ j, j ≤ N → Q j ≤ 0 := by
    intro j hj
    simp only [hQ, sum_sub_distrib, sum_const, Nat.card_Icc, nsmul_eq_mul]
    have := hP j hj
    have hc : ((j + 1 - 1 : ℕ) : ℝ) = j := by simp
    rw [hc]; linarith
  have hid : ∀ M : ℕ, ∑ d ∈ Icc 1 M, (L d - B) * w d =
      Q M * w M + ∑ d ∈ Ico 1 M, Q d * (w d - w (d + 1)) := by
    intro M
    induction M with
    | zero => simp [hQ]
    | succ M ih =>
      rw [sum_Icc_succ_top (by omega), ih]
      rcases Nat.eq_zero_or_pos M with rfl | hM
      · simp [hQ]
      · rw [sum_Ico_succ_top (by omega)]
        have hQs : Q (M + 1) = Q M + (L (M + 1) - B) := by
          simp only [hQ]; rw [sum_Icc_succ_top (by omega)]
        rw [hQs]; ring
  have key : ∑ d ∈ Icc 1 N, (L d - B) * w d ≤ 0 := by
    rw [hid N]
    have h1 : Q N * w N ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (hQle N le_rfl) (hw0 N)
    have h2 : ∑ d ∈ Ico 1 N, Q d * (w d - w (d + 1)) ≤ 0 := by
      apply sum_nonpos
      intro d hd
      have hd' : d ≤ N := (Finset.mem_Ico.1 hd).2.le
      exact mul_nonpos_of_nonpos_of_nonneg (hQle d hd') (by linarith [hw d (Finset.mem_Ico.1 hd).1])
    linarith
  have : ∑ d ∈ Icc 1 N, (L d - B) * w d =
      ∑ d ∈ Icc 1 N, L d * w d - B * ∑ d ∈ Icc 1 N, w d := by
    rw [mul_sum, ← sum_sub_distrib]; congr 1; ext d; ring
  linarith

lemma log_sub_le_sum (m N : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) :
    Real.log N - Real.log m ≤ ∑ j ∈ Ico m N, (1 : ℝ) / j := by
  induction N, hmN using Nat.le_induction with
  | base => simp
  | succ N hmN ih =>
    rw [sum_Ico_succ_top hmN]
    have hN : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hm hmN)
    have hstep : Real.log ((N + 1 : ℕ) : ℝ) - Real.log N ≤ 1 / N := by
      rw [← Real.log_div (by positivity) hN.ne']
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
      push_cast; field_simp; ring
    linarith

/-- Abstract Landau-Mertens theorem: from the Dirichlet identity `a·log = L * a`, a power-saving
asymptotic for `∑ a`, and a Chebyshev bound for `L`, one gets `∑_{m≤N} L m / m = log N + O(1)`. -/
theorem absMertens (a L : ℕ → ℝ) (c C B δ : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (ha : ∀ m, 0 ≤ a m) (hL : ∀ m, 0 ≤ L m)
    (hH1 : ∀ m, 1 ≤ m → a m * Real.log m = ∑ d ∈ m.divisors, L d * a (m / d))
    (hH2 : ∀ x : ℝ, 1 ≤ x → |∑ m ∈ Icc 1 ⌊x⌋₊, a m - c * x| ≤ C * x ^ (1 - δ))
    (hH3 : ∀ N : ℕ, ∑ m ∈ Icc 1 N, L m ≤ B * N) :
    ∃ M : ℝ, ∀ N : ℕ, 1 ≤ N → |∑ m ∈ Icc 1 N, L m / m - Real.log N| ≤ M := by
  set A : ℕ → ℝ := fun j => ∑ m ∈ Icc 1 j, a m with hA
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg _).trans (hH2 1 le_rfl)
    rwa [Real.one_rpow, mul_one] at this
  have hAj : ∀ j : ℕ, 1 ≤ j → |A j - c * j| ≤ C * (j : ℝ) ^ (1 - δ) := by
    intro j hj
    have := hH2 (j : ℝ) (by exact_mod_cast hj)
    rwa [Nat.floor_natCast] at this
  have hAle : ∀ j : ℕ, 1 ≤ j → A j ≤ (c + C) * j := by
    intro j hj
    have h1 := (abs_le.1 (hAj j hj)).2
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have h2 : (j : ℝ) ^ (1 - δ) ≤ j := by
      have := Real.rpow_le_rpow_of_exponent_le hj1 (show 1 - δ ≤ 1 by linarith)
      rwa [Real.rpow_one] at this
    nlinarith
  -- Step (a): Dirichlet hyperbola / Fubini.
  have hfub : ∀ N : ℕ, ∑ m ∈ Icc 1 N, a m * Real.log m = ∑ d ∈ Icc 1 N, L d * A (N / d) := by
    intro N
    rw [sum_congr rfl (fun m hm => hH1 m (mem_Icc.1 hm).1)]
    rw [sum_comm' (s' := fun d => (Icc 1 N).filter (fun m => d ∣ m)) (t' := Icc 1 N)]
    · refine sum_congr rfl (fun d hd => ?_)
      have hd1 : 1 ≤ d := (mem_Icc.1 hd).1
      rw [← mul_sum, hA]
      congr 1
      refine sum_nbij' (fun m => m / d) (fun e => e * d) ?_ ?_ ?_ ?_ ?_
      · intro m hm
        simp only [mem_filter, mem_Icc] at hm
        simp only [mem_coe, mem_Icc]
        obtain ⟨⟨hm1, hmN⟩, hdm⟩ := hm
        exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdm) (by omega),
          Nat.div_le_div_right hmN⟩
      · intro e he
        simp only [mem_coe, mem_Icc] at he
        simp only [mem_coe, mem_filter, mem_Icc]
        refine ⟨⟨by nlinarith, (Nat.le_div_iff_mul_le (by omega)).1 he.2⟩, dvd_mul_left d e⟩
      · intro m hm
        simp only [mem_coe, mem_filter] at hm
        exact Nat.div_mul_cancel hm.2
      · intro e _
        exact Nat.mul_div_cancel e (by omega)
      · intro m _; rfl
    · intro m d
      simp only [mem_Icc, Nat.mem_divisors, mem_filter]
      constructor
      · rintro ⟨⟨hm1, hmN⟩, hdm, -⟩
        have := Nat.le_of_dvd (by omega) hdm
        have := Nat.pos_of_dvd_of_pos hdm (by omega)
        exact ⟨⟨⟨hm1, hmN⟩, hdm⟩, by omega, by omega⟩
      · rintro ⟨⟨⟨hm1, hmN⟩, hdm⟩, -, -⟩
        exact ⟨⟨hm1, hmN⟩, hdm, by omega⟩
  -- Step (b): `S N = log N · A N + O(N)`.
  have hS_up : ∀ N : ℕ, ∑ m ∈ Icc 1 N, a m * Real.log m ≤ Real.log N * A N := by
    intro N
    rw [hA, mul_sum]
    refine sum_le_sum (fun m hm => ?_)
    have hm := mem_Icc.1 hm
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right
      (Real.log_le_log (by exact_mod_cast hm.1) (by exact_mod_cast hm.2)) (ha m)
  have hS_lo : ∀ N : ℕ, Real.log N * A N - ∑ m ∈ Icc 1 N, a m * Real.log m ≤ (c + C) * N := by
    intro N
    have e1 : Real.log N * A N - ∑ m ∈ Icc 1 N, a m * Real.log m =
        ∑ m ∈ Icc 1 N, a m * (Real.log N - Real.log m) := by
      rw [hA, mul_sum, ← sum_sub_distrib]; congr 1; ext m; ring
    rw [e1]
    have e2 : ∑ m ∈ Icc 1 N, a m * (Real.log N - Real.log m) ≤
        ∑ m ∈ Icc 1 N, ∑ j ∈ Ico m N, a m * (1 / (j : ℝ)) := by
      refine sum_le_sum (fun m hm => ?_)
      have hm := mem_Icc.1 hm
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (log_sub_le_sum m N hm.1 hm.2) (ha m)
    have e3 : ∑ m ∈ Icc 1 N, ∑ j ∈ Ico m N, a m * (1 / (j : ℝ)) =
        ∑ j ∈ Ico 1 N, ∑ m ∈ Icc 1 j, a m * (1 / (j : ℝ)) := by
      apply sum_comm'
      intro m j
      simp only [mem_Icc, mem_Ico]
      omega
    have e4 : ∑ j ∈ Ico 1 N, ∑ m ∈ Icc 1 j, a m * (1 / (j : ℝ)) ≤ ∑ j ∈ Ico 1 N, (c + C) := by
      refine sum_le_sum (fun j hj => ?_)
      have hj := (mem_Ico.1 hj).1
      have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
      rw [← sum_mul]
      have := hAle j hj
      rw [hA] at this
      rw [mul_one_div, div_le_iff₀ hjpos]
      exact this
    have e5 : ∑ j ∈ Ico 1 N, (c + C) ≤ (c + C) * N := by
      rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact_mod_cast Nat.sub_le N 1
    linarith
  -- Step (c): replace `A (N/d)` by `c N / d`.
  have hT : ∀ N : ℕ, 1 ≤ N → |∑ d ∈ Icc 1 N, L d * A (N / d) -
      c * N * ∑ d ∈ Icc 1 N, L d / d| ≤ C * B * N / δ := by
    intro N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have e1 : ∑ d ∈ Icc 1 N, L d * A (N / d) - c * N * ∑ d ∈ Icc 1 N, L d / d =
        ∑ d ∈ Icc 1 N, L d * (A (N / d) - c * ((N : ℝ) / d)) := by
      rw [mul_sum, ← sum_sub_distrib]; congr 1; ext d; ring
    rw [e1]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have e2 : ∀ d ∈ Icc 1 N, |L d * (A (N / d) - c * ((N : ℝ) / d))| ≤
        C * (N : ℝ) ^ (1 - δ) * (L d * (d : ℝ) ^ (δ - 1)) := by
      intro d hd
      have hd := mem_Icc.1 hd
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hd.1
      have hx : (1 : ℝ) ≤ (N : ℝ) / d := by
        rw [le_div_iff₀ hdpos, one_mul]; exact_mod_cast hd.2
      have h1 := hH2 ((N : ℝ) / d) hx
      rw [Nat.floor_div_eq_div] at h1
      rw [abs_mul, abs_of_nonneg (hL d)]
      have h3 : ((N : ℝ) / d) ^ (1 - δ) = (N : ℝ) ^ (1 - δ) * (d : ℝ) ^ (δ - 1) := by
        rw [Real.div_rpow hNpos.le hdpos.le, div_eq_mul_inv, ← Real.rpow_neg hdpos.le]
        congr 2; ring
      rw [h3] at h1
      calc L d * |A (N / d) - c * ((N : ℝ) / d)|
          ≤ L d * (C * ((N : ℝ) ^ (1 - δ) * (d : ℝ) ^ (δ - 1))) :=
            mul_le_mul_of_nonneg_left h1 (hL d)
        _ = C * (N : ℝ) ^ (1 - δ) * (L d * (d : ℝ) ^ (δ - 1)) := by ring
    refine (sum_le_sum e2).trans ?_
    rw [← mul_sum]
    have hab := abel_ineq L (fun d => (d : ℝ) ^ (δ - 1)) B N (fun j _ => hH3 j)
      (fun d hd => Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hd)
        (by push_cast; linarith) (by linarith))
      (fun d => Real.rpow_nonneg (Nat.cast_nonneg d) _)
    have hsr := sum_rpow_le δ hδ0 hδ1 N
    have hB0 : 0 ≤ B := by
      have := (sum_nonneg (fun m _ => hL m)).trans (hH3 1)
      simpa using this
    have hNr : (N : ℝ) ^ (1 - δ) * (N : ℝ) ^ δ = N := by
      rw [← Real.rpow_add hNpos]; simp
    have hpos : 0 ≤ C * (N : ℝ) ^ (1 - δ) := mul_nonneg hC0 (Real.rpow_nonneg hNpos.le _)
    calc C * (N : ℝ) ^ (1 - δ) * ∑ d ∈ Icc 1 N, L d * (d : ℝ) ^ (δ - 1)
        ≤ C * (N : ℝ) ^ (1 - δ) * (B * ((N : ℝ) ^ δ / δ)) :=
          mul_le_mul_of_nonneg_left (hab.trans (mul_le_mul_of_nonneg_left hsr hB0)) hpos
      _ = C * B * ((N : ℝ) ^ (1 - δ) * (N : ℝ) ^ δ) / δ := by ring
      _ = C * B * N / δ := by rw [hNr]
  -- Step (d): `log N · A N = c N log N + O(N)`.
  have hD : ∀ N : ℕ, 1 ≤ N → |Real.log N * A N - c * N * Real.log N| ≤ C * N / δ := by
    intro N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    have e1 : Real.log N * A N - c * N * Real.log N = Real.log N * (A N - c * N) := by ring
    rw [e1, abs_mul, abs_of_nonneg hlog0]
    have hl := Real.log_le_rpow_div hNpos.le hδ0
    have hNr : (N : ℝ) ^ (1 - δ) * (N : ℝ) ^ δ = N := by
      rw [← Real.rpow_add hNpos]; simp
    calc Real.log N * |A N - c * N| ≤ ((N : ℝ) ^ δ / δ) * (C * (N : ℝ) ^ (1 - δ)) :=
          mul_le_mul hl (hAj N hN) (abs_nonneg _) (by positivity)
      _ = C * ((N : ℝ) ^ (1 - δ) * (N : ℝ) ^ δ) / δ := by ring
      _ = C * N / δ := by rw [hNr]
  -- Combine.
  refine ⟨(C * B / δ + (c + C) + C / δ) / c, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := hT N hN
  have h2 := hS_up N
  have h3 := hS_lo N
  have h4 := hD N hN
  rw [← hfub N] at h1
  set X := ∑ m ∈ Icc 1 N, L m / m with hX
  set S := ∑ m ∈ Icc 1 N, a m * Real.log m with hS
  have hexp : c * N * (X - Real.log N) = -(S - c * N * X) - (Real.log N * A N - S) +
      (Real.log N * A N - c * N * Real.log N) := by ring
  have hK : (C * B / δ + (c + C) + C / δ) * N = C * B * N / δ + (c + C) * N + C * N / δ := by
    ring
  have key : |c * N * (X - Real.log N)| ≤ (C * B / δ + (c + C) + C / δ) * N := by
    rw [hexp, hK]
    rw [abs_le] at h1 h4 ⊢
    constructor
    · linarith [h1.1, h1.2, h4.1, h4.2]
    · linarith [h1.1, h1.2, h4.1, h4.2]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < c * N)] at key
  rw [le_div_iff₀ hc]
  have hN0 : (0 : ℝ) < N := hNpos
  have : |X - Real.log N| * c * N ≤ ((C * B / δ + (c + C) + C / δ)) * N := by linarith
  exact le_of_mul_le_mul_right this hN0

end BHMert
end MertSec

section BSec

open Finset NumberField UniqueFactorizationMonoid

namespace BHB

variable {K : Type} [Field K] [NumberField K]



open scoped Classical

/-- Ideals of norm exactly `m`. -/
noncomputable def Iset (m : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_eq (S := (𝓞 K)) m).toFinset

lemma mem_Iset {m : ℕ} {I : Ideal (𝓞 K)} : I ∈ Iset m ↔ Ideal.absNorm I = m := by
  classical
  simp [Iset]

/-- Nonzero prime ideals of norm at most `d`. -/
noncomputable def PrimeSet (d : ℕ) : Finset (Ideal (𝓞 K)) :=
  ((Ideal.finite_setOfPred_absNorm_le (S := (𝓞 K)) d).toFinset).filter
    (fun P => P.IsPrime ∧ P ≠ ⊥)

lemma mem_PrimeSet {d : ℕ} {P : Ideal (𝓞 K)} :
    P ∈ PrimeSet d ↔ Ideal.absNorm P ≤ d ∧ P.IsPrime ∧ P ≠ ⊥ := by
  classical
  simp [PrimeSet]

/-- Pairs `(P, k)`, `P` a nonzero prime, `k ≥ 1`, with `N(P)^k = d`. -/
noncomputable def Tset (d : ℕ) : Finset ((_ : Ideal (𝓞 K)) × ℕ) :=
  (PrimeSet d).sigma (fun P => (Icc 1 d).filter (fun k => Ideal.absNorm P ^ k = d))

/-- The von Mangoldt-type coefficient of `K`. -/
noncomputable def Lf (d : ℕ) : ℝ := ∑ x ∈ Tset (K := K) d, Real.log (Ideal.absNorm x.1)

lemma two_le_absNorm {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hb : P ≠ ⊥) : 2 ≤ Ideal.absNorm P := by
  have h0 : Ideal.absNorm P ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have h1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.ne_top
  omega

/-- `log N(I) = ∑_{P | I} v_P(I) log N(P)`. -/
lemma log_absNorm_eq (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    Real.log (Ideal.absNorm I) = ∑ P ∈ (normalizedFactors I).toFinset,
      ((normalizedFactors I).count P : ℝ) * Real.log (Ideal.absNorm P) := by
  have hprod : Ideal.absNorm I = ∏ P ∈ (normalizedFactors I).toFinset,
      Ideal.absNorm P ^ (normalizedFactors I).count P := by
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI]
    rw [map_multiset_prod, Finset.prod_multiset_map_count]
  rw [hprod]
  push_cast
  rw [Real.log_prod]
  · refine sum_congr rfl (fun P _ => ?_)
    rw [Real.log_pow]
  · intro P hP
    have hP' := Multiset.mem_toFinset.1 hP
    have hb : P ≠ ⊥ := by
      rintro rfl; rw [← Ideal.zero_eq_bot] at hP'; exact zero_notMem_normalizedFactors I hP'
    have : (Ideal.absNorm P : ℝ) ≠ 0 := by
      rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact hb
    exact pow_ne_zero _ this

/-- A chosen quotient `I / Q`. -/
noncomputable def quo (I Q : Ideal (𝓞 K)) : Ideal (𝓞 K) := if h : Q ∣ I then Classical.choose h else ⊥

lemma quo_spec {I Q : Ideal (𝓞 K)} (h : Q ∣ I) : I = Q * quo I Q := by
  unfold quo; rw [dif_pos h]; exact Classical.choose_spec h

lemma quo_mul {Q J : Ideal (𝓞 K)} (hQ : Q ≠ ⊥) : quo (Q * J) Q = J := by
  have h := quo_spec (dvd_mul_right Q J)
  exact (mul_left_cancel₀ (by rwa [Ne, Ideal.zero_eq_bot]) h).symm

lemma count_pow_mul {P J : Ideal (𝓞 K)} (hP : P.IsPrime) (hb : P ≠ ⊥) (hJ : J ≠ ⊥) (k : ℕ) :
    (normalizedFactors (P ^ k * J)).count P = k + (normalizedFactors J).count P := by
  have hpr := Ideal.prime_of_isPrime hb hP
  have hP0 : P ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
  have hJ0 : J ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
  rw [normalizedFactors_mul (pow_ne_zero k hP0) hJ0, normalizedFactors_pow,
    normalizedFactors_irreducible hpr.irreducible, normalize_eq, Multiset.count_add,
    Multiset.count_nsmul, Multiset.count_singleton_self, mul_one]

lemma pow_dvd_of_le_count {I P : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hP : P.IsPrime) (hb : P ≠ ⊥) {k : ℕ}
    (hk : k ≤ (normalizedFactors I).count P) : P ^ k ∣ I := by
  have hpr := Ideal.prime_of_isPrime hb hP
  have hP0 : P ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
  have hI0 : I ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
  rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero k hP0) hI0,
    normalizedFactors_pow, normalizedFactors_irreducible hpr.irreducible, normalize_eq,
    Multiset.le_iff_count]
  intro a
  rw [Multiset.count_nsmul, Multiset.count_singleton]
  split_ifs with h
  · subst h; simpa using hk
  · simp

lemma prime_of_mem_nf {I P : Ideal (𝓞 K)} (h : P ∈ normalizedFactors I) : P.IsPrime ∧ P ≠ ⊥ := by
  refine ⟨Ideal.isPrime_of_prime (prime_of_normalized_factor P h), ?_⟩
  rintro rfl; rw [← Ideal.zero_eq_bot] at h; exact zero_notMem_normalizedFactors I h

/-- Divisor data of `I`: pairs `(P, k)` with `1 ≤ k ≤ v_P(I)`. -/
noncomputable def Dset (I : Ideal (𝓞 K)) : Finset ((_ : Ideal (𝓞 K)) × ℕ) :=
  (normalizedFactors I).toFinset.sigma (fun P => Icc 1 ((normalizedFactors I).count P))

lemma log_absNorm_eq_sum (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    Real.log (Ideal.absNorm I) = ∑ x ∈ Dset I, Real.log (Ideal.absNorm x.1) := by
  rw [log_absNorm_eq I hI, Dset, sum_sigma]
  refine sum_congr rfl (fun P _ => ?_)
  dsimp only
  rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
  simp

/-- The Dirichlet identity `a(m) log m = ∑_{d ∣ m} L(d) a(m/d)`. -/
theorem dirichlet_identity (m : ℕ) (hm : 1 ≤ m) :
    ((Iset (K := K) m).card : ℝ) * Real.log m =
      ∑ d ∈ m.divisors, Lf (K := K) d * ((Iset (K := K) (m / d)).card : ℝ) := by
  have hL : ((Iset (K := K) m).card : ℝ) * Real.log m =
      ∑ z ∈ (Iset (K := K) m).sigma Dset, Real.log (Ideal.absNorm z.2.1) := by
    rw [sum_sigma, ← nsmul_eq_mul, ← sum_const]
    refine sum_congr rfl (fun I hI => ?_)
    have hIm := mem_Iset.1 hI
    have hI0 : I ≠ ⊥ := by
      intro h; rw [h, Ideal.absNorm_bot] at hIm; omega
    rw [← log_absNorm_eq_sum I hI0, hIm]
  have hR : ∑ d ∈ m.divisors, Lf (K := K) d * ((Iset (K := K) (m / d)).card : ℝ) =
      ∑ w ∈ m.divisors.sigma (fun d => Tset (K := K) d ×ˢ Iset (K := K) (m / d)),
        Real.log (Ideal.absNorm w.2.1.1) := by
    rw [sum_sigma]
    refine sum_congr rfl (fun d _ => ?_)
    rw [sum_product, Lf, sum_mul]
    refine sum_congr rfl (fun x _ => ?_)
    dsimp only
    rw [sum_const, nsmul_eq_mul, mul_comm]
  rw [hL, hR]
  refine sum_nbij' (fun z => ⟨Ideal.absNorm z.2.1 ^ z.2.2, (z.2, quo z.1 (z.2.1 ^ z.2.2))⟩)
    (fun w => ⟨w.2.1.1 ^ w.2.1.2 * w.2.2, w.2.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨I, ⟨P, k⟩⟩ hz
    simp only [mem_sigma, Dset, Multiset.mem_toFinset, mem_Icc] at hz
    obtain ⟨hI, hP, hk1, hk2⟩ := hz
    have hIm := mem_Iset.1 hI
    have hI0 : I ≠ ⊥ := by
      intro h; rw [h, Ideal.absNorm_bot] at hIm; omega
    obtain ⟨hPp, hPb⟩ := prime_of_mem_nf hP
    have hdvd := pow_dvd_of_le_count hI0 hPp hPb hk2
    have hspec := quo_spec hdvd
    have hN2 := two_le_absNorm hPp hPb
    have hnorm : m = Ideal.absNorm P ^ k * Ideal.absNorm (quo I (P ^ k)) := by
      rw [← hIm]; conv_lhs => rw [hspec]
      rw [map_mul, map_pow]
    have hpos : 0 < Ideal.absNorm P ^ k := pow_pos (by omega) k
    refine mem_sigma.2 ⟨Nat.mem_divisors.2 ⟨⟨_, hnorm⟩, Nat.one_le_iff_ne_zero.1 hm⟩,
      mem_product.2 ⟨?_, ?_⟩⟩
    · refine mem_sigma.2 ⟨mem_PrimeSet.2 ⟨(pow_one (Ideal.absNorm P)).symm.le.trans
        (Nat.pow_le_pow_right (by omega) hk1), hPp, hPb⟩,
        mem_filter.2 ⟨mem_Icc.2 ⟨hk1, ?_⟩, rfl⟩⟩
      calc k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
        _ ≤ Ideal.absNorm P ^ k := Nat.pow_le_pow_left hN2 k
    · rw [mem_Iset]
      dsimp only
      rw [hnorm, Nat.mul_div_cancel_left _ hpos]
  · rintro ⟨d, ⟨⟨P, k⟩, J⟩⟩ hw
    simp only [mem_sigma, mem_product] at hw
    obtain ⟨hd, hx, hJ⟩ := hw
    rw [Nat.mem_divisors] at hd
    simp only [Tset, mem_sigma, mem_PrimeSet, mem_filter, mem_Icc] at hx
    obtain ⟨⟨-, hPp, hPb⟩, ⟨hk1, -⟩, hPk⟩ := hx
    rw [mem_Iset] at hJ
    obtain ⟨hdm, -⟩ := hd
    have hJ0 : J ≠ ⊥ := by
      intro h; rw [h, Ideal.absNorm_bot] at hJ
      have := Nat.div_pos (Nat.le_of_dvd (by omega) hdm) (Nat.pos_of_dvd_of_pos hdm (by omega))
      omega
    have hcount := count_pow_mul hPp hPb hJ0 k
    refine mem_sigma.2 ⟨?_, ?_⟩
    · rw [mem_Iset]
      dsimp only
      rw [map_mul, map_pow, hPk, hJ, Nat.mul_div_cancel' hdm]
    · have h1 : 0 < (normalizedFactors (P ^ k * J)).count P := by omega
      have h2 : k ≤ (normalizedFactors (P ^ k * J)).count P := by omega
      exact mem_sigma.2 ⟨Multiset.mem_toFinset.2 (Multiset.count_pos.1 h1), mem_Icc.2 ⟨hk1, h2⟩⟩
  · rintro ⟨I, ⟨P, k⟩⟩ hz
    simp only [mem_sigma, Dset, Multiset.mem_toFinset, mem_Icc] at hz
    obtain ⟨hI, hP, hk1, hk2⟩ := hz
    have hIm := mem_Iset.1 hI
    have hI0 : I ≠ ⊥ := by
      intro h; rw [h, Ideal.absNorm_bot] at hIm; omega
    obtain ⟨hPp, hPb⟩ := prime_of_mem_nf hP
    have hspec := quo_spec (pow_dvd_of_le_count hI0 hPp hPb hk2)
    dsimp only
    rw [← hspec]
  · rintro ⟨d, ⟨⟨P, k⟩, J⟩⟩ hw
    simp only [mem_sigma, mem_product] at hw
    obtain ⟨-, hx, -⟩ := hw
    simp only [Tset, mem_sigma, mem_PrimeSet, mem_filter] at hx
    obtain ⟨⟨-, hPp, hPb⟩, -, hPk⟩ := hx
    have hPk0 : P ^ k ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]; exact pow_ne_zero k (by rwa [Ne, Ideal.zero_eq_bot])
    dsimp only
    rw [quo_mul hPk0, hPk]
  · intro z _; rfl

section bound

lemma exists_prime_mem {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hb : P ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : (𝓞 K)) ∈ P := by
  haveI : P.IsMaximal := hP.isMaximal hb
  letI : Field ((𝓞 K) ⧸ P) := Ideal.Quotient.field P
  haveI : Finite ((𝓞 K) ⧸ P) :=
    (Ideal.absNorm_ne_zero_iff P).1 (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨p, hc⟩ := CharP.exists ((𝓞 K) ⧸ P)
  refine ⟨p, CharP.char_is_prime ((𝓞 K) ⧸ P) p, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

lemma liesOver_of_mem {P : Ideal (𝓞 K)} (hP : P.IsPrime) {p : ℕ} (hp : p.Prime)
    (h : ((p : ℕ) : (𝓞 K)) ∈ P) : P.LiesOver (Ideal.span {(p : ℤ)}) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hle : Ideal.span {(p : ℤ)} ≤ P.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P
    simpa using h
  exact ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top hle⟩

lemma absNorm_eq_pow {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hb : P ≠ ⊥) {p : ℕ} (hp : p.Prime)
    (h : ((p : ℕ) : (𝓞 K)) ∈ P) :
    ∃ f, 1 ≤ f ∧ f ≤ Module.finrank ℚ K ∧ Ideal.absNorm P = p ^ f := by
  have hle : Ideal.span {((p : ℕ) : (𝓞 K))} ≤ P := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact h
  have hd := Ideal.absNorm_dvd_absNorm_of_le hle
  have hN : Ideal.absNorm (Ideal.span {((p : ℕ) : (𝓞 K))}) = p ^ Module.finrank ℚ K := by
    rw [Ideal.absNorm_span_singleton]
    have : ((p : ℕ) : (𝓞 K)) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  rw [hN] at hd
  obtain ⟨f, hf, he⟩ := (Nat.dvd_prime_pow hp).1 hd
  have h2 := two_le_absNorm hP hb
  refine ⟨f, ?_, hf, he⟩
  rcases Nat.eq_zero_or_pos f with rfl | hpos
  · rw [he] at h2; simp at h2
  · exact hpos

lemma Lf_nonneg (d : ℕ) : 0 ≤ Lf (K := K) d :=
  sum_nonneg (fun _ _ => Real.log_natCast_nonneg _)

lemma Lf_le (d : ℕ) :
    Lf (K := K) d ≤ (Module.finrank ℚ K : ℝ) ^ 2 * ArithmeticFunction.vonMangoldt d := by
  set n := Module.finrank ℚ K with hn
  rcases (Tset (K := K) d).eq_empty_or_nonempty with h | ⟨⟨P0, k0⟩, h0⟩
  · rw [Lf, h, sum_empty]
    exact mul_nonneg (by positivity) ArithmeticFunction.vonMangoldt_nonneg
  simp only [Tset, mem_sigma, mem_PrimeSet, mem_filter, mem_Icc] at h0
  obtain ⟨⟨-, hP0, hb0⟩, ⟨hk01, -⟩, hd0⟩ := h0
  obtain ⟨p, hp, hpP⟩ := exists_prime_mem hP0 hb0
  obtain ⟨f0, hf01, -, hf0⟩ := absNorm_eq_pow hP0 hb0 hp hpP
  have hdp : d = p ^ (f0 * k0) := by rw [← hd0, hf0, pow_mul]
  have hΛ : ArithmeticFunction.vonMangoldt d = Real.log p := by
    rw [hdp, ArithmeticFunction.vonMangoldt_apply_pow (by positivity),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hterm : ∀ x ∈ Tset (K := K) d, Real.log (Ideal.absNorm x.1) ≤ n * Real.log p ∧
      x.1 ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K) := by
    rintro ⟨P, k⟩ hx
    simp only [Tset, mem_sigma, mem_PrimeSet, mem_filter, mem_Icc] at hx
    obtain ⟨⟨-, hP, hb⟩, ⟨hk1, -⟩, hd⟩ := hx
    obtain ⟨q, hq, hqP⟩ := exists_prime_mem hP hb
    obtain ⟨f, hf1, hfn, hf⟩ := absNorm_eq_pow hP hb hq hqP
    have hqp : q = p := by
      have e : q ^ (f * k - 1 + 1) = p ^ (f0 * k0 - 1 + 1) := by
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))),
          Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))),
          pow_mul,
          ← hf, hd, hdp]
      exact (Nat.Prime.pow_inj hq hp e).1
    subst hqp
    refine ⟨?_, ?_⟩
    · rw [hf, Nat.cast_pow, Real.log_pow]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfn) (Real.log_natCast_nonneg _)
    · haveI := liesOver_of_mem hP hq hqP
      haveI : Fact q.Prime := ⟨hq⟩
      haveI : (Ideal.span {(q : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime q
      rw [IsDedekindDomain.mem_primesOverFinset_iff (by simp [hq.ne_zero])]
      exact ⟨hP, inferInstance⟩
  have hinj : Set.InjOn (fun x : (_ : Ideal (𝓞 K)) × ℕ => x.1) (Tset (K := K) d) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    obtain ⟨P, k⟩ := x
    obtain ⟨P', k'⟩ := y
    simp only at hxy
    subst hxy
    simp only [Tset, mem_sigma, mem_PrimeSet, mem_filter, mem_Icc] at hx hy
    have h2 := two_le_absNorm hx.1.2.1 hx.1.2.2
    have : k = k' := Nat.pow_right_injective h2 (hx.2.2.trans hy.2.2.symm)
    subst this; rfl
  have hcard : (Tset (K := K) d).card ≤ n := by
    calc (Tset (K := K) d).card = ((Tset (K := K) d).image (fun x => x.1)).card :=
          (card_image_of_injOn hinj).symm
      _ ≤ (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)).card :=
          card_le_card (fun P hP => by
            obtain ⟨x, hx, rfl⟩ := mem_image.1 hP; exact (hterm x hx).2)
      _ ≤ n := by
          haveI : Fact p.Prime := ⟨hp⟩
          haveI : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
          exact Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K (by simp [hp.ne_zero])
  have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg _
  rw [Lf, hΛ]
  calc ∑ x ∈ Tset (K := K) d, Real.log (Ideal.absNorm x.1)
      ≤ ∑ _x ∈ Tset (K := K) d, ((n : ℝ) * Real.log p) := sum_le_sum (fun x hx => (hterm x hx).1)
    _ = (Tset (K := K) d).card * ((n : ℝ) * Real.log p) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ) * ((n : ℝ) * Real.log p) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (mul_nonneg (Nat.cast_nonneg _) hlp)
    _ = (n : ℝ) ^ 2 * Real.log p := by ring

lemma sum_Lf_le (N : ℕ) : ∑ m ∈ Icc 1 N, Lf (K := K) m ≤
    ((Module.finrank ℚ K : ℝ) ^ 2 * (Real.log 4 + 4)) * N := by
  calc ∑ m ∈ Icc 1 N, Lf (K := K) m
      ≤ ∑ m ∈ Icc 1 N, (Module.finrank ℚ K : ℝ) ^ 2 * ArithmeticFunction.vonMangoldt m :=
        sum_le_sum (fun m _ => Lf_le m)
    _ ≤ ∑ m ∈ Icc 0 N, (Module.finrank ℚ K : ℝ) ^ 2 * ArithmeticFunction.vonMangoldt m :=
        sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_left (Nat.zero_le 1))
          (fun m _ _ => mul_nonneg (by positivity) ArithmeticFunction.vonMangoldt_nonneg)
    _ = (Module.finrank ℚ K : ℝ) ^ 2 * Chebyshev.psi N := by
        rw [← mul_sum, Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    _ ≤ (Module.finrank ℚ K : ℝ) ^ 2 * ((Real.log 4 + 4) * N) :=
        mul_le_mul_of_nonneg_left (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N))
          (by positivity)
    _ = ((Module.finrank ℚ K : ℝ) ^ 2 * (Real.log 4 + 4)) * N := by ring

lemma Lf_prime (p : ℕ) (hp : p.Prime) :
    Lf (K := K) p =
      (Nat.card {P : Ideal (𝓞 K) // P.IsPrime ∧ Ideal.absNorm P = p} : ℝ) * Real.log p := by
  set S := (PrimeSet (K := K) p).filter (fun P => Ideal.absNorm P = p) with hSdef
  have hS : ∀ P : Ideal (𝓞 K), P ∈ S ↔ (P.IsPrime ∧ Ideal.absNorm P = p) := by
    intro P
    rw [hSdef, mem_filter, mem_PrimeSet]
    constructor
    · rintro ⟨⟨-, hP, -⟩, hN⟩; exact ⟨hP, hN⟩
    · rintro ⟨hP, hN⟩
      refine ⟨⟨hN.le, hP, ?_⟩, hN⟩
      rintro rfl; rw [Ideal.absNorm_bot] at hN; exact hp.ne_zero hN.symm
  have hcard : Nat.card {P : Ideal (𝓞 K) // P.IsPrime ∧ Ideal.absNorm P = p} = S.card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun P => (hS P).symm))
  rw [hcard, Lf, ← nsmul_eq_mul, ← sum_const]
  refine sum_nbij' (fun x => x.1) (fun P => ⟨P, 1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨P, k⟩ hx
    simp only [Tset, mem_sigma, mem_PrimeSet, mem_filter, mem_Icc] at hx
    obtain ⟨⟨hle, hP, hb⟩, -, hd⟩ := hx
    have := (Nat.Prime.pow_eq_iff hp).1 hd
    exact (hS P).2 ⟨hP, this.1⟩
  · intro P hP
    obtain ⟨hPp, hN⟩ := (hS P).1 hP
    have hb : P ≠ ⊥ := by
      rintro rfl; rw [Ideal.absNorm_bot] at hN; exact hp.ne_zero hN.symm
    simp only [Tset, mem_sigma, mem_PrimeSet, mem_filter, mem_Icc]
    exact ⟨⟨hN.le, hPp, hb⟩, ⟨le_rfl, hp.one_le⟩, by rw [pow_one, hN]⟩
  · rintro ⟨P, k⟩ hx
    simp only [Tset, mem_sigma, mem_PrimeSet, mem_filter, mem_Icc] at hx
    have := (Nat.Prime.pow_eq_iff hp).1 hx.2.2
    simp only [this.2]
  · intro P _; rfl
  · rintro ⟨P, k⟩ hx
    simp only [Tset, mem_sigma, mem_PrimeSet, mem_filter, mem_Icc] at hx
    have := (Nat.Prime.pow_eq_iff hp).1 hx.2.2
    simp only [this.1]

end bound

end BHB
end BSec

section Assembly
open Finset NumberField

/-- Ideal counting with a power-saving error and positive density
(Landau 1918; Lang, Algebraic Number Theory, Ch. VI §3, Thm 3). -/
def BHGlue.IdealCountErrorPos : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∃ c C : ℝ, 0 < c ∧ ∀ x : ℝ, 1 ≤ x →
    |(Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ x} : ℝ) - c * x| ≤
      C * x ^ (1 - 1 / (Module.finrank ℚ K : ℝ))

lemma BHB.card_le_eq (K : Type) [Field K] [NumberField K] (x : ℝ) (hx : 0 ≤ x) :
    (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ x} : ℝ) =
      1 + ∑ m ∈ Icc 1 ⌊x⌋₊, ((BHB.Iset (K := K) m).card : ℝ) := by
  classical
  have h1 : ∀ I : Ideal (𝓞 K), ((Ideal.absNorm I : ℝ) ≤ x ↔
      I ∈ (Icc 0 ⌊x⌋₊).biUnion (fun m => BHB.Iset (K := K) m)) := by
    intro I
    rw [mem_biUnion]
    constructor
    · intro h
      exact ⟨Ideal.absNorm I, mem_Icc.2 ⟨Nat.zero_le _, Nat.le_floor h⟩, BHB.mem_Iset.2 rfl⟩
    · rintro ⟨m, hm, hI⟩
      rw [BHB.mem_Iset.1 hI]
      exact (Nat.cast_le.2 (mem_Icc.1 hm).2).trans (Nat.floor_le hx)
  have hc : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ x} =
      ((Icc 0 ⌊x⌋₊).biUnion (fun m => BHB.Iset (K := K) m)).card := by
    rw [← Nat.card_eq_finsetCard]; exact Nat.card_congr (Equiv.subtypeEquivRight h1)
  have h0 : (BHB.Iset (K := K) 0).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨⊥, ?_⟩
    ext I
    rw [BHB.mem_Iset, mem_singleton, Ideal.absNorm_eq_zero_iff]
  rw [hc, card_biUnion (fun a _ b _ hab => Finset.disjoint_left.2
    (fun I h1 h2 => hab ((BHB.mem_Iset.1 h1).symm.trans (BHB.mem_Iset.1 h2))))]
  have hIoc : Ioc 0 ⌊x⌋₊ = Icc 1 ⌊x⌋₊ := by ext; simp only [mem_Ioc, mem_Icc]; omega
  rw [Nat.cast_sum, ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le _), h0, hIoc, Nat.cast_one]

lemma BHB.primesBelow_succ (N : ℕ) :
    Nat.primesBelow (N + 1) = (Icc 1 N).filter Nat.Prime := by
  ext p
  simp only [Nat.mem_primesBelow, mem_filter, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h2.one_le, by omega⟩, h2⟩
  · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨by omega, h2⟩

theorem BHGlue.mertensDegOne_of_count (hIC : BHGlue.IdealCountErrorPos) :
    BHGlue.MertensDegOne := by
  intro K _ _
  obtain ⟨c, C, hc, hcount⟩ := hIC K
  set n := Module.finrank ℚ K with hn
  have hn1 : 1 ≤ n := Module.finrank_pos
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  set δ : ℝ := 1 / (n : ℝ) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 := by rw [hδ, div_le_one (by linarith)]; exact hnR
  have hH2 : ∀ x : ℝ, 1 ≤ x → |∑ m ∈ Icc 1 ⌊x⌋₊, ((BHB.Iset (K := K) m).card : ℝ) - c * x| ≤
      (C + 1) * x ^ (1 - δ) := by
    intro x hx
    have h := hcount x hx
    rw [BHB.card_le_eq K x (by linarith)] at h
    have hx1 : 1 ≤ x ^ (1 - δ) := Real.one_le_rpow hx (by linarith)
    have e : ∑ m ∈ Icc 1 ⌊x⌋₊, ((BHB.Iset (K := K) m).card : ℝ) - c * x =
        (1 + ∑ m ∈ Icc 1 ⌊x⌋₊, ((BHB.Iset (K := K) m).card : ℝ) - c * x) - 1 := by ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_one]
    have : C * x ^ (1 - 1 / (n : ℝ)) = C * x ^ (1 - δ) := rfl
    linarith
  obtain ⟨M1, hM1⟩ := BHMert.absMertens (fun m => ((BHB.Iset (K := K) m).card : ℝ))
    (BHB.Lf (K := K)) c (C + 1) ((n : ℝ) ^ 2 * (Real.log 4 + 4)) δ hc hδ0 hδ1
    (fun m => Nat.cast_nonneg _) BHB.Lf_nonneg (fun m hm => BHB.dirichlet_identity m hm) hH2
    BHB.sum_Lf_le
  have hΛ3 : ∀ N : ℕ, ∑ m ∈ Icc 1 N, ArithmeticFunction.vonMangoldt m ≤ (Real.log 4 + 4) * N := by
    intro N
    calc ∑ m ∈ Icc 1 N, ArithmeticFunction.vonMangoldt m
        ≤ ∑ m ∈ Icc 0 N, ArithmeticFunction.vonMangoldt m :=
          sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_left (Nat.zero_le 1))
            (fun m _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      _ = Chebyshev.psi N := by rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
      _ ≤ (Real.log 4 + 4) * N := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N)
  obtain ⟨M2, hM2⟩ := BHMert.absMertens (fun _ => (1 : ℝ))
    (fun m => ArithmeticFunction.vonMangoldt m) 1 1 (Real.log 4 + 4) 1 one_pos one_pos le_rfl
    (fun _ => zero_le_one) (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
    (fun m _ => by simp [ArithmeticFunction.vonMangoldt_sum])
    (fun x hx => by
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one, sub_self,
        Real.rpow_zero, one_mul]
      rw [abs_le]
      constructor
      · linarith [Nat.lt_floor_add_one x]
      · linarith [Nat.floor_le (show (0 : ℝ) ≤ x by linarith)])
    hΛ3
  obtain ⟨M3, hM3⟩ := BHGlue.mertens_below
  have hM10 : 0 ≤ M1 := (abs_nonneg _).trans (hM1 1 le_rfl)
  have hM20 : 0 ≤ M2 := (abs_nonneg _).trans (hM2 1 le_rfl)
  have hM30 : 0 ≤ M3 := (abs_nonneg _).trans (hM3 0)
  set cnt : ℕ → ℝ := fun p =>
    (Nat.card {P : Ideal (𝓞 K) // P.IsPrime ∧ Ideal.absNorm P = p} : ℝ) with hcnt
  -- bound for primes up to N (inclusive)
  have hQ : ∀ N : ℕ, 1 ≤ N → |∑ p ∈ (Icc 1 N).filter Nat.Prime, cnt p * Real.log p / p -
      Real.log N| ≤ M1 + (n : ℝ) ^ 2 * (M2 + M3 + Real.log 2) := by
    intro N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hsplitL := (sum_filter_add_sum_filter_not (Icc 1 N) Nat.Prime
      (fun m => BHB.Lf (K := K) m / m)).symm
    have hsplitΛ := (sum_filter_add_sum_filter_not (Icc 1 N) Nat.Prime
      (fun m => ArithmeticFunction.vonMangoldt m / m)).symm
    have hprimeL : ∑ p ∈ (Icc 1 N).filter Nat.Prime, BHB.Lf (K := K) p / p =
        ∑ p ∈ (Icc 1 N).filter Nat.Prime, cnt p * Real.log p / p := by
      refine sum_congr rfl (fun p hp => ?_)
      rw [BHB.Lf_prime p (mem_filter.1 hp).2]
    have hprimeΛ : ∑ p ∈ (Icc 1 N).filter Nat.Prime, ArithmeticFunction.vonMangoldt p / p =
        ∑ p ∈ Nat.primesBelow (N + 1), Real.log p / p := by
      rw [BHB.primesBelow_succ]
      refine sum_congr rfl (fun p hp => ?_)
      rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.1 hp).2]
    have hnp0 : 0 ≤ ∑ m ∈ (Icc 1 N).filter (fun m => ¬ Nat.Prime m), BHB.Lf (K := K) m / m :=
      sum_nonneg (fun m _ => div_nonneg (BHB.Lf_nonneg m) (Nat.cast_nonneg _))
    have hnpLe : ∑ m ∈ (Icc 1 N).filter (fun m => ¬ Nat.Prime m), BHB.Lf (K := K) m / m ≤
        (n : ℝ) ^ 2 * ∑ m ∈ (Icc 1 N).filter (fun m => ¬ Nat.Prime m),
          ArithmeticFunction.vonMangoldt m / m := by
      rw [mul_sum]
      refine sum_le_sum (fun m _ => ?_)
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (BHB.Lf_le m) (Nat.cast_nonneg _)
    have hlog : |Real.log ((N + 1 : ℕ) : ℝ) - Real.log N| ≤ Real.log 2 := by
      have h1 : Real.log N ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
        Real.log_le_log hNpos (by push_cast; linarith)
      have h2 : Real.log ((N + 1 : ℕ) : ℝ) ≤ Real.log 2 + Real.log N := by
        rw [← Real.log_mul (by norm_num) hNpos.ne']
        exact Real.log_le_log (by positivity)
          (by push_cast; linarith [show (1 : ℝ) ≤ N from by exact_mod_cast hN])
      rw [abs_le]; constructor <;> linarith
    have hnpΛ : ∑ m ∈ (Icc 1 N).filter (fun m => ¬ Nat.Prime m),
        ArithmeticFunction.vonMangoldt m / m ≤ M2 + M3 + Real.log 2 := by
      have a1 := hM2 N hN
      have a2 := hM3 (N + 1)
      rw [hsplitΛ, hprimeΛ] at a1
      rw [abs_le] at a1 a2 hlog
      linarith [a1.1, a1.2, a2.1, a2.2, hlog.1, hlog.2]
    have b1 := hM1 N hN
    rw [hsplitL, hprimeL] at b1
    have hn2 : 0 ≤ (n : ℝ) ^ 2 := by positivity
    have b2 : (n : ℝ) ^ 2 * ∑ m ∈ (Icc 1 N).filter (fun m => ¬ Nat.Prime m),
        ArithmeticFunction.vonMangoldt m / m ≤ (n : ℝ) ^ 2 * (M2 + M3 + Real.log 2) :=
      mul_le_mul_of_nonneg_left hnpΛ hn2
    rw [abs_le] at b1 ⊢
    constructor <;> linarith [b1.1, b1.2]
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨M1 + (n : ℝ) ^ 2 * (M2 + M3 + Real.log 2) + Real.log 2, fun N => ?_⟩
  have hK0 : 0 ≤ M1 + (n : ℝ) ^ 2 * (M2 + M3 + Real.log 2) := by positivity
  rcases Nat.lt_or_ge N 2 with hN | hN
  · interval_cases N
    · rw [show Nat.primesBelow 0 = ∅ by decide, sum_empty, Nat.cast_zero, Real.log_zero,
        sub_zero, abs_zero]
      linarith
    · rw [show Nat.primesBelow 1 = ∅ by decide, sum_empty, Nat.cast_one, Real.log_one,
        sub_zero, abs_zero]
      linarith
  · obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    have hN' : 1 ≤ N' := by omega
    have hq := hQ N' hN'
    rw [← BHB.primesBelow_succ] at hq
    have hNpos : (0 : ℝ) < N' := by exact_mod_cast hN'
    have hlog : |Real.log ((N' + 1 : ℕ) : ℝ) - Real.log N'| ≤ Real.log 2 := by
      have h1 : Real.log N' ≤ Real.log ((N' + 1 : ℕ) : ℝ) :=
        Real.log_le_log hNpos (by push_cast; linarith)
      have h2 : Real.log ((N' + 1 : ℕ) : ℝ) ≤ Real.log 2 + Real.log N' := by
        rw [← Real.log_mul (by norm_num) hNpos.ne']
        exact Real.log_le_log (by positivity)
          (by push_cast; linarith [show (1 : ℝ) ≤ N' from by exact_mod_cast hN'])
      rw [abs_le]; constructor <;> linarith
    rw [abs_le] at hq hlog ⊢
    constructor <;> linarith [hq.1, hq.2, hlog.1, hlog.2]

/-- The parent, modulo the single remaining child `IdealCountErrorPos`. -/
theorem BHGlue.parent_of_idealCount (hIC : BHGlue.IdealCountErrorPos)
    (polys : Finset ℤ[X]) (h_nonempty : polys.Nonempty)
    (h_bunyakovsky : ∀ f ∈ polys, BunyakovskyCondition f)
    (h_schinzel : SchinzelCondition polys) :
    ∃ C : ℝ, 0 < C ∧ Filter.Tendsto (partialProduct polys) Filter.atTop (nhds C) :=
  BHGlue.parent_of_mertens (BHGlue.mertensDegOne_of_count hIC) polys h_nonempty h_bunyakovsky
    h_schinzel

end Assembly

/-- The ideal-counting child, now proved (lattice count with boundary error + Lipschitz
parametrisation of the frontier of `normLeOne`). -/
theorem BHGlue.idealCountErrorPos_proved : BHGlue.IdealCountErrorPos :=
  fun K _ _ => BHA.idealCountErrorPos K

open Polynomial Filter Topology Asymptotics FCP.BatemanHorn in
theorem solution
    (polys : Finset ℤ[X]) (h_nonempty : polys.Nonempty)
    (h_bunyakovsky : ∀ f ∈ polys, BunyakovskyCondition f)
    (h_schinzel : SchinzelCondition polys) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (partialProduct polys) atTop (𝓝 C) := by
  exact BHGlue.parent_of_idealCount BHGlue.idealCountErrorPos_proved polys h_nonempty
    h_bunyakovsky h_schinzel
