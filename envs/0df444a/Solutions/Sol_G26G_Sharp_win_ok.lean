-- Prove2me | solution 1 for G26G.Sharp.win_ok
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:31:32.171946+00:00
-- url     : https://prove2.me/submissions/de4156d4-5322-4b97-bfcb-e5681938fccb

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_G26_body
import Definitions.Def_IAFTRL_G26_run
import Definitions.Def_IAFTRL_G26_window
import Theorems.Thm_IAFTRL_lemma_G_12
import Theorems.Thm_IAFTRL_lemma_J_4

-- ===== Solutions.T31.Geo =====

/-! ### General tools for the Theorem 3.1 leaves -/

open MeasureTheory Matrix Set

namespace T31

/-! #### Quadratic forms of positive definite matrices -/

/-! #### Convex hulls of compact sets in finite dimension -/

section Hull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E]

end Hull

/-! #### Integrals against measures supported on a compact set -/

variable {d : ℕ}

/-! #### Discrete measures -/

section Disc

variable {ι : Type*} [Fintype ι]

/-- the discrete measure `∑ r_i δ_{x_i}` -/
noncomputable def disc (r : ι → ℝ) (x : ι → Fin d → ℝ) : Measure (Fin d → ℝ) :=
  ∑ i, ENNReal.ofReal (r i) • Measure.dirac (x i)

instance disc_finite (r : ι → ℝ) (x : ι → Fin d → ℝ) : IsFiniteMeasure (disc r x) := by
  refine ⟨?_⟩
  simp only [disc, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.ofReal_lt_top

end Disc

/-! #### The gauge of `𝒮 = Conv(𝒜 ∪ -𝒜)` dominates the sup norm -/

lemma Sset_sub_ball {𝒜 : Set (Fin d → ℝ)} (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) :
    IAFTRL.Sset 𝒜 ⊆ Metric.closedBall 0 1 := by
  refine convexHull_min ?_ (convex_closedBall 0 1)
  have h1 : ∀ a ∈ 𝒜, ‖a‖ ≤ 1 := by
    intro a ha
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    have : a i * a i ≤ a ⬝ᵥ a :=
      Finset.single_le_sum (f := fun j => a j * a j) (fun j _ => mul_self_nonneg _)
        (Finset.mem_univ i)
    rw [Real.norm_eq_abs]
    have := hball a ha
    nlinarith [abs_mul_abs_self (a i), abs_nonneg (a i)]
  rintro x (hx | hx)
  · simpa using h1 x hx
  · have := h1 (-x) (by simpa using hx)
    simpa [norm_neg] using this

lemma Sset_nhds {𝒜 : Set (Fin d → ℝ)} (hne : 𝒜.Nonempty) (hspan : Submodule.span ℝ 𝒜 = ⊤) :
    IAFTRL.Sset 𝒜 ∈ nhds (0 : Fin d → ℝ) := by
  set S := IAFTRL.Sset 𝒜 with hSdef
  have hconv : Convex ℝ S := convex_convexHull ℝ _
  have hsymm : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    have h' : -(𝒜 ∪ -𝒜) = 𝒜 ∪ -𝒜 := by
      ext y; simp only [Set.mem_neg, Set.mem_union, neg_neg]; tauto
    have : -x ∈ -convexHull ℝ (𝒜 ∪ -𝒜) := by rw [Set.neg_mem_neg]; exact hx
    rw [← convexHull_neg, h'] at this
    exact this
  have haff : affineSpan ℝ S = ⊤ := by
    obtain ⟨a₀, ha₀⟩ := hne
    have hSne : S.Nonempty := ⟨a₀, subset_convexHull ℝ _ (Or.inl ha₀)⟩
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ _ _ hSne, eq_top_iff, ← hspan]
    refine Submodule.span_le.2 fun a ha => ?_
    have hpa : a ∈ S := subset_convexHull ℝ _ (Or.inl ha)
    have hna : -a ∈ S := subset_convexHull ℝ _ (Or.inr (by simpa using ha))
    have h2 := vsub_mem_vectorSpan ℝ hpa hna
    rw [vsub_eq_sub, sub_neg_eq_add] at h2
    have := Submodule.smul_mem _ (1 / 2 : ℝ) h2
    have e : (1 / 2 : ℝ) • (a + a) = a := by
      rw [← two_smul ℝ a, smul_smul]; norm_num
    rwa [e] at this
  obtain ⟨x, hx⟩ := (hconv.interior_nonempty_iff_affineSpan_eq_top).2 haff
  have hxn : S ∈ nhds x := mem_interior_iff_mem_nhds.1 hx
  have hx' : -x ∈ interior S := by
    rw [mem_interior_iff_mem_nhds]
    have : (fun y : Fin d → ℝ => -y) ⁻¹' S ∈ nhds (-x) :=
      continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hxn)
    exact Filter.mem_of_superset this fun y hy => by simpa using hsymm _ hy
  have h0 : (0 : Fin d → ℝ) ∈ interior S := by
    have := hconv.interior hx hx' (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa using this
  exact mem_interior_iff_mem_nhds.1 h0

lemma norm_le_sNorm {𝒜 : Set (Fin d → ℝ)} (hne : 𝒜.Nonempty) (hspan : Submodule.span ℝ 𝒜 = ⊤)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (x : Fin d → ℝ) : ‖x‖ ≤ IAFTRL.sNorm 𝒜 x := by
  have := le_gauge_of_subset_closedBall (absorbent_nhds_zero (Sset_nhds hne hspan)) zero_le_one
    (Sset_sub_ball hball) (x := x)
  simpa [IAFTRL.sNorm] using this

end T31


-- ===== Solutions.G1.Geo2 =====

/-! ### Generator geometry helpers -/

open MeasureTheory ProbabilityTheory Set IAFTRL

namespace G1L

variable {d : ℕ}

lemma Sset_gen {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IsGenerator 𝒜 ℬ) : Sset 𝒜 = Sset ℬ := by
  unfold Sset
  apply le_antisymm
  · refine convexHull_min ?_ (convex_convexHull ℝ _)
    rintro x (hx | hx)
    · exact convexHull_mono subset_union_left (hgen.2 hx)
    · have h1 : -x ∈ convexHull ℝ ℬ := hgen.2 hx
      have h2 : x ∈ convexHull ℝ (-ℬ) := by
        rw [convexHull_neg, Set.mem_neg]; exact h1
      exact convexHull_mono subset_union_right h2
  · exact convexHull_mono (union_subset_union hgen.1 (Set.neg_subset_neg.2 hgen.1))

lemma sNorm_gen {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IsGenerator 𝒜 ℬ) (x : Fin d → ℝ) :
    sNorm 𝒜 x = sNorm ℬ x := by
  unfold sNorm; rw [Sset_gen hgen]

lemma Kset_gen {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IsGenerator 𝒜 ℬ) : Kset 𝒜 = Kset ℬ :=
  ((convexHull_mono hgen.1).antisymm (convexHull_min hgen.2 (convex_convexHull ℝ ℬ))).symm

end G1L


-- ===== Solutions.G2.Run =====

/-! ### Basic facts about GIA-FTRL runs -/

open MeasureTheory ProbabilityTheory Set IAFTRL
open scoped ENNReal

namespace G2R

variable {d : ℕ}

/-! #### Geometry -/

/-! #### Runs -/

section Run

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝒜 ℬ : Set (Fin d → ℝ)}
  {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

lemma feas (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (ω : Ω) :
    IsFeasible3_6 ℬ e (t + 1) (R.cumEst t ω) (R.p t ω) :=
  ((hR t ht).2.1.2 ω).1

lemma p_supp (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (ω : Ω) :
    R.p t ω (Kset ℬ)ᶜ = 0 :=
  (feas hR ht ω).2.1

end Run

/-! #### Deterministic range bounds -/

lemma gB_pos : 0 < gB d := by unfold gB; positivity

section Bounds

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝒜 ℬ : Set (Fin d → ℝ)}
  {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

end Bounds

end G2R


-- ===== Solutions.G26.Freeze =====

/-! ### Freezing an affine field at a predictable stopping rule -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {d : ℕ} {Ω : Type*}

lemma survS_anti (A : ℕ → Set Ω) {m n : ℕ} (h : m ≤ n) : survS A n ⊆ survS A m := by
  intro ω hω
  simp only [survS, Set.mem_iInter, Finset.mem_range] at hω ⊢
  exact fun i hi => hω i (by omega)

/-- on the surviving set the frozen field is the field -/
lemma frz_eq {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) :
    ∀ n ω, (n = 0 ∨ ω ∈ survS A (n - 1)) → frz X A n ω = X n ω := by
  intro n ω h
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Nat.add_sub_cancel] at h
    rcases h with h | h
    · omega
    · simp only [frz, if_pos h]

lemma frz_succ_of_notMem {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) {n : ℕ} {ω : Ω}
    (h : ω ∉ survS A n) : frz X A (n + 1) ω = frz X A n ω := by
  simp only [frz, if_neg h]

/-- once frozen at the first failure `i`, the field stays at its value at `i` -/
lemma frz_stop {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) {i : ℕ} {ω : Ω}
    (hi : i = 0 ∨ ω ∈ survS A (i - 1)) (hfail : ω ∉ A i) :
    ∀ N, i ≤ N → frz X A N ω = X i ω := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact frz_eq X A i ω hi
  | succ N hiN ih =>
    have hnot : ω ∉ survS A N := by
      intro h
      have := survS_anti A hiN h
      simp only [survS, Set.mem_iInter, Finset.mem_range] at this
      exact hfail (this i (by omega))
    rw [frz_succ_of_notMem X A hnot, ih]

section

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

end

end G26


-- ===== Solutions.G26.Geo =====

/-! ### The projective body of normalized directions (Lemma G.16) -/

open MeasureTheory ProbabilityTheory Set IAFTRL

namespace G26G

open G26

variable {d : ℕ}

variable {𝒜 ℬ : Set (Fin d → ℝ)} {θ astar : Fin d → ℝ}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

lemma ne𝒜 : 𝒜.Nonempty := ⟨astar, H.hastar⟩

lemma haK : astar ∈ Kset ℬ := H.hgen.2 H.hastar

lemma sig_pos : 0 < H.sig := (Classical.choose_spec H.hsharp).1

lemma sig_spec {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) :
    H.sig * sNorm ℬ (a - astar) ≤ gap θ astar a := by
  have h := (Classical.choose_spec H.hsharp).2 a (by rw [G1L.Kset_gen H.hgen]; exact ha)
  rw [G1L.sNorm_gen H.hgen] at h
  exact h

lemma norm_le (x : Fin d → ℝ) : ‖x‖ ≤ sNorm ℬ x := by
  rw [← G1L.sNorm_gen H.hgen]; exact T31.norm_le_sNorm H.ne𝒜 H.hspan H.hball x

lemma gap_pos {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) (hne : a ≠ astar) : 0 < gap θ astar a := by
  have h1 : 0 < ‖a - astar‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have h2 := H.norm_le (a - astar)
  exact lt_of_lt_of_le (mul_pos H.sig_pos (lt_of_lt_of_le h1 h2)) (H.sig_spec ha)

end Sharp

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

lemma U0_sNorm {u : Fin d → ℝ} (hu : u ∈ U0 ℬ θ astar) : sNorm ℬ u ≤ H.sig⁻¹ := by
  obtain ⟨a, ⟨ha, hne⟩, rfl⟩ := hu
  have h := H.gap_pos ha hne
  unfold ndir sNorm
  rw [gauge_smul_of_nonneg (inv_nonneg.2 h.le), smul_eq_mul]
  have h2 := H.sig_spec ha
  unfold sNorm at h2
  rw [inv_mul_le_iff₀ h]
  have hs := H.sig_pos
  rw [← div_eq_mul_inv, le_div_iff₀ hs]
  linarith

lemma U0_bdd : U0 ℬ θ astar ⊆ Metric.closedBall 0 H.sig⁻¹ := by
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (H.norm_le u).trans (H.U0_sNorm hu)

lemma UT_bdd {u : Fin d → ℝ} (hu : u ∈ UT ℬ θ astar) : ‖u‖ ≤ H.sig⁻¹ := by
  have := closure_minimal H.U0_bdd Metric.isClosed_closedBall hu
  rwa [Metric.mem_closedBall, dist_zero_right] at this

lemma DT_mem {w : Fin d → ℝ} (hw : w ∈ DT ℬ θ astar) :
    ∃ l ∈ Icc (0 : ℝ) 1, ∃ u ∈ UT ℬ θ astar, w = l • u := by
  obtain ⟨⟨l, u⟩, ⟨hl, hu⟩, rfl⟩ := hw
  exact ⟨l, hl, u, hu, rfl⟩

/-- the cone body lies in the span of the centered differences -/
lemma DT_sub_span : DT ℬ θ astar ⊆
    (Submodule.span ℝ ((fun a => a - astar) '' Kset ℬ) : Set (Fin d → ℝ)) := by
  set V := Submodule.span ℝ ((fun a => a - astar) '' Kset ℬ)
  have hV : IsClosed (V : Set (Fin d → ℝ)) := Submodule.closed_of_finiteDimensional V
  have hU0 : U0 ℬ θ astar ⊆ V := by
    rintro _ ⟨a, ⟨ha, -⟩, rfl⟩
    exact V.smul_mem _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  have hUT : UT ℬ θ astar ⊆ V := closure_minimal hU0 hV
  rintro _ ⟨⟨l, u⟩, ⟨-, hu⟩, rfl⟩
  exact V.smul_mem l (hUT hu)

lemma DT_bdd {w : Fin d → ℝ} (hw : w ∈ DT ℬ θ astar) : ‖w‖ ≤ H.sig⁻¹ := by
  obtain ⟨l, ⟨hl0, hl1⟩, u, hu, rfl⟩ := H.DT_mem hw
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hl0]
  have := H.UT_bdd hu
  have hs : 0 ≤ H.sig⁻¹ := inv_nonneg.2 H.sig_pos.le
  nlinarith [norm_nonneg u]

/-- **projective extension (G.306)**: the normalized field is dominated by the centered field -/
lemma DT_span_bound : ∃ Λ1 : ℝ, 0 < Λ1 ∧ ∀ (w : Fin d → ℝ) (M : ℝ),
    (∀ a ∈ Kset ℬ, |(a - astar) ⬝ᵥ w| ≤ M) → ∀ u ∈ DT ℬ θ astar, |u ⬝ᵥ w| ≤ Λ1 * M := by
  classical
  set s := (fun a => a - astar) '' Kset ℬ
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent ℝ s
  have : Finite b := hli.finite_of_isNoetherian
  haveI : Fintype b := Fintype.ofFinite b
  set L := Fintype.linearCombination ℝ (fun i : b => (i : Fin d → ℝ))
  have hL : LinearMap.range L = Submodule.span ℝ s := by
    rw [Fintype.range_linearCombination, Subtype.range_coe, hspan]
  obtain ⟨g, hg⟩ := L.rangeRestrict.exists_rightInverse_of_surjective L.range_rangeRestrict
  set gc := LinearMap.toContinuousLinearMap g
  refine ⟨(Fintype.card b : ℝ) * ‖gc‖ * H.sig⁻¹ + 1, add_pos_of_nonneg_of_pos (mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) gc.opNorm_nonneg) (inv_nonneg.2 H.sig_pos.le)) one_pos, ?_⟩
  intro w M hM u hu
  have hM0 : 0 ≤ M := by
    have := hM astar H.haK
    simpa using le_trans (abs_nonneg _) this
  have huV : u ∈ LinearMap.range L := by rw [hL]; exact H.DT_sub_span hu
  set c := g ⟨u, huV⟩
  have hLc : L c = u := by
    have := congrArg Subtype.val (LinearMap.congr_fun hg ⟨u, huV⟩)
    simpa [c] using this
  have hc : ‖c‖ ≤ ‖gc‖ * H.sig⁻¹ := by
    have h1 : ‖c‖ ≤ ‖gc‖ * ‖(⟨u, huV⟩ : LinearMap.range L)‖ := gc.le_opNorm _
    have h2 : ‖(⟨u, huV⟩ : LinearMap.range L)‖ = ‖u‖ := rfl
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (H.DT_bdd hu) gc.opNorm_nonneg)
  rw [← hLc, Fintype.linearCombination_apply, sum_dotProduct]
  calc |∑ i : b, (c i • (i : Fin d → ℝ)) ⬝ᵥ w| ≤ ∑ i : b, |(c i • (i : Fin d → ℝ)) ⬝ᵥ w| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : b, ‖c‖ * M := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [smul_dotProduct, smul_eq_mul, abs_mul]
        obtain ⟨a, ha, hai⟩ := hbs i.2
        have h1 : |(i : Fin d → ℝ) ⬝ᵥ w| ≤ M := by rw [← hai]; exact hM a ha
        have h2 : |c i| ≤ ‖c‖ := by
          have := norm_le_pi_norm c i
          rwa [Real.norm_eq_abs] at this
        exact mul_le_mul h2 h1 (abs_nonneg _) (norm_nonneg _)
    _ = (Fintype.card b : ℝ) * ‖c‖ * M := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ ((Fintype.card b : ℝ) * ‖gc‖ * H.sig⁻¹ + 1) * M := by
        have : (Fintype.card b : ℝ) * ‖c‖ ≤ (Fintype.card b : ℝ) * ‖gc‖ * H.sig⁻¹ + 1 := by
          have := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (Fintype.card b))
          linarith
        exact mul_le_mul_of_nonneg_right this hM0

end Sharp

end G26G


-- ===== Solutions.G26.RunN =====

/-! ### The normalized field on the cone body satisfies the field interface (Lemmas G.17, G.28) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

lemma Lam1_eq : ∃ h, Lam1 ℬ θ astar = Classical.choose (p := fun Λ1 : ℝ => 0 < Λ1 ∧
    ∀ (w : Fin d → ℝ) (M : ℝ), (∀ a ∈ Kset ℬ, |(a - astar) ⬝ᵥ w| ≤ M) →
      ∀ u ∈ DT ℬ θ astar, |u ⬝ᵥ w| ≤ Λ1 * M) h :=
  ⟨H.DT_span_bound, by unfold Lam1; rw [dif_pos H.DT_span_bound]⟩

lemma Lam1_pos : 0 < Lam1 ℬ θ astar := by
  obtain ⟨h, e⟩ := H.Lam1_eq; rw [e]; exact (Classical.choose_spec h).1

lemma kb_ge : 1 ≤ H.kb ∧ H.sig⁻¹ ≤ H.kb ∧ H.sig⁻¹ ^ 2 ≤ H.kb := by
  have : 0 ≤ H.sig⁻¹ := inv_nonneg.2 H.sig_pos.le
  unfold kb; refine ⟨?_, ?_, ?_⟩ <;> nlinarith

end Sharp

end G26G

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

end Sharp

end G26G


-- ===== Solutions.G26.SIFreeze =====

/-! ### Freezing a scalar interface at a predictable success rule (Lemma G.29, (G.653)–(G.659)) -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {Ω : Type*}

open Classical in
/-- the freezing index: the first failure of the rule before `n`, or `n` -/
noncomputable def fidx (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) : ℕ :=
  if h : ∃ i, i < n ∧ ω ∉ A i then Nat.find h else n

lemma frz_fidx {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    frz X A n ω = X (fidx A n ω) ω ∧ fidx A n ω ≤ n ∧
      (fidx A n ω = n ∨ ω ∉ A (fidx A n ω)) ∧ ∀ j < fidx A n ω, ω ∈ A j := by
  classical
  unfold fidx
  split_ifs with h
  · have hspec := Nat.find_spec h
    have hmin : ∀ j < Nat.find h, ω ∈ A j := fun j hj => by
      by_contra hj'
      exact Nat.find_min h hj ⟨by have := hspec.1; omega, hj'⟩
    have hsurv : Nat.find h = 0 ∨ ω ∈ survS A (Nat.find h - 1) := by
      rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | hpos
      · exact Or.inl h0
      · right
        simp only [survS, Set.mem_iInter, Finset.mem_range]
        intro j hj; exact hmin j (by omega)
    exact ⟨frz_stop X A hsurv hspec.2 n hspec.1.le, hspec.1.le, Or.inr hspec.2, hmin⟩
  · push Not at h
    have hs : n = 0 ∨ ω ∈ survS A (n - 1) := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · exact Or.inl h0
      · right
        simp only [survS, Set.mem_iInter, Finset.mem_range]
        intro j hj; exact h j (by omega)
    exact ⟨frz_eq X A n ω hs, le_rfl, Or.inl rfl, fun j hj => h j hj⟩

lemma frz_before {E : Type*} (X : ℕ → Ω → E) {A : ℕ → Set Ω} {u : ℕ} (hA : ∀ n < u, A n = univ) :
    frz X A u = X u := by
  funext ω
  refine frz_eq X A u ω ?_
  rcases Nat.eq_zero_or_pos u with h | h
  · exact Or.inl h
  · right
    simp only [survS, Set.mem_iInter, Finset.mem_range]
    intro j hj; rw [hA j (by omega)]; trivial

variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω}
  {Y : ℕ → Ω → ℝ} {I : ℕ → Set Ω} {m N : ℕ} {τ β : ℕ → ℝ} {B : ℝ}

end G26

namespace G26

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω}
  {Y : ℕ → Ω → ℝ} {I : ℕ → Set Ω} {m N : ℕ} {τ β : ℕ → ℝ} {B : ℝ}

end G26


-- ===== Solutions.G26.Params =====

/-! ### Thresholds: buffers `τ_s = (s+1)^{7/8} + 4z` and logarithmic gap cutoffs -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26G

open G26 G26R

lemma root8_pow {x : ℝ} (hx : 0 ≤ x) : root8 x ^ 8 = x := by
  unfold root8
  have h1 : Real.sqrt (Real.sqrt (Real.sqrt x)) ^ 2 = Real.sqrt (Real.sqrt x) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have h2 : Real.sqrt (Real.sqrt x) ^ 2 = Real.sqrt x := Real.sq_sqrt (Real.sqrt_nonneg _)
  have h3 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  calc Real.sqrt (Real.sqrt (Real.sqrt x)) ^ 8 =
      ((Real.sqrt (Real.sqrt (Real.sqrt x)) ^ 2) ^ 2) ^ 2 := by ring
    _ = x := by rw [h1, h2, h3]

lemma root8_nonneg (x : ℝ) : 0 ≤ root8 x := Real.sqrt_nonneg _

lemma root8_mono {x y : ℝ} (hxy : x ≤ y) : root8 x ≤ root8 y := by
  unfold root8
  exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hxy))

lemma le_root8 {x a : ℝ} (ha : 0 ≤ a) (h : a ^ 8 ≤ x) : a ≤ root8 x := by
  have hx : 0 ≤ x := le_trans (by positivity) h
  by_contra hlt
  push Not at hlt
  have := pow_lt_pow_left₀ hlt (root8_nonneg x) (by norm_num : (8 : ℕ) ≠ 0)
  rw [root8_pow hx] at this
  linarith

end G26G

namespace G26G

lemma root8_eq_rpow {x : ℝ} (hx : 0 ≤ x) : root8 x = x ^ ((1 : ℝ) / 8) := by
  have h1 : (x ^ ((1 : ℝ) / 8)) ^ (8 : ℕ) = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  have h2 := root8_pow hx
  have hn1 : 0 ≤ x ^ ((1 : ℝ) / 8) := Real.rpow_nonneg hx _
  exact (pow_left_inj₀ (root8_nonneg x) hn1 (by norm_num : (8 : ℕ) ≠ 0)).1 (h2.trans h1.symm)

lemma rpow78_eq {x : ℝ} (hx : 0 ≤ x) : x ^ ((7 : ℝ) / 8) = root8 x ^ 7 := by
  rw [root8_eq_rpow hx, ← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

/-- `root8` dominates polynomial thresholds: if `c^8 ≤ x` then `c ≤ root8 x` -/
lemma root8_ge_of {x c : ℝ} (hc : 0 ≤ c) (h : c ^ 8 ≤ x) : c ≤ root8 x := le_root8 hc h

end G26G


-- ===== Solutions.G26.RefBlock =====

/-! ### Uniform reference control on a block (Lemma G.29) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma add_pow_le_two {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    (x + y) ^ n ≤ 2 ^ n * (x ^ n + y ^ n) := by
  rcases le_total x y with h | h
  · have h1 : (x + y) ^ n ≤ (2 * y) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
    rw [mul_pow] at h1
    have : 0 ≤ x ^ n := pow_nonneg hx n
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) n]
  · have h1 : (x + y) ^ n ≤ (2 * x) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
    rw [mul_pow] at h1
    have : 0 ≤ y ^ n := pow_nonneg hy n
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) n]

lemma frz_univ {E : Type*} (X : ℕ → Ω → E) (n : ℕ) : frz X (fun _ => univ) n = X n := by
  funext ω
  obtain ⟨h1, -, h3, -⟩ := frz_fidx X (fun _ => (univ : Set Ω)) n ω
  rcases h3 with h | h
  · rw [h1, h]
  · exact absurd trivial h

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

variable (he : Function.Surjective e)
include he

end Sharp

end G26G


-- ===== Solutions.G26.WinPar =====

/-! ### Lemma G.26: the window parameters and the per-round failure bound -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma log_e_ge {x : ℝ} (hx : 1 ≤ x) : 1 ≤ Real.log (Real.exp 1 * x) := by
  rw [Real.log_mul (Real.exp_pos 1).ne' (by linarith), Real.log_exp]
  linarith [Real.log_nonneg hx]

lemma Hcf_facts {C : ℝ} (hC : 0 ≤ C) : 1 ≤ nCf C ∧ C ≤ nCf C ∧ (nCf C : ℝ) + 1 ≤ Hcf C ∧ 1 ≤ Hcf C := by
  have h1 : C ≤ (nCf C : ℝ) := by
    unfold nCf; push_cast; linarith [Nat.le_ceil C]
  have hn : (1 : ℝ) ≤ (nCf C : ℝ) + 1 := by linarith [(Nat.cast_nonneg (nCf C) : (0 : ℝ) ≤ _)]
  have hl := log_e_ge hn
  have h3 : (nCf C : ℝ) + 1 ≤ Hcf C := by
    unfold Hcf; nlinarith
  exact ⟨by unfold nCf; omega, h1, h3, by linarith⟩

lemma root8_of_pow {a : ℝ} (ha : 0 ≤ a) : root8 (a ^ 8) = a :=
  (pow_left_inj₀ (root8_nonneg _) ha (by norm_num : (8 : ℕ) ≠ 0)).1 (root8_pow (by positivity))

lemma root8_le_of {x a : ℝ} (ha : 0 ≤ a) (h : x ≤ a ^ 8) : root8 x ≤ a :=
  (root8_mono h).trans (root8_of_pow ha).le

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

omit he in
lemma κ1_ge : 16 ≤ H.κ1 := by
  have := H.Lam1_pos; have : (0 : ℝ) ≤ max 1 (cK d) := le_trans zero_le_one (le_max_left _ _)
  unfold κ1; nlinarith

omit he in
lemma ε0_pos : 0 < H.ε0 := by have := H.κ1_ge; unfold ε0; positivity

omit he in
lemma ε0_le : H.ε0 ≤ (1 / (8 * H.κ1)) ^ 8 ∧ H.ε0 ≤ 1 / 2 := by
  have hk := H.κ1_ge
  have h8 : (1 : ℝ) ≤ (8 * H.κ1) ^ 8 := one_le_pow₀ (by linarith)
  unfold ε0
  constructor
  · rw [div_pow, one_pow]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith

set_option maxHeartbeats 2000000 in
/-- **the window parameter facts**: for `t ≥ t0`, every hypothesis of the window lemmas holds -/
theorem win_ok {C : ℝ} (hC : 0 ≤ C) {t : ℕ} (ht0 : H.t0f he C ≤ t) :
    let Hc := Hcf C
    let m := mw (H.M0 he) Hc t
    let z := zw m t
    1 ≤ m ∧ m ≤ t ∧ 2 * ((m : ℝ) + 1) ≤ (t : ℝ) + 1 ∧
    cTw d H.sig⁻¹ H.kb ≤ root8 ((m : ℝ) + 1) ∧ H.sig⁻¹ * C ≤ (m : ℝ) + 1 ∧
    2 * H.Sref he + 2 ≤ m ∧
    2 ^ 21 * (((nCf C : ℝ) + 1) * Real.log (Real.exp 1 * ((nCf C : ℝ) + 1))) ≤ (m : ℝ) + 1 ∧
    0 < z ∧ (m : ℝ) + 1 ≤ z ∧
    z ≤ ((t : ℝ) + 1) * root8 (((m : ℝ) + 1) / ((t : ℝ) + 1)) ^ 7 ∧
    H.κ1 * root8 (((m : ℝ) + 1) / ((t : ℝ) + 1)) ≤ 1 ∧
    (((m : ℝ) + 1) / z) ^ 8 ≤ ((m : ℝ) + 1) / ((t : ℝ) + 1) ∧
    ((t : ℝ) + 1) / ((m : ℝ) + 1) ≤ (m : ℝ) + 1 ∧
    tauB z t ≤ (t : ℝ) + 1 ∧
    (tauB z t / ((t : ℝ) + 1)) ^ 16 ≤
      2 ^ 16 * (1 / ((t : ℝ) + 1) ^ 2 + 4 ^ 16 * (((m : ℝ) + 1) / ((t : ℝ) + 1)) ^ 4) ∧
    (((m : ℝ) + 1) / ((t : ℝ) + 1)) ^ 4 ≤
      16 * (((H.M0 he : ℝ) + 3) ^ 4 + 1) * (Hc / ((t : ℝ) + 1)) ^ 2 ∧
    (((nCf C : ℝ) + 1) ^ 4 + 1) / ((m : ℝ) + 1) ^ 4 ≤
      (Hc / ((t : ℝ) + 1)) ^ 2 + 1 / ((t : ℝ) + 1) ^ 2 ∧
    1 / ((m : ℝ) + 1) ^ 4 ≤ 1 / ((t : ℝ) + 1) ^ 2 := by
  intro Hc m z
  obtain ⟨hn1, hCn, hnH, hH1⟩ := Hcf_facts hC
  have hl0 : 0 ≤ H.sig⁻¹ := inv_nonneg.2 H.sig_pos.le
  have hcT1 : 0 ≤ cTw d H.sig⁻¹ H.kb := by
    unfold cTw; have := G2R.gB_pos (d := d); have := H.kb_ge.1; positivity
  set M0 := H.M0 he with hM0
  have hM0r : cTw d H.sig⁻¹ H.kb ^ 8 + H.sig⁻¹ + 2 ^ 22 ≤ (M0 : ℝ) := by
    rw [hM0]; unfold Sharp.M0; push_cast
    have := Nat.le_ceil (cTw d H.sig⁻¹ H.kb ^ 8 + H.sig⁻¹ + 2 ^ 22); linarith
  have hM0S : 2 * H.Sref he + 2 ≤ M0 := by rw [hM0]; unfold Sharp.M0; omega
  have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  -- the window start
  have hm1 : (M0 : ℝ) * Hc ≤ (m : ℝ) := by
    show (M0 : ℝ) * Hc ≤ ((mw M0 Hc t : ℕ) : ℝ)
    unfold mw; push_cast
    linarith [Nat.le_ceil ((M0 : ℝ) * Hc), (Nat.cast_nonneg _ : (0 : ℝ) ≤
      (⌈Real.sqrt (Hc * ((t : ℝ) + 1))⌉₊ : ℕ))]
  have hm2 : Real.sqrt (Hc * ((t : ℝ) + 1)) ≤ (m : ℝ) := by
    show Real.sqrt (Hc * ((t : ℝ) + 1)) ≤ ((mw M0 Hc t : ℕ) : ℝ)
    unfold mw; push_cast
    linarith [Nat.le_ceil (Real.sqrt (Hc * ((t : ℝ) + 1))), (Nat.cast_nonneg _ : (0 : ℝ) ≤
      (⌈(M0 : ℝ) * Hc⌉₊ : ℕ))]
  have hm3 : (m : ℝ) + 1 ≤ ((M0 : ℝ) + 3) * Hc + Real.sqrt (Hc * ((t : ℝ) + 1)) := by
    show ((mw M0 Hc t : ℕ) : ℝ) + 1 ≤ _
    unfold mw; push_cast
    have a1 := Nat.ceil_lt_add_one (show 0 ≤ (M0 : ℝ) * Hc by positivity)
    have a2 := Nat.ceil_lt_add_one (Real.sqrt_nonneg (Hc * ((t : ℝ) + 1)))
    have : (3 : ℝ) ≤ 3 * Hc := by linarith
    linarith
  have hM0m : (M0 : ℝ) ≤ (m : ℝ) := le_trans (le_mul_of_one_le_right (by positivity) hH1) hm1
  have hmM : M0 ≤ m := by exact_mod_cast hM0m
  have hmsq : Hc * ((t : ℝ) + 1) ≤ ((m : ℝ) + 1) ^ 2 := by
    have h1 := Real.sq_sqrt (show 0 ≤ Hc * ((t : ℝ) + 1) by positivity)
    have h2 : Real.sqrt (Hc * ((t : ℝ) + 1)) ≤ (m : ℝ) + 1 := by linarith
    have h3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
    linarith
  -- `t ≥ t0`
  have hε := H.ε0_pos
  obtain ⟨hε8, hε2⟩ := H.ε0_le
  have hU0 : H.Uw he * Hc ≤ (t : ℝ) := by
    have := Nat.le_ceil (H.Uw he * Hc)
    have h' : ((H.t0f he C : ℕ) : ℝ) ≤ t := by exact_mod_cast ht0
    unfold t0f at h'; linarith
  have hU0a : 4 * ((M0 : ℝ) + 3) / H.ε0 ≤ H.Uw he := by
    unfold Uw; have : 0 ≤ 4 / H.ε0 ^ 2 := by positivity
    rw [← hM0]; linarith
  have hU0b : 4 / H.ε0 ^ 2 ≤ H.Uw he := by
    unfold Uw; have : 0 ≤ 4 * ((M0 : ℝ) + 3) / H.ε0 := by positivity
    linarith
  have hU0c : 256 ≤ H.Uw he := by
    unfold Uw; have : 0 ≤ 4 * ((M0 : ℝ) + 3) / H.ε0 := by positivity
    have : 0 ≤ 4 / H.ε0 ^ 2 := by positivity
    linarith
  have hHt : Hc / ((t : ℝ) + 1) ≤ H.ε0 ^ 2 / 4 := by
    rw [div_le_div_iff₀ ht1 (by norm_num)]
    have h1 : 4 / H.ε0 ^ 2 * Hc ≤ (t : ℝ) + 1 := by
      have := mul_le_mul_of_nonneg_right hU0b (by linarith : (0 : ℝ) ≤ Hc)
      linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h1
    linarith
  have hHt1 : Hc / ((t : ℝ) + 1) ≤ 1 := by
    have : H.ε0 ^ 2 / 4 ≤ 1 := by
      have := pow_le_pow_left₀ hε.le hε2 2
      linarith
    linarith
  have hαt : ((M0 : ℝ) + 3) * Hc / ((t : ℝ) + 1) ≤ H.ε0 / 4 := by
    rw [div_le_div_iff₀ ht1 (by norm_num)]
    have h1 : 4 * ((M0 : ℝ) + 3) / H.ε0 * Hc ≤ (t : ℝ) + 1 := by
      have := mul_le_mul_of_nonneg_right hU0a (by linarith : (0 : ℝ) ≤ Hc)
      linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hε] at h1
    linarith
  have hβt : Real.sqrt (Hc * ((t : ℝ) + 1)) / ((t : ℝ) + 1) = Real.sqrt (Hc / ((t : ℝ) + 1)) := by
    have e : Hc / ((t : ℝ) + 1) = Hc * ((t : ℝ) + 1) / ((t : ℝ) + 1) ^ 2 := by
      field_simp <;> ring
    rw [e, Real.sqrt_div (by positivity), Real.sqrt_sq ht1.le]
  have hβ : Real.sqrt (Hc / ((t : ℝ) + 1)) ≤ H.ε0 / 2 := by
    calc Real.sqrt (Hc / ((t : ℝ) + 1)) ≤ Real.sqrt ((H.ε0 / 2) ^ 2) :=
          Real.sqrt_le_sqrt (by rw [div_pow]; linarith)
      _ = H.ε0 / 2 := Real.sqrt_sq (by positivity)
  set x := ((m : ℝ) + 1) / ((t : ℝ) + 1) with hx
  have hx0 : 0 < x := by positivity
  have hxab : x ≤ ((M0 : ℝ) + 3) * Hc / ((t : ℝ) + 1) + Real.sqrt (Hc / ((t : ℝ) + 1)) := by
    rw [hx, ← hβt, ← add_div]; exact div_le_div_of_nonneg_right hm3 ht1.le
  have hxε : x ≤ H.ε0 := by linarith
  have hx1 : x ≤ 1 / 2 := hxε.trans hε2
  -- the root
  set ξ := root8 x with hξ
  have hξ0 : 0 < ξ := by
    rw [hξ, root8_eq_rpow hx0.le]; exact Real.rpow_pos_of_pos hx0 _
  have hξ8 : ξ ^ 8 = x := root8_pow hx0.le
  have hk := H.κ1_ge
  have hξκ : ξ ≤ 1 / (8 * H.κ1) := root8_le_of (by positivity) (hxε.trans hε8)
  have hξ1 : ξ ≤ 1 / 8 := hξκ.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have hξ1' : ξ ≤ 1 := by linarith
  have hz : z = ((t : ℝ) + 1) * ξ ^ 7 := rfl
  have hm8 : (m : ℝ) + 1 = ((t : ℝ) + 1) * ξ ^ 8 := by rw [hξ8, hx]; field_simp
  have hz0 : 0 < z := by rw [hz]; positivity
  have hmz : (m : ℝ) + 1 ≤ z := by
    rw [hm8, hz]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hξ0.le hξ1' (by norm_num)) ht1.le
  have hzx : ((m : ℝ) + 1) / z = ξ := by
    rw [hm8, hz]; field_simp
  -- the buffer at `t`
  set rt := root8 ((t : ℝ) + 1) with hrt
  have hrt8 : rt ^ 8 = (t : ℝ) + 1 := root8_pow ht1.le
  have ht256 : (256 : ℝ) ≤ (t : ℝ) + 1 := by
    have := mul_le_mul hU0c hH1 (by norm_num) (by linarith)
    linarith
  have hrt2 : 2 ≤ rt := le_root8 (by norm_num) (by norm_num; linarith)
  have hrt0 : 0 < rt := by linarith
  have hτ : tauB z t = rt ^ 7 + 4 * z := by
    unfold tauB; rw [rpow78_eq ht1.le]
  have hy : tauB z t / ((t : ℝ) + 1) = 1 / rt + 4 * ξ ^ 7 := by
    rw [hτ, hz, ← hrt8]; field_simp <;> ring
  have hξ7 : ξ ^ 7 ≤ 1 / 8 := (pow_le_of_le_one hξ0.le hξ1' (by norm_num)).trans hξ1
  have hξ7' : 4 * ξ ^ 7 ≤ 1 / 2 := by linarith
  have hyle : tauB z t / ((t : ℝ) + 1) ≤ 1 := by
    rw [hy]; have : 1 / rt ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hrt2
    linarith
  have hτt : tauB z t ≤ (t : ℝ) + 1 := by
    have := (div_le_one ht1).1 hyle; exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hz0, hmz, le_of_eq rfl, ?_, ?_, ?_, hτt, ?_, ?_, ?_, ?_⟩
  · have : 2 ≤ M0 := by omega
    omega
  · have h : 2 * ((m : ℝ) + 1) ≤ (t : ℝ) + 1 := by
      have := (div_le_iff₀ ht1).1 (hx ▸ hx1 : ((m : ℝ) + 1) / ((t : ℝ) + 1) ≤ 1 / 2)
      linarith
    have : (m : ℝ) ≤ t := by linarith
    exact_mod_cast this
  · have := (div_le_iff₀ ht1).1 (hx ▸ hx1 : ((m : ℝ) + 1) / ((t : ℝ) + 1) ≤ 1 / 2)
    linarith
  · refine root8_ge_of hcT1 ?_
    have : 0 ≤ H.sig⁻¹ := hl0
    linarith
  · calc H.sig⁻¹ * C ≤ H.sig⁻¹ * Hc := mul_le_mul_of_nonneg_left (by linarith) hl0
      _ ≤ (M0 : ℝ) * Hc := mul_le_mul_of_nonneg_right (by linarith [pow_nonneg hcT1 8]) (by linarith)
      _ ≤ (m : ℝ) + 1 := by linarith
  · omega
  · show 2 ^ 21 * Hc ≤ (m : ℝ) + 1
    have : (2 : ℝ) ^ 21 ≤ M0 := by linarith [pow_nonneg hcT1 8]
    have := mul_le_mul_of_nonneg_right this (by linarith : (0 : ℝ) ≤ Hc)
    linarith
  · calc H.κ1 * ξ ≤ H.κ1 * (1 / (8 * H.κ1)) := mul_le_mul_of_nonneg_left hξκ (by linarith)
      _ = 1 / 8 := by field_simp
      _ ≤ 1 := by norm_num
  · rw [hzx, hξ8]
  · rw [div_le_iff₀ (by positivity)]
    have : (t : ℝ) + 1 ≤ Hc * ((t : ℝ) + 1) := le_mul_of_one_le_left ht1.le hH1
    calc (t : ℝ) + 1 ≤ ((m : ℝ) + 1) ^ 2 := this.trans hmsq
      _ = ((m : ℝ) + 1) * ((m : ℝ) + 1) := sq _
  · rw [hy]
    refine (add_pow_le_two (by positivity) (by positivity) 16).trans ?_
    gcongr
    · rw [div_pow, one_pow, ← hrt8, ← pow_mul]
    · rw [mul_pow, show (ξ ^ 7) ^ 16 = (ξ ^ 8) ^ 14 by rw [← pow_mul, ← pow_mul], hξ8]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx0.le (by linarith) (by norm_num))
        (by positivity)
  · -- `x^4 ≤ 8((M0+3)^4+1)(Hc/(t+1))^2`
    set h := Hc / ((t : ℝ) + 1) with hh
    have hh0 : 0 ≤ h := by positivity
    have hα : ((M0 : ℝ) + 3) * Hc / ((t : ℝ) + 1) = ((M0 : ℝ) + 3) * h := by rw [hh]; ring
    rw [hα] at hxab
    have h4 := pow_le_pow_left₀ hx0.le hxab 4
    have h5 := add_pow_le_two (by positivity : 0 ≤ ((M0 : ℝ) + 3) * h)
      (Real.sqrt_nonneg h) 4
    have hs4 : Real.sqrt h ^ 4 = h ^ 2 := by
      rw [show 4 = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hh0]
    have hh4 : h ^ 4 ≤ h ^ 2 := pow_le_pow_of_le_one hh0 hHt1 (by norm_num)
    rw [hs4, mul_pow] at h5
    have : ((M0 : ℝ) + 3) ^ 4 * h ^ 4 ≤ ((M0 : ℝ) + 3) ^ 4 * h ^ 2 :=
      mul_le_mul_of_nonneg_left hh4 (by positivity)
    linarith
  · -- `((nC+1)^4+1)/(m+1)^4 ≤ (Hc/(t+1))^2 + 1/(t+1)^2`
    have hm4 : Hc ^ 2 * ((t : ℝ) + 1) ^ 2 ≤ ((m : ℝ) + 1) ^ 4 := by
      have := pow_le_pow_left₀ (by positivity) hmsq 2
      rw [mul_pow, ← pow_mul] at this; exact this
    have hm4' : ((t : ℝ) + 1) ^ 2 ≤ ((m : ℝ) + 1) ^ 4 :=
      le_trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hH1)) hm4
    have hn4 : ((nCf C : ℝ) + 1) ^ 4 ≤ Hc ^ 2 * Hc ^ 2 := by
      rw [← pow_add]; exact pow_le_pow_left₀ (by positivity) hnH 4
    have e1 : ((nCf C : ℝ) + 1) ^ 4 / ((m : ℝ) + 1) ^ 4 ≤ Hc ^ 2 / ((t : ℝ) + 1) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc ((nCf C : ℝ) + 1) ^ 4 * ((t : ℝ) + 1) ^ 2 ≤ Hc ^ 2 * Hc ^ 2 * ((t : ℝ) + 1) ^ 2 :=
            mul_le_mul_of_nonneg_right hn4 (by positivity)
        _ = Hc ^ 2 * (Hc ^ 2 * ((t : ℝ) + 1) ^ 2) := by ring
        _ ≤ Hc ^ 2 * ((m : ℝ) + 1) ^ 4 := mul_le_mul_of_nonneg_left hm4 (by positivity)
    have e2 : 1 / ((m : ℝ) + 1) ^ 4 ≤ 1 / ((t : ℝ) + 1) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) hm4'
    rw [add_div, div_pow]
    linarith
  · have hm4 : Hc ^ 2 * ((t : ℝ) + 1) ^ 2 ≤ ((m : ℝ) + 1) ^ 4 := by
      have := pow_le_pow_left₀ (by positivity) hmsq 2
      rw [mul_pow, ← pow_mul] at this; exact this
    exact one_div_le_one_div_of_le (by positivity)
      (le_trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hH1)) hm4)

end Sharp

end G26G


theorem _root_.solution : type_of% @G26G.Sharp.win_ok := @G26G.Sharp.win_ok
