-- Prove2me | solution 1 for G26G.Sharp.ref_block
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:40:49.296919+00:00
-- url     : https://prove2.me/submissions/429c352f-4272-467f-b0fa-bdbc58d8cc69

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_G26_body
import Definitions.Def_IAFTRL_G26_run
import Definitions.Def_IAFTRL_G26_window
import Theorems.Thm_G26_FI_absMax_env
import Theorems.Thm_G26G_Sharp_far_prob
import Theorems.Thm_G26G_Sharp_prep_prob
import Theorems.Thm_G26G_ref_block_alg
import Theorems.Thm_G26R_runK_FI
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

/-- combinations of `n` points of `K` -/
def combSet (K : Set E) (n : ℕ) : Set E :=
  (fun p : (Fin n → ℝ) × (Fin n → E) => ∑ i, p.1 i • p.2 i) ''
    (stdSimplex ℝ (Fin n) ×ˢ Set.univ.pi (fun _ => K))

lemma combSet_succ {K : Set E} {z₀ : E} (hz₀ : z₀ ∈ K) (n : ℕ) :
    combSet K n ⊆ combSet K (n + 1) := by
  rintro x ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
  refine ⟨⟨Fin.snoc w 0, Fin.snoc z z₀⟩, ⟨⟨fun i => ?_, ?_⟩, fun i _ => ?_⟩, ?_⟩
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simpa using hw.1 j
  · simp [Fin.sum_univ_castSucc, hw.2]
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hz₀
    · simpa using hz j (mem_univ _)
  · simp [Fin.sum_univ_castSucc]

lemma combSet_mono {K : Set E} (hK : K.Nonempty) {k N : ℕ} (h : k ≤ N) :
    combSet K k ⊆ combSet K N := by
  obtain ⟨z₀, hz₀⟩ := hK
  induction N, h using Nat.le_induction with
  | base => exact le_rfl
  | succ N _ ih => exact ih.trans (combSet_succ hz₀ N)

lemma combSet_sub_hull (K : Set E) (n : ℕ) : combSet K n ⊆ convexHull ℝ K := by
  rintro x ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
  exact (convex_convexHull ℝ K).sum_mem (fun i _ => hw.1 i) hw.2
    (fun i _ => subset_convexHull ℝ K (hz i (mem_univ _)))

variable [FiniteDimensional ℝ E]

lemma hull_sub_combSet (K : Set E) :
    convexHull ℝ K ⊆ combSet K (Module.finrank ℝ E + 1) := by
  intro x hx
  obtain ⟨ι, _, z, w, hzK, hai, hw0, hw1, hsum⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hcard : Fintype.card ι ≤ Module.finrank ℝ E + 1 :=
    hai.card_le_finrank_succ.trans (Nat.succ_le_succ (Submodule.finrank_le _))
  have hne : K.Nonempty := convexHull_nonempty_iff.1 ⟨x, hx⟩
  refine combSet_mono hne hcard ?_
  let σ := Fintype.equivFin ι
  refine ⟨⟨w ∘ σ.symm, z ∘ σ.symm⟩, ⟨⟨fun i => (hw0 _).le, ?_⟩, fun i _ => hzK ⟨_, rfl⟩⟩, ?_⟩
  · simpa [Function.comp] using (Equiv.sum_comp σ.symm w).trans hw1
  · simp only [Function.comp]
    rw [← hsum]
    exact Equiv.sum_comp σ.symm (fun i => w i • z i)

lemma isCompact_convexHull_of {K : Set E} (hK : IsCompact K) : IsCompact (convexHull ℝ K) := by
  have : convexHull ℝ K = combSet K (Module.finrank ℝ E + 1) :=
    (hull_sub_combSet K).antisymm (combSet_sub_hull K _)
  rw [this]
  refine IsCompact.image ((isCompact_stdSimplex ℝ (Fin _)).prod (isCompact_univ_pi fun _ => hK)) ?_
  fun_prop

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


-- ===== Solutions.G2.Lex =====

/-! ### Lexicographic minimizers exist on compact sets -/

open Set IAFTRL

namespace G2L

variable {d : ℕ}

lemma lex_min_exists {M : Set (Fin d → ℝ)} (hM : IsCompact M) (hne : M.Nonempty) :
    ∃ b ∈ M, ∀ b' ∈ M, toLex b ≤ toLex b' := by
  have key : ∀ n : ℕ, ∃ b ∈ M, ∀ b' ∈ M, (∀ j : Fin d, j.val < n → b j = b' j) ∨
      ∃ i : Fin d, i.val < n ∧ (∀ j : Fin d, j < i → b j = b' j) ∧ b i < b' i := by
    intro n
    induction n with
    | zero =>
      obtain ⟨b, hb⟩ := hne
      exact ⟨b, hb, fun b' _ => Or.inl fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ n ih =>
      obtain ⟨b, hbM, hb⟩ := ih
      by_cases hnd : n < d
      · set M' := {b' ∈ M | ∀ j : Fin d, j.val < n → b' j = b j} with hM'
        have hM'c : IsCompact M' := by
          change IsCompact (M ∩ {b' : Fin d → ℝ | ∀ j : Fin d, j.val < n → b' j = b j})
          refine hM.inter_right ?_
          have : {b' : Fin d → ℝ | ∀ j : Fin d, j.val < n → b' j = b j} =
              ⋂ j : Fin d, ⋂ (_ : j.val < n), {b' | b' j = b j} := by
            ext b'; simp
          rw [this]
          exact isClosed_iInter fun j => isClosed_iInter fun _ =>
            isClosed_eq (continuous_apply j) continuous_const
        have hM'ne : M'.Nonempty := ⟨b, hbM, fun _ _ => rfl⟩
        obtain ⟨bs, ⟨hbsM, hbsb⟩, hmin⟩ :=
          hM'c.exists_isMinOn hM'ne (continuous_apply (⟨n, hnd⟩ : Fin d)).continuousOn
        refine ⟨bs, hbsM, fun b' hb'M => ?_⟩
        rcases hb b' hb'M with hA | ⟨i, hi, hpre, hlt⟩
        · have hb'M' : b' ∈ M' := ⟨hb'M, fun j hj => (hA j hj).symm⟩
          have hle : bs ⟨n, hnd⟩ ≤ b' ⟨n, hnd⟩ := hmin hb'M'
          rcases hle.lt_or_eq with hlt | heq
          · refine Or.inr ⟨⟨n, hnd⟩, Nat.lt_succ_self n, fun j hj => ?_, hlt⟩
            have hj' : j.val < n := hj
            rw [hbsb j hj', hA j hj']
          · refine Or.inl fun j hj => ?_
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
            · rw [hbsb j hj', hA j hj']
            · have : j = ⟨n, hnd⟩ := Fin.ext hj'
              rw [this, heq]
        · refine Or.inr ⟨i, Nat.lt_succ_of_lt hi, fun j hj => ?_, ?_⟩
          · have hj' : j.val < n := lt_trans hj hi
            rw [hbsb j hj', hpre j hj]
          · rw [hbsb i hi]; exact hlt
      · refine ⟨b, hbM, fun b' hb'M => ?_⟩
        rcases hb b' hb'M with hA | ⟨i, hi, hpre, hlt⟩
        · exact Or.inl fun j _ => hA j (lt_of_lt_of_le j.isLt (not_lt.1 hnd))
        · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hpre, hlt⟩
  obtain ⟨b, hbM, hb⟩ := key d
  refine ⟨b, hbM, fun b' hb'M => ?_⟩
  rcases hb b' hb'M with hA | ⟨i, -, hpre, hlt⟩
  · have : b = b' := funext fun j => hA j j.isLt
    rw [this]
  · exact le_of_lt ⟨i, hpre, hlt⟩

lemma lexMinimizer_mem {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) (hne : ℬ.Nonempty)
    (v : Fin d → ℝ) : lexMinimizer ℬ v ∈ ℬ := by
  have hc : Continuous fun x : Fin d → ℝ => x ⬝ᵥ v := by
    simp only [dotProduct]; fun_prop
  obtain ⟨b₀, hb₀, hmin⟩ := hℬ.exists_isMinOn hne hc.continuousOn
  set M := ℬ ∩ {b | b ⬝ᵥ v ≤ b₀ ⬝ᵥ v} with hM
  have hMc : IsCompact M := hℬ.inter_right (isClosed_le hc continuous_const)
  obtain ⟨b, ⟨hbℬ, hbv⟩, hlex⟩ := lex_min_exists hMc ⟨b₀, hb₀, show b₀ ⬝ᵥ v ≤ b₀ ⬝ᵥ v from le_refl _⟩
  have h : ∃ b ∈ ℬ, (∀ a ∈ ℬ, b ⬝ᵥ v ≤ a ⬝ᵥ v) ∧
      ∀ b' ∈ ℬ, (∀ a ∈ ℬ, b' ⬝ᵥ v ≤ a ⬝ᵥ v) → toLex b ≤ toLex b' :=
    ⟨b, hbℬ, fun a ha => le_trans hbv (hmin ha),
      fun b' hb' hb'min => hlex b' ⟨hb', hb'min b₀ hb₀⟩⟩
  unfold lexMinimizer
  rw [dif_pos h]
  exact (Classical.choose_spec h).1

lemma cand_mem {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) (hne : ℬ.Nonempty)
    (e : ℕ → Fin d → ℚ) (m : ℕ) : cand ℬ e m ∈ ℬ :=
  lexMinimizer_mem hℬ hne _

end G2L


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

lemma Kset_compact {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) : IsCompact (Kset ℬ) :=
  T31.isCompact_convexHull_of hℬ

lemma span_B {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) : Submodule.span ℝ ℬ = ⊤ := by
  rw [eq_top_iff, ← hspan]
  refine Submodule.span_le.2 fun a ha => ?_
  have : convexHull ℝ ℬ ⊆ Submodule.span ℝ ℬ :=
    convexHull_min Submodule.subset_span (Submodule.span ℝ ℬ).convex
  exact this (hgen.2 ha)

lemma B_nonempty {𝒜 ℬ : Set (Fin d → ℝ)} (hd : 1 ≤ d) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) : ℬ.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have := span_B hgen hspan
  rw [h, Submodule.span_empty] at this
  have hne : (Pi.single (⟨0, hd⟩ : Fin d) (1 : ℝ)) ∈ (⊤ : Submodule ℝ (Fin d → ℝ)) := trivial
  rw [← this, Submodule.mem_bot] at hne
  have := congrFun hne ⟨0, hd⟩
  simp at this

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

lemma gbeta_pos (hd : 1 ≤ d) (t : ℕ) : 0 < gbeta d t := by
  unfold gbeta
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  positivity

lemma gB_pos : 0 < gB d := by unfold gB; positivity

section Bounds

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝒜 ℬ : Set (Fin d → ℝ)}
  {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

end Bounds

end G2R


-- ===== Solutions.G1.RefId =====

/-! ### The reference is `a*` on Laplace histories, for large rounds -/

open MeasureTheory ProbabilityTheory Set IAFTRL

namespace G1R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}

lemma hPen_ge (m : ℕ) : (m : ℝ) + 2 ≤ hPen ℬ e m := by
  classical
  unfold hPen
  have := Finset.sum_nonneg (s := (Finset.range m).filter (· ∈ Jset ℬ e))
    (f := fun i => Real.exp ((sNorm ℬ (cand ℬ e m - cand ℬ e i))⁻¹ ^ 8))
    (fun _ _ => (Real.exp_pos _).le)
  linarith

lemma hPen_far {j m : ℕ} (hj : j ∈ Jset ℬ e) (hjm : j < m) :
    (m : ℝ) + 2 + Real.exp ((sNorm ℬ (cand ℬ e m - cand ℬ e j))⁻¹ ^ 8) ≤ hPen ℬ e m := by
  classical
  have hmem : j ∈ (Finset.range m).filter (· ∈ Jset ℬ e) :=
    Finset.mem_filter.2 ⟨Finset.mem_range.2 hjm, hj⟩
  have hsum := Finset.single_le_sum
    (f := fun i => Real.exp ((sNorm ℬ (cand ℬ e m - cand ℬ e i))⁻¹ ^ 8))
    (fun _ _ => (Real.exp_pos _).le) hmem
  unfold hPen
  linarith

end G1R


-- ===== Solutions.G26.Supp =====

/-! ### Support functions and extrema of affine fields on a compact body -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {d : ℕ}

/-- the `ℓ¹` radius of `D` -/
noncomputable def rad1 (D : Set (Fin d → ℝ)) : ℝ := sSup ((fun u : Fin d → ℝ => ∑ i, |u i|) '' D)

lemma abs_dot_le (u v : Fin d → ℝ) : |u ⬝ᵥ v| ≤ (∑ i, |u i|) * ‖v‖ := by
  unfold dotProduct
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (abs_nonneg _)

section

variable {D : Set (Fin d → ℝ)} (hD : IsCompact D)
include hD

lemma bdd_img (w : Fin d → ℝ) : BddAbove ((fun u => u ⬝ᵥ w) '' D) :=
  (hD.image (by simp only [dotProduct]; fun_prop)).bddAbove

lemma le_supp {u : Fin d → ℝ} (hu : u ∈ D) (w : Fin d → ℝ) : u ⬝ᵥ w ≤ supp D w :=
  le_csSup (bdd_img hD w) ⟨u, hu, rfl⟩

lemma supp_mem (hne : D.Nonempty) (w : Fin d → ℝ) : ∃ u ∈ D, u ⬝ᵥ w = supp D w := by
  have hc : IsCompact ((fun u => u ⬝ᵥ w) '' D) :=
    hD.image (by simp only [dotProduct]; fun_prop)
  obtain ⟨u, hu, he⟩ := hc.sSup_mem (hne.image _)
  exact ⟨u, hu, he⟩

lemma le_rad1 {u : Fin d → ℝ} (hu : u ∈ D) : ∑ i, |u i| ≤ rad1 D :=
  le_csSup (hD.image (by fun_prop)).bddAbove ⟨u, hu, rfl⟩

lemma supp_sub_le (hne : D.Nonempty) (w w' : Fin d → ℝ) :
    supp D w - supp D w' ≤ rad1 D * ‖w - w'‖ := by
  obtain ⟨u, hu, he⟩ := supp_mem hD hne w
  have h1 := le_supp hD hu w'
  have h2 := abs_dot_le u (w - w')
  have h3 : (∑ i, |u i|) * ‖w - w'‖ ≤ rad1 D * ‖w - w'‖ :=
    mul_le_mul_of_nonneg_right (le_rad1 hD hu) (norm_nonneg _)
  rw [dotProduct_sub] at h2
  have := (abs_le.1 h2).2
  linarith

lemma rad1_nonneg (hne : D.Nonempty) : 0 ≤ rad1 D := by
  obtain ⟨u, hu⟩ := hne
  exact le_trans (Finset.sum_nonneg fun i _ => abs_nonneg _) (le_rad1 hD hu)

lemma supp_lip (hne : D.Nonempty) : LipschitzWith (Real.toNNReal (rad1 D)) (supp D) := by
  refine LipschitzWith.of_dist_le_mul fun w w' => ?_
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (rad1_nonneg hD hne)]
  refine abs_le.2 ⟨?_, supp_sub_le hD hne w w'⟩
  have := supp_sub_le hD hne w' w
  rw [norm_sub_rev] at this
  linarith

lemma supp_cont (hne : D.Nonempty) : Continuous (supp D) := (supp_lip hD hne).continuous

lemma negMax_ge {u : Fin d → ℝ} (hu : u ∈ D) (V : Fin d → ℝ) (c : ℝ) :
    -(u ⬝ᵥ V + c) ≤ negMax D V c := by
  have := le_supp hD hu (-V)
  rw [dotProduct_neg] at this
  unfold negMax; linarith

lemma posMax_ge {u : Fin d → ℝ} (hu : u ∈ D) (V : Fin d → ℝ) (c : ℝ) :
    u ⬝ᵥ V + c ≤ posMax D V c := by
  have := le_supp hD hu V
  unfold posMax; linarith

lemma abs_le_absMax {u : Fin d → ℝ} (hu : u ∈ D) (V : Fin d → ℝ) (c : ℝ) :
    |u ⬝ᵥ V + c| ≤ absMax D V c := by
  unfold absMax
  refine abs_le.2 ⟨?_, le_trans (posMax_ge hD hu V c) (le_max_left _ _)⟩
  have := le_trans (negMax_ge hD hu V c) (le_max_right (posMax D V c) _)
  linarith

omit hD in
lemma negMax_le_absMax (V : Fin d → ℝ) (c : ℝ) : negMax D V c ≤ absMax D V c :=
  le_max_right _ _

lemma negMax_mem (hne : D.Nonempty) (V : Fin d → ℝ) (c : ℝ) :
    ∃ u ∈ D, -(u ⬝ᵥ V + c) = negMax D V c := by
  obtain ⟨u, hu, he⟩ := supp_mem hD hne (-V)
  refine ⟨u, hu, ?_⟩
  rw [dotProduct_neg] at he
  unfold negMax; linarith

lemma posMax_mem (hne : D.Nonempty) (V : Fin d → ℝ) (c : ℝ) :
    ∃ u ∈ D, u ⬝ᵥ V + c = posMax D V c := by
  obtain ⟨u, hu, he⟩ := supp_mem hD hne V
  exact ⟨u, hu, by unfold posMax; linarith⟩

/-- the absolute maximum is attained -/
lemma absMax_mem (hne : D.Nonempty) (V : Fin d → ℝ) (c : ℝ) :
    ∃ u ∈ D, |u ⬝ᵥ V + c| = absMax D V c ∧ ∀ x ∈ D, |x ⬝ᵥ V + c| ≤ |u ⬝ᵥ V + c| := by
  obtain ⟨u1, hu1, h1⟩ := posMax_mem hD hne V c
  obtain ⟨u2, hu2, h2⟩ := negMax_mem hD hne V c
  rcases le_total (negMax D V c) (posMax D V c) with h | h
  · have hA : absMax D V c = posMax D V c := max_eq_left h
    have hval : |u1 ⬝ᵥ V + c| = absMax D V c := by
      rw [hA, h1]
      refine abs_of_nonneg ?_
      have := negMax_ge hD hu1 V c
      linarith
    exact ⟨u1, hu1, hval, fun x hx => hval ▸ abs_le_absMax hD hx V c⟩
  · have hA : absMax D V c = negMax D V c := max_eq_right h
    have hval : |u2 ⬝ᵥ V + c| = absMax D V c := by
      rw [hA, ← h2, abs_of_nonpos]
      have := posMax_ge hD hu2 V c
      linarith
    exact ⟨u2, hu2, hval, fun x hx => hval ▸ abs_le_absMax hD hx V c⟩

lemma negMax_cont (hne : D.Nonempty) :
    Continuous fun p : (Fin d → ℝ) × ℝ => negMax D p.1 p.2 := by
  unfold negMax
  exact ((supp_cont hD hne).comp continuous_fst.neg).sub continuous_snd

lemma posMax_cont (hne : D.Nonempty) :
    Continuous fun p : (Fin d → ℝ) × ℝ => posMax D p.1 p.2 := by
  unfold posMax
  exact ((supp_cont hD hne).comp continuous_fst).add continuous_snd

lemma absMax_cont (hne : D.Nonempty) :
    Continuous fun p : (Fin d → ℝ) × ℝ => absMax D p.1 p.2 :=
  (posMax_cont hD hne).max (negMax_cont hD hne)

lemma absMax_meas (hne : D.Nonempty) {Ω : Type*} {m : MeasurableSpace Ω} {V : Ω → Fin d → ℝ}
    {c : Ω → ℝ} (hV : Measurable V) (hc : Measurable c) :
    Measurable fun ω => absMax D (V ω) (c ω) := by
  have h := (absMax_cont hD hne).measurable
  exact h.comp (f := fun ω => (V ω, c ω)) (hV.prodMk hc)

end

end G26


-- ===== Solutions.G26.Iface =====

/-! ### The abstract affine-field interface of Lemma G.25 -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {d : ℕ} {Ω : Type*}

section

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

/-- the field at a fixed point is `F_n`-measurable -/
lemma FI.fz_meas (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) (u : Fin d → ℝ) :
    Measurable[F n] (fun ω => fz V c n ω u) := by
  unfold fz
  have h : Continuous fun p : (Fin d → ℝ) × ℝ => u ⬝ᵥ p.1 + p.2 := by
    simp only [dotProduct]; fun_prop
  exact h.measurable.comp ((I.Vm n hn).prodMk (I.cm n hn))

lemma FI.absMax_meas (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) :
    Measurable[F n] (fun ω => absMax D (V n ω) (c n ω)) :=
  G26.absMax_meas I.hD I.hne (I.Vm n hn) (I.cm n hn)

/-- deterministic envelope of the field and its extrema -/
lemma FI.env' (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ᵐ ω ∂μ, absMax D (V n ω) (c n ω) ≤ r ∧
      ∀ u ∈ D, |fz V c n ω u| ≤ r := by
  obtain ⟨r, hr⟩ := I.env n hn
  refine ⟨max r 0, le_max_right _ _, ?_⟩
  filter_upwards [hr] with ω h
  obtain ⟨x0, hx0, hval, -⟩ := absMax_mem I.hD I.hne (V n ω) (c n ω)
  have hA : absMax D (V n ω) (c n ω) ≤ max r 0 := by
    rw [← hval]; exact (h x0 hx0).trans (le_max_left _ _)
  exact ⟨hA, fun u hu => (abs_le_absMax I.hD hu _ _).trans hA⟩

end

end G26


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

lemma frz_eq_of_mem {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) {n : ℕ} {ω : Ω}
    (h : ω ∈ survS A n) : frz X A n ω = X n ω := by
  cases n with
  | zero => rfl
  | succ n => exact frz_eq X A (n + 1) ω (Or.inr (survS_anti A (by omega) h))

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

/-- the frozen pair `(V, c)` at time `n` equals the pair at a common earlier time -/
lemma frz_pair_exists (V : ℕ → Ω → (Fin d → ℝ)) (c : ℕ → Ω → ℝ) (A : ℕ → Set Ω) :
    ∀ n ω, ∃ i ≤ n, frz V A n ω = V i ω ∧ frz c A n ω = c i ω := by
  intro n ω
  induction n with
  | zero => exact ⟨0, le_rfl, rfl, rfl⟩
  | succ n ih =>
    by_cases h : ω ∈ survS A n
    · exact ⟨n + 1, le_rfl, by simp only [frz, if_pos h], by simp only [frz, if_pos h]⟩
    · obtain ⟨i, hi, he, he'⟩ := ih
      exact ⟨i, by omega, by rw [frz_succ_of_notMem V A h, he],
        by rw [frz_succ_of_notMem c A h, he']⟩

/-- the increment of the frozen field -/
lemma fxi_frz (V : ℕ → Ω → (Fin d → ℝ)) (c : ℕ → Ω → ℝ) (A : ℕ → Set Ω) (n : ℕ) (ω : Ω)
    (u : Fin d → ℝ) :
    fxi (frz V A) (frz c A) n ω u = (survS A n).indicator (fun ω => fxi V c n ω u) ω := by
  by_cases h : ω ∈ survS A n
  · rw [Set.indicator_of_mem h]
    unfold fxi fz
    rw [frz_eq_of_mem V A h, frz_eq_of_mem c A h]
    simp only [frz, if_pos h]
  · rw [Set.indicator_of_notMem h]
    unfold fxi fz
    rw [frz_succ_of_notMem V A h, frz_succ_of_notMem c A h]; ring

section

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma FI.Fmono' (I : FI D μ F T V c J β B lo hi m0) {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ T) :
    F m ≤ F n := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih => exact (ih (by omega)).trans (I.Fmono n (by omega))

lemma FI.survS_meas (I : FI D μ F T V c J β B lo hi m0) {A : ℕ → Set Ω}
    (hA : ∀ n ≤ T, MeasurableSet[F n] (A n)) {n : ℕ} (hn : n ≤ T) :
    MeasurableSet[F n] (survS A n) := by
  unfold survS
  refine Finset.measurableSet_biInter _ fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  exact I.Fmono' (by omega) hn _ (hA i (by omega))

lemma FI.frz_meas (I : FI D μ F T V c J β B lo hi m0) {A : ℕ → Set Ω}
    (hA : ∀ n ≤ T, MeasurableSet[F n] (A n)) {E : Type*} [MeasurableSpace E]
    (X : ℕ → Ω → E) (hX : ∀ n ≤ T, Measurable[F n] (X n)) :
    ∀ n ≤ T, Measurable[F n] (frz X A n) := by
  intro n hn
  induction n with
  | zero => exact hX 0 hn
  | succ n ih =>
    have hS := I.survS_meas hA (n := n) (by omega)
    have hmono := I.Fmono n (by omega)
    classical
    show Measurable[F (n + 1)] fun ω => if ω ∈ survS A n then X (n + 1) ω else frz X A n ω
    exact Measurable.ite (hmono _ hS) (hX (n + 1) hn) ((ih (by omega)).mono hmono le_rfl)

lemma FI.fxi_int [IsFiniteMeasure μ] (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n < T)
    {u : Fin d → ℝ} (hu : u ∈ D) :
    ∃ r : ℝ, Integrable (fun ω => fxi V c n ω u) μ ∧ ∀ᵐ ω ∂μ, |fxi V c n ω u| ≤ r := by
  obtain ⟨r0, -, hr0⟩ := I.env' hn.le
  obtain ⟨r1, -, hr1⟩ := I.env' (n := n + 1) hn
  have hb : ∀ᵐ ω ∂μ, |fxi V c n ω u| ≤ r1 + r0 := by
    filter_upwards [hr0, hr1] with ω h0 h1
    unfold fxi
    exact le_trans (abs_sub _ _) (add_le_add (h1.2 u hu) (h0.2 u hu))
  refine ⟨r1 + r0, ?_, hb⟩
  have hm : Measurable (fun ω => fxi V c n ω u) := by
    unfold fxi
    exact ((I.fz_meas hn u).mono (I.Fle (n + 1) hn) le_rfl).sub
      ((I.fz_meas hn.le u).mono (I.Fle n hn.le) le_rfl)
  exact Integrable.of_bound hm.aestronglyMeasurable _ (by
    filter_upwards [hb] with ω h; rwa [Real.norm_eq_abs])

lemma FI.frz_N0 (I : FI D μ F T V c J β B lo hi m0) (A : ℕ → Set Ω) {n : ℕ} (hn : n ≤ T) :
    ∀ᵐ ω ∂μ, 0 ≤ negMax D (frz V A n ω) (frz c A n ω) := by
  have hall : ∀ᵐ ω ∂μ, ∀ i : Fin (n + 1), 0 ≤ negMax D (V i ω) (c i ω) :=
    ae_all_iff.2 fun i => I.N0 i (by have := i.2; omega)
  filter_upwards [hall] with ω hω
  obtain ⟨i, hi, hV, hc⟩ := frz_pair_exists V c A n ω
  rw [hV, hc]; exact hω ⟨i, by omega⟩

/-- **freezing preserves the field interface** -/
theorem FI.freeze [IsFiniteMeasure μ] (I : FI D μ F T V c J β B lo hi m0) {A : ℕ → Set Ω}
    (hA : ∀ n ≤ T, MeasurableSet[F n] (A n)) (hlo : lo ≤ 0) (hhi : 0 ≤ hi)
    (hβ : ∀ n, 0 ≤ β n) (hB : 0 < B) {J' : ℕ → Set Ω} (hJ'm : ∀ n ≤ T, MeasurableSet[F n] (J' n))
    (hJ'mono : ∀ n, J' (n + 1) ⊆ J' n) (hAJ : ∀ n, survS A n ∩ J' n ⊆ J n) :
    FI D μ F T (frz V A) (frz c A) J' β B lo hi m0 where
  hD := I.hD
  hconv := I.hconv
  hne := I.hne
  Fle := I.Fle
  Fmono := I.Fmono
  Vm := I.frz_meas hA V I.Vm
  cm := I.frz_meas hA c I.cm
  Jm := hJ'm
  Jmono := hJ'mono
  env := by
    intro n hn
    have : ∀ i ∈ Finset.range (n + 1), ∃ r : ℝ, ∀ᵐ ω ∂μ, ∀ u ∈ D, |u ⬝ᵥ V i ω + c i ω| ≤ r :=
      fun i hi => I.env i (by have := Finset.mem_range.1 hi; omega)
    choose r hr using this
    refine ⟨∑ i ∈ (Finset.range (n + 1)).attach, max (r i.1 i.2) 0, ?_⟩
    have hall : ∀ᵐ ω ∂μ, ∀ i : Finset.range (n + 1), ∀ u ∈ D, |u ⬝ᵥ V i ω + c i ω| ≤ r i.1 i.2 :=
      ae_all_iff.2 fun i => hr i.1 i.2
    filter_upwards [hall] with ω hω u hu
    obtain ⟨i, hi, hV, hc⟩ := frz_pair_exists V c A n ω
    have hmem : i ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
    have hle : max (r i hmem) 0 ≤ ∑ j ∈ (Finset.range (n + 1)).attach, max (r j.1 j.2) 0 :=
      Finset.single_le_sum (f := fun j : Finset.range (n + 1) => max (r j.1 j.2) 0)
        (fun j _ => le_max_right _ _) (Finset.mem_attach _ ⟨i, hmem⟩)
    rw [hV, hc]
    exact ((hω ⟨i, hmem⟩ u hu).trans (le_max_left _ _)).trans hle
  N0 := fun n hn => I.frz_N0 A hn
  drift := by
    intro n hm0 hn u hu
    have hS := I.survS_meas hA (n := n) hn.le
    obtain ⟨r, hint, -⟩ := I.fxi_int hn hu
    have hce : μ[fun ω => fxi (frz V A) (frz c A) n ω u | F n] =ᵐ[μ]
        (survS A n).indicator (μ[fun ω => fxi V c n ω u | F n]) := by
      have e : (fun ω => fxi (frz V A) (frz c A) n ω u) =
          (survS A n).indicator (fun ω => fxi V c n ω u) := by
        funext ω; exact fxi_frz V c A n ω u
      rw [e]
      exact condExp_indicator hint hS
    filter_upwards [hce, I.drift n hm0 hn u hu] with ω h1 h2 hJ
    rw [h1]
    by_cases hω : ω ∈ survS A n
    · rw [Set.indicator_of_mem hω]; exact h2 (hAJ n ⟨hω, hJ⟩)
    · rw [Set.indicator_of_notMem hω]; exact ⟨hlo, hhi⟩
  mag := by
    intro n hm0 hn
    filter_upwards [I.mag n hm0 hn, I.frz_N0 A hn.le] with ω hω hN hJ u hu
    by_cases hS : ω ∈ survS A n
    · rw [fxi_frz, Set.indicator_of_mem hS, fz, frz_eq_of_mem V A hS, frz_eq_of_mem c A hS]
      exact hω (hAJ n ⟨hS, hJ⟩) u hu
    · rw [fxi_frz, Set.indicator_of_notMem hS, abs_zero]
      have h1 := negMax_ge I.hD hu (frz V A n ω) (frz c A n ω)
      have h2 : 0 ≤ fz (frz V A) (frz c A) n ω u + 2 * negMax D (frz V A n ω) (frz c A n ω) := by
        unfold fz; linarith
      have := hβ n
      positivity
  sec := by
    intro n hm0 hn u hu
    have hS := I.survS_meas hA (n := n) hn.le
    obtain ⟨r, hint, hb⟩ := I.fxi_int hn hu
    have hint2 : Integrable (fun ω => fxi V c n ω u ^ 2) μ := by
      refine Integrable.of_bound (hint.aestronglyMeasurable.pow 2) (r ^ 2) ?_
      filter_upwards [hb] with ω h
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have hce : μ[fun ω => fxi (frz V A) (frz c A) n ω u ^ 2 | F n] =ᵐ[μ]
        (survS A n).indicator (μ[fun ω => fxi V c n ω u ^ 2 | F n]) := by
      have e : (fun ω => fxi (frz V A) (frz c A) n ω u ^ 2) =
          (survS A n).indicator (fun ω => fxi V c n ω u ^ 2) := by
        funext ω
        rw [fxi_frz]
        by_cases hω : ω ∈ survS A n
        · simp [hω]
        · simp [hω]
      rw [e]
      exact condExp_indicator hint2 hS
    filter_upwards [hce, I.sec n hm0 hn u hu] with ω h1 h2 hJ
    rw [h1]
    by_cases hω : ω ∈ survS A n
    · rw [Set.indicator_of_mem hω, fz, frz_eq_of_mem V A hω, frz_eq_of_mem c A hω]
      exact h2 (hAJ n ⟨hω, hJ⟩)
    · rw [Set.indicator_of_notMem hω]
      have := hβ n
      positivity

end

end G26


-- ===== Solutions.G26.RunK =====

/-! ### The loss-difference field on `K` satisfies the field interface (Lemma G.10) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26R

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}

/-- the negative maximum of `X(u) = (u − a*)ᵀS` on `K` -/
noncomputable def NK (ℬ : Set (Fin d → ℝ)) (astar S : Fin d → ℝ) : ℝ :=
  negMax (Kset ℬ) S (-(astar ⬝ᵥ S))

lemma fzK (u astar S : Fin d → ℝ) : u ⬝ᵥ S + -(astar ⬝ᵥ S) = (u - astar) ⬝ᵥ S := by
  rw [sub_dotProduct]; ring

section

variable (hd : 1 ≤ d) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ) (hspan : Submodule.span ℝ 𝒜 = ⊤)
include hd hℬ hgen hspan

lemma NK_facts {astar : Fin d → ℝ} (haK : astar ∈ Kset ℬ) (S : Fin d → ℝ) {u : Fin d → ℝ}
    (hu : u ∈ Kset ℬ) :
    0 ≤ NK ℬ astar S ∧ 0 ≤ (u - astar) ⬝ᵥ S + NK ℬ astar S := by
  have hKc := G2R.Kset_compact hℬ
  have h1 := negMax_ge hKc haK S (-(astar ⬝ᵥ S))
  have h2 := negMax_ge hKc hu S (-(astar ⬝ᵥ S))
  rw [fzK] at h1 h2
  simp only [sub_self, zero_dotProduct, neg_zero] at h1
  unfold NK
  constructor <;> linarith

end

end G26R

namespace G26R

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma cumEst_succ (n : ℕ) (ω : Ω) : R.cumEst (n + 1) ω = R.cumEst n ω + R.thetaHat n ω := by
  simp [GRun.cumEst, Finset.sum_range_succ]

end G26R


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

lemma Kc : IsCompact (Kset ℬ) := G2R.Kset_compact H.hℬ

lemma sig_pos : 0 < H.sig := (Classical.choose_spec H.hsharp).1

lemma sig_spec {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) :
    H.sig * sNorm ℬ (a - astar) ≤ gap θ astar a := by
  have h := (Classical.choose_spec H.hsharp).2 a (by rw [G1L.Kset_gen H.hgen]; exact ha)
  rw [G1L.sNorm_gen H.hgen] at h
  exact h

omit H in
lemma sNorm_nonneg (x : Fin d → ℝ) : 0 ≤ sNorm ℬ x := by unfold sNorm; exact gauge_nonneg _

lemma norm_le (x : Fin d → ℝ) : ‖x‖ ≤ sNorm ℬ x := by
  rw [← G1L.sNorm_gen H.hgen]; exact T31.norm_le_sNorm H.ne𝒜 H.hspan H.hball x

end Sharp

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

end Sharp

end G26G


-- ===== Solutions.G26.RefGood =====

/-! ### A measurable sufficient condition for the reference to be `a*` -/

open MeasureTheory ProbabilityTheory Set IAFTRL

namespace G26G

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

lemma js_spec : js ℬ e astar ∈ Jset ℬ e ∧ cand ℬ e (js ℬ e astar) = astar := by
  have h := IAFTRL.lemma_G_12 𝒜 ℬ e H.h𝒜 H.hℬ H.hgen H.hball H.hspan he θ astar H.hastar
    H.huniq H.hsharp
  unfold js; rw [dif_pos h]; exact Classical.choose_spec h

lemma js_mem : js ℬ e astar ∈ Jset ℬ e := (H.js_spec he).1

lemma js_cand : cand ℬ e (js ℬ e astar) = astar := (H.js_spec he).2

lemma hs_pos : 0 < H.hs he := by
  have := G1R.hPen_ge (ℬ := ℬ) (e := e) (js ℬ e astar)
  unfold hs; linarith

lemma D0_nonneg : 0 ≤ H.D0 he :=
  Finset.sum_nonneg fun i _ => inv_nonneg.2 (sNorm_nonneg _)

open Classical in
lemma D0_ge {i : ℕ} (hi : i < js ℬ e astar) (hiJ : i ∈ Jset ℬ e) :
    (sNorm ℬ (cand ℬ e i - astar))⁻¹ ≤ H.D0 he :=
  Finset.single_le_sum (f := fun i => (sNorm ℬ (cand ℬ e i - astar))⁻¹)
    (fun i _ => inv_nonneg.2 (sNorm_nonneg _)) (Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hiJ⟩)

/-- **deterministic reference control**: a far-region lower bound and a near-region bound on the
negative field force strict optimality of `a*` -/
theorem good_of {n : ℕ} {S : Fin d → ℝ} {ε : ℝ} (hε : 0 < ε) (hεD : ε * (H.D0 he + 1) ≤ H.sig)
    (hnear : ∀ a ∈ Kset ℬ, -((a - astar) ⬝ᵥ S) <
      gbeta d n * (Real.exp ((H.sig / ε) ^ 8) - H.hs he))
    (hfar : ∀ a ∈ Kset ℬ, ε ≤ gap θ astar a → gbeta d n * H.hs he < (a - astar) ⬝ᵥ S) :
    goodS ℬ e (js ℬ e astar) n S := by
  intro i hi hij
  have hBne := G2R.B_nonempty H.hd H.hgen H.hspan
  have hbK : cand ℬ e i ∈ Kset ℬ := subset_convexHull ℝ ℬ (G2L.cand_mem H.hℬ hBne e i)
  rw [H.js_cand he]
  have hbne : cand ℬ e i ≠ astar := by
    rw [← H.js_cand he]
    rcases lt_or_gt_of_ne hij with h | h
    · exact (H.js_mem he) i h
    · exact (hi (js ℬ e astar) h).symm
  set b := cand ℬ e i
  have hsplit : (b - astar) ⬝ᵥ S = b ⬝ᵥ S - astar ⬝ᵥ S := sub_dotProduct _ _ _
  have hβ := G2R.gbeta_pos H.hd n
  have hhi0 : 0 ≤ hPen ℬ e i := by have := G1R.hPen_ge (ℬ := ℬ) (e := e) i; linarith
  by_cases hΔ : ε ≤ gap θ astar b
  · have h1 := hfar b hbK hΔ
    have h2 : 0 ≤ gbeta d n * hPen ℬ e i := mul_nonneg hβ.le hhi0
    have : H.hs he = hPen ℬ e (js ℬ e astar) := rfl
    rw [← this]
    linarith
  · push Not at hΔ
    set δ := sNorm ℬ (b - astar)
    have hδ0 : 0 < δ := by
      have h1 : 0 < ‖b - astar‖ := norm_pos_iff.2 (sub_ne_zero.2 hbne)
      exact lt_of_lt_of_le h1 (H.norm_le _)
    have hδε : H.sig * δ < ε := lt_of_le_of_lt (H.sig_spec hbK) hΔ
    have hsig := H.sig_pos
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · -- an early atom is far
      exfalso
      have h1 := H.D0_ge he hlt hi
      have h2 : 1 ≤ H.D0 he * δ := by
        calc (1 : ℝ) = δ⁻¹ * δ := (inv_mul_cancel₀ hδ0.ne').symm
          _ ≤ H.D0 he * δ := mul_le_mul_of_nonneg_right h1 hδ0.le
      have h3 : H.sig ≤ H.sig * (H.D0 he * δ) := le_mul_of_one_le_right hsig.le h2
      have h4 : ε * (H.D0 he + 1) > H.sig := by
        have : H.sig * (H.D0 he * δ) = (H.sig * δ) * H.D0 he := by ring
        have h5 : (H.sig * δ) * H.D0 he ≤ ε * H.D0 he :=
          mul_le_mul_of_nonneg_right hδε.le (H.D0_nonneg he)
        nlinarith
      linarith
    · -- a late atom carries a large priority
      have hfar' := G1R.hPen_far (H.js_mem he) hgt
      rw [H.js_cand he] at hfar'
      have hd1 : H.sig / ε < δ⁻¹ := by
        rw [div_lt_iff₀ hε, lt_inv_mul_iff₀ hδ0]; linarith
      have hexp : Real.exp ((H.sig / ε) ^ 8) < Real.exp (δ⁻¹ ^ 8) :=
        Real.exp_lt_exp.2 (pow_lt_pow_left₀ hd1 (by positivity) (by norm_num))
      have hpos : (0 : ℝ) ≤ (i : ℝ) + 2 := by positivity
      have h1 := hnear b hbK
      have h2 : gbeta d n * (Real.exp ((H.sig / ε) ^ 8) - H.hs he) ≤
          gbeta d n * (hPen ℬ e i - H.hs he) := by
        apply mul_le_mul_of_nonneg_left _ hβ.le
        linarith
      have : H.hs he = hPen ℬ e (js ℬ e astar) := rfl
      rw [← this]
      have e1 : gbeta d n * (hPen ℬ e i - H.hs he) = gbeta d n * hPen ℬ e i - gbeta d n * H.hs he := by
        ring
      linarith

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

lemma gbeta_ge16 (n : ℕ) : 16 ≤ gbeta d (n + 1) := by
  unfold gbeta; have : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have := Real.sqrt_nonneg ((n + 1 : ℕ) : ℝ); linarith

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


-- ===== Solutions.G26.RunEnv =====

/-! ### Envelopes of the run fields: absolute maxima and block crossings (Lemmas G.15, G.30) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26

variable {d : ℕ} {Ω : Type*}

lemma rdim_le (D : Set (Fin d → ℝ)) : rdim D ≤ d := by
  unfold rdim
  have := Submodule.finrank_le (vectorSpan ℝ D)
  simpa using this

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma FI.absMax_int [IsProbabilityMeasure μ] (I : FI D μ F T V c J β B lo hi m0) {n : ℕ}
    (hn : n ≤ T) (P : ℕ) : Integrable (fun ω => absMax D (V n ω) (c n ω) ^ P) μ := by
  obtain ⟨r, hr0, hr⟩ := I.env' hn
  refine Integrable.of_bound
    (((I.absMax_meas hn).mono (I.Fle n hn) le_rfl).pow_const P).aestronglyMeasurable (r ^ P) ?_
  filter_upwards [hr, I.N0 n hn] with ω h h0
  have h1 : 0 ≤ absMax D (V n ω) (c n ω) := h0.trans (negMax_le_absMax _ _)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h1 _)]
  exact pow_le_pow_left₀ h1 h.1 P

end G26

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma kk_facts (d : ℕ) : 2 ≤ kk d ∧ 4 ≤ 4 * kk d ∧ Even (4 * kk d) ∧ d ≤ 4 * kk d ∧
    2 ^ 20 * ((4 * kk d : ℕ) : ℝ) ≤ gB d := by
  unfold kk gB
  refine ⟨by omega, by omega, ⟨2 * (1024 * (d + 1)), by ring⟩, by omega, ?_⟩
  push_cast; nlinarith

lemma gbeta_le (d n : ℕ) : gbeta d (n + 1) ≤ (16 * d + 1) * ((n : ℝ) + 1) := by
  unfold gbeta
  have h1 : Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]; push_cast; nlinarith
  have h2 : (16 * d : ℝ) ≤ 16 * d * ((n : ℝ) + 1) := by
    have : (0 : ℝ) ≤ 16 * d := by positivity
    nlinarith
  nlinarith

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

/-- **the absolute envelope of the jointly frozen loss-difference field (G.288)** -/
theorem absK_env (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {A : ℕ → Set Ω}
    (hA : ∀ n ≤ T, MeasurableSet[Fx R T n] (A n)) {n : ℕ} (hn : n ≤ T) :
    ∫ ω, absMax (Kset ℬ) (frz R.cumEst A n ω)
      (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A n ω) ^ (4 * kk d) ∂P ≤
      cK d * ((n : ℝ) + 1) ^ (4 * kk d) := by
  obtain ⟨hk2, hP4, hev, hdP, hB⟩ := kk_facts d
  have I0 := runK_FI H.hd H.h𝒜 H.hℬ H.hgen H.hspan hR H.haK
  have I := I0.freeze hA (by norm_num) (by norm_num) (fun n => (G2R.gbeta_pos H.hd (n + 1)).le)
    G2R.gB_pos (J' := fun _ => univ) (fun _ _ => MeasurableSet.univ) (fun _ => subset_rfl)
    (fun _ => subset_univ _)
  have h0 : ∀ ω, Gf (Kset ℬ) (frz R.cumEst A) (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A)
      (4 * kk d) 0 ω = 0 := by
    intro ω
    unfold Gf fz
    simp only [frz, GRun.cumEst, Finset.range_zero, Finset.sum_empty, dotProduct_zero, neg_zero,
      add_zero]
    rw [zero_pow (by omega)]; simp
  have h := I.absMax_env (by norm_num) le_rfl hP4 hev ((rdim_le _).trans hdP) hB
    (fun n => G2R.gbeta_pos H.hd (n + 1)) (fun n => gbeta_le d n) h0 hn
  simp only [Set.indicator_univ] at h
  refine h.trans ?_
  unfold cK
  have h4 : (4 : ℝ) ^ rdim (Kset ℬ) ≤ 4 ^ d := pow_le_pow_right₀ (by norm_num) (rdim_le _)
  have hC : 0 ≤ Cabs (4 * kk d) (16 * d + 1) (gB d) 0 := by unfold Cabs; positivity
  gcongr

end Sharp

end G26G


-- ===== Solutions.G26.Params =====

/-! ### Thresholds: buffers `τ_s = (s+1)^{7/8} + 4z` and logarithmic gap cutoffs -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26G

open G26 G26R

lemma p78_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : x ^ ((7 : ℝ) / 8) ≤ y ^ ((7 : ℝ) / 8) :=
  Real.rpow_le_rpow hx hxy (by norm_num)

lemma p78_ge_one {x : ℝ} (hx : 1 ≤ x) : 1 ≤ x ^ ((7 : ℝ) / 8) :=
  Real.one_le_rpow hx (by norm_num)

lemma tauB_mono {z : ℝ} (s : ℕ) : tauB z s ≤ tauB z (s + 1) := by
  unfold tauB
  have := p78_mono (x := (s : ℝ) + 1) (y := ((s + 1 : ℕ) : ℝ) + 1) (by positivity) (by push_cast; linarith)
  linarith

lemma tauB_delta (z : ℝ) (s : ℕ) : tauB z (s + 1) - tauB z s ≤ 1 := by
  unfold tauB
  have h := Real.rpow_add_le_add_rpow (p := (7 : ℝ) / 8) (a := (s : ℝ) + 1) (b := 1)
    (by positivity) zero_le_one (by norm_num) (by norm_num)
  rw [Real.one_rpow] at h
  have e : ((s + 1 : ℕ) : ℝ) + 1 = (s : ℝ) + 1 + 1 := by push_cast; ring
  rw [e]; linarith

lemma tauB_ge {z : ℝ} (hz : 0 ≤ z) (s : ℕ) :
    ((s : ℝ) + 1) ^ ((7 : ℝ) / 8) ≤ tauB z s ∧ 4 * z ≤ tauB z s ∧ 1 ≤ tauB z s := by
  unfold tauB
  have h1 := p78_ge_one (x := (s : ℝ) + 1) (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])
  refine ⟨by linarith, ?_, by linarith⟩
  have : 0 ≤ ((s : ℝ) + 1) ^ ((7 : ℝ) / 8) := by positivity
  linarith

lemma tauB_pos {z : ℝ} (hz : 0 ≤ z) (s : ℕ) : 0 < tauB z s := by
  linarith [(tauB_ge hz s).2.2]

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

lemma sqrt_eq_root8 {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x = root8 x ^ 4 := by
  rw [root8_eq_rpow hx, ← Real.rpow_natCast, ← Real.rpow_mul hx, Real.sqrt_eq_rpow]; norm_num

lemma one_le_root8 {x : ℝ} (hx : 1 ≤ x) : 1 ≤ root8 x :=
  le_root8 zero_le_one (by simpa using hx)

end G26G


-- ===== Solutions.G26.RefBlock =====

/-! ### Uniform reference control on a block (Lemma G.29) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

/-- the absolute maximum of the loss-difference field on `K` -/
noncomputable def RX (ℬ : Set (Fin d → ℝ)) (astar : Fin d → ℝ) (S : Fin d → ℝ) : ℝ :=
  absMax (Kset ℬ) S (-(astar ⬝ᵥ S))

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

/-- the logarithmic level of the gap cutoff at run index `s` -/
noncomputable def Lf (s : ℕ) : ℝ := 4 * Real.log (Real.exp 1 * ((s : ℝ) + 2)) + (H.D0 he + 1) ^ 8

/-- the gap cutoff `ε_s = ς / L_s^{1/8}` -/
noncomputable def εf (s : ℕ) : ℝ := H.sig / root8 (H.Lf he s)

lemma Lf_facts (s : ℕ) : (H.D0 he + 1) ^ 8 ≤ H.Lf he s ∧ 1 ≤ H.Lf he s ∧
    ((s : ℝ) + 2) ^ 4 ≤ Real.exp (H.Lf he s) := by
  have hD := H.D0_nonneg he
  have hlog : 1 ≤ Real.log (Real.exp 1 * ((s : ℝ) + 2)) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
    have : 0 ≤ Real.log ((s : ℝ) + 2) := Real.log_nonneg (by linarith [(Nat.cast_nonneg s : (0:ℝ) ≤ s)])
    linarith
  have h1 : 1 ≤ (H.D0 he + 1) ^ 8 := one_le_pow₀ (by linarith)
  unfold Lf
  refine ⟨by linarith, by linarith, ?_⟩
  have h2 : Real.exp (4 * Real.log (Real.exp 1 * ((s : ℝ) + 2))) =
      (Real.exp 1 * ((s : ℝ) + 2)) ^ 4 := by
    rw [mul_comm, Real.exp_mul, Real.exp_log (by positivity)]; norm_cast
  have h3 : Real.exp (4 * Real.log (Real.exp 1 * ((s : ℝ) + 2))) ≤
      Real.exp (4 * Real.log (Real.exp 1 * ((s : ℝ) + 2)) + (H.D0 he + 1) ^ 8) :=
    Real.exp_le_exp.2 (by linarith)
  have h4 : ((s : ℝ) + 2) ^ 4 ≤ (Real.exp 1 * ((s : ℝ) + 2)) ^ 4 := by
    have : (s : ℝ) + 2 ≤ Real.exp 1 * ((s : ℝ) + 2) := by
      have := Real.add_one_le_exp (1 : ℝ)
      nlinarith [(Nat.cast_nonneg s : (0:ℝ) ≤ s)]
    exact pow_le_pow_left₀ (by positivity) this 4
  linarith

lemma Lf_mono {s t : ℕ} (h : s ≤ t) : H.Lf he s ≤ H.Lf he t := by
  unfold Lf
  have : Real.log (Real.exp 1 * ((s : ℝ) + 2)) ≤ Real.log (Real.exp 1 * ((t : ℝ) + 2)) :=
    Real.log_le_log (by positivity) (by
      have : (s : ℝ) ≤ t := by exact_mod_cast h
      nlinarith [Real.exp_pos 1])
  linarith

lemma root8_Lf_pos (s : ℕ) : 0 < root8 (H.Lf he s) := by
  have h := (H.Lf_facts he s).2.1
  have := le_root8 zero_le_one (by norm_num; exact h : (1 : ℝ) ^ 8 ≤ H.Lf he s)
  linarith

lemma εf_pos (s : ℕ) : 0 < H.εf he s := div_pos H.sig_pos (H.root8_Lf_pos he s)

lemma εf_D0 (s : ℕ) : H.εf he s * (H.D0 he + 1) ≤ H.sig := by
  have hr := H.root8_Lf_pos he s
  have h1 : H.D0 he + 1 ≤ root8 (H.Lf he s) :=
    le_root8 (by linarith [H.D0_nonneg he]) (H.Lf_facts he s).1
  unfold εf
  rw [div_mul_eq_mul_div, div_le_iff₀ hr]
  exact mul_le_mul_of_nonneg_left h1 H.sig_pos.le

lemma εf_pow (s : ℕ) : (H.sig / H.εf he s) ^ 8 = H.Lf he s := by
  have hr := H.root8_Lf_pos he s
  unfold εf
  rw [div_div_cancel₀ H.sig_pos.ne', root8_pow (by linarith [(H.Lf_facts he s).2.1])]

lemma εf_anti {s t : ℕ} (h : s ≤ t) : H.εf he t ≤ H.εf he s := by
  unfold εf
  exact div_le_div_of_nonneg_left H.sig_pos.le (H.root8_Lf_pos he s)
    (root8_mono (H.Lf_mono he h))

/-- **deterministic reference control at run index `s`**: a failure of strict reference optimality
forces a large absolute maximum or a small value in the far region -/
theorem not_good {s : ℕ} (hs : 2 * H.hs he ≤ ((s : ℝ) + 2) ^ 4) {S : Fin d → ℝ}
    (hng : ¬ goodS ℬ e (js ℬ e astar) (s + 1) S) :
    ((s : ℝ) + 2) ^ 4 / 2 ≤ RX ℬ astar S ∨
      ∃ a ∈ Dfar ℬ θ astar (H.εf he s), (a - astar) ⬝ᵥ S ≤ gbeta d (s + 1) * H.hs he := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hR, hF⟩ := hcon
  apply hng
  have hβ1 : 1 ≤ gbeta d (s + 1) := by linarith [H.gbeta_ge16 s]
  refine H.good_of he (H.εf_pos he s) (H.εf_D0 he s) ?_ ?_
  · intro a ha
    have h1 : |(a - astar) ⬝ᵥ S| ≤ RX ℬ astar S := by
      have := abs_le_absMax H.Kc ha S (-(astar ⬝ᵥ S))
      rwa [fzK] at this
    rw [H.εf_pow he s]
    have h2 := (H.Lf_facts he s).2.2
    have h3 : ((s : ℝ) + 2) ^ 4 / 2 ≤ Real.exp (H.Lf he s) - H.hs he := by linarith
    have h4 : 0 ≤ Real.exp (H.Lf he s) - H.hs he := by
      have := H.hs_pos he; linarith
    have h5 : Real.exp (H.Lf he s) - H.hs he ≤ gbeta d (s + 1) * (Real.exp (H.Lf he s) - H.hs he) :=
      le_mul_of_one_le_left h4 hβ1
    linarith [neg_abs_le ((a - astar) ⬝ᵥ S)]
  · intro a ha hε
    exact hF a ⟨ha, hε⟩

/-- **near failures are controlled by the absolute envelope (G.651)** -/
theorem near_prob (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {s : ℕ} (hs : s ≤ T) {lam : ℝ}
    (hlam : 0 < lam) :
    P.real {ω | lam ≤ RX ℬ astar (R.cumEst s ω)} ≤ cK d * ((s : ℝ) + 1) ^ (4 * kk d) / lam ^ (4 * kk d) := by
  have hA : ∀ n ≤ T, MeasurableSet[Fx R T n] ((fun _ => (univ : Set Ω)) n) :=
    fun _ _ => MeasurableSet.univ
  have h := H.absK_env hR hA hs
  simp only [frz_univ] at h
  have I0 := runK_FI H.hd H.h𝒜 H.hℬ H.hgen H.hspan hR H.haK
  have hint := I0.absMax_int hs (4 * kk d)
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (Filter.Eventually.of_forall fun ω => by
      have := (NK_facts H.hd H.hℬ H.hgen H.hspan H.haK (R.cumEst s ω) H.haK).1
      exact pow_nonneg (this.trans (negMax_le_absMax _ _)) _) hint (lam ^ (4 * kk d))
  have hsub : {ω | lam ≤ RX ℬ astar (R.cumEst s ω)} ⊆
      {ω | lam ^ (4 * kk d) ≤ absMax (Kset ℬ) (R.cumEst s ω) (-(astar ⬝ᵥ R.cumEst s ω)) ^ (4 * kk d)} :=
    fun ω hω => pow_le_pow_left₀ hlam.le hω _
  have hpos : 0 < lam ^ (4 * kk d) := by positivity
  rw [le_div_iff₀ hpos]
  calc P.real {ω | lam ≤ RX ℬ astar (R.cumEst s ω)} * lam ^ (4 * kk d)
      ≤ P.real {ω | lam ^ (4 * kk d) ≤ absMax (Kset ℬ) (R.cumEst s ω)
          (-(astar ⬝ᵥ R.cumEst s ω)) ^ (4 * kk d)} * lam ^ (4 * kk d) :=
        mul_le_mul_of_nonneg_right (measureReal_mono hsub) hpos.le
    _ ≤ _ := by linarith

end Sharp

end G26G


-- ===== Solutions.G26.RefAlg =====

/-! ### Real-variable estimates for the reference block bound -/

open IAFTRL

namespace G26G

/-- `root8 (2y) ≤ 2 root8 y` -/
lemma root8_two_mul {y : ℝ} (hy : 0 ≤ y) : root8 (2 * y) ≤ 2 * root8 y := by
  have h1 := root8_pow hy
  have h2 : (2 * root8 y) ^ 8 = 256 * y := by rw [mul_pow, h1]; norm_num
  by_contra h
  push Not at h
  have h3 := pow_lt_pow_left₀ h (by have := root8_nonneg y; positivity) (by norm_num : (8 : ℕ) ≠ 0)
  rw [root8_pow (by linarith), h2] at h3
  linarith

lemma gbeta_cast (d n : ℕ) : gbeta d (n + 1) = 16 * (d : ℝ) + Real.sqrt ((n : ℝ) + 1) := by
  unfold gbeta; push_cast; ring

lemma tauB_ge_r7 {z : ℝ} (hz : 0 ≤ z) (n : ℕ) : root8 ((n : ℝ) + 1) ^ 7 ≤ tauB z n := by
  rw [← rpow78_eq (by positivity)]; exact (tauB_ge hz n).1

lemma thr_tauB {d n : ℕ} {z : ℝ} (hz : 0 ≤ z) (hn : (gB d * (16 * d + 4)) ^ 8 ≤ (n : ℝ) + 1) :
    gB d * (gbeta d (n + 1) + 3) ≤ tauB z n := by
  have hB := G2R.gB_pos (d := d)
  set ry := root8 ((n : ℝ) + 1)
  have hry : gB d * (16 * d + 4) ≤ ry := le_root8 (by positivity) hn
  have hr1 : 1 ≤ ry := one_le_root8 (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
  have hsq : Real.sqrt ((n : ℝ) + 1) = ry ^ 4 := sqrt_eq_root8 (by positivity)
  rw [gbeta_cast, hsq]
  refine le_trans ?_ (tauB_ge_r7 hz n)
  have h4 : 1 ≤ ry ^ 4 := one_le_pow₀ hr1
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : 16 * (d : ℝ) + ry ^ 4 + 3 ≤ (16 * d + 4) * ry ^ 4 := by nlinarith
  have h3 : ry ≤ ry ^ 3 := by nlinarith [one_le_pow₀ (n := 2) hr1]
  calc gB d * (16 * d + ry ^ 4 + 3) ≤ gB d * ((16 * d + 4) * ry ^ 4) :=
        mul_le_mul_of_nonneg_left h1 hB.le
    _ = (gB d * (16 * d + 4)) * ry ^ 4 := by ring
    _ ≤ ry ^ 3 * ry ^ 4 := mul_le_mul_of_nonneg_right (hry.trans h3) (by positivity)
    _ = ry ^ 7 := by ring

lemma thr_tm {m0 : ℕ} {z c : ℝ} (hz : 0 ≤ z) (hc : 0 ≤ c) (h : c ^ 8 ≤ (m0 : ℝ) + 1) :
    c ≤ tauB z m0 := by
  have hr := le_root8 hc h
  have hr1 : 1 ≤ root8 ((m0 : ℝ) + 1) := one_le_root8 (by linarith [(Nat.cast_nonneg m0 : (0:ℝ) ≤ m0)])
  have : root8 ((m0 : ℝ) + 1) ≤ root8 ((m0 : ℝ) + 1) ^ 7 := by
    calc root8 ((m0 : ℝ) + 1) = root8 ((m0 : ℝ) + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hr1 (by norm_num)
  linarith [tauB_ge_r7 hz m0]

lemma thr_tb {d P m0 u n : ℕ} {z : ℝ} (hz : 0 ≤ z) (hn : n < 2 * u)
    (hu : (u : ℝ) + 1 ≤ 4 * ((m0 : ℝ) + 1))
    (h : (960 * ((P : ℝ) + 1) * (16 * d + 1)) ^ 8 ≤ (m0 : ℝ) + 1) :
    40 * ((P : ℝ) + 1) * gbeta d (n + 1) * ((n : ℝ) + 1) ≤ tauB z m0 ^ 2 := by
  set r := root8 ((m0 : ℝ) + 1)
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hP : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  have hr := le_root8 (by positivity) h
  have hr1 : 1 ≤ r := one_le_root8 (by linarith [(Nat.cast_nonneg m0 : (0:ℝ) ≤ m0)])
  have hr8 : r ^ 8 = (m0 : ℝ) + 1 := root8_pow (by positivity)
  have hn1 : (n : ℝ) + 1 ≤ 8 * r ^ 8 := by
    have : (n : ℝ) + 1 ≤ 2 * u := by exact_mod_cast hn
    rw [hr8]; linarith
  have hsq : Real.sqrt ((n : ℝ) + 1) ≤ 3 * r ^ 4 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [pow_nonneg (show (0:ℝ) ≤ r by linarith) 8]
  have hs1 : 1 ≤ Real.sqrt ((n : ℝ) + 1) := by
    rw [Real.one_le_sqrt]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hgb : gbeta d (n + 1) ≤ (16 * d + 1) * (3 * r ^ 4) := by
    rw [gbeta_cast]; nlinarith
  have ht := tauB_ge_r7 hz m0
  have ht2 : r ^ 14 ≤ tauB z m0 ^ 2 := by
    rw [show r ^ 14 = (r ^ 7) ^ 2 by ring]
    exact pow_le_pow_left₀ (by positivity) ht 2
  have hr2 : 960 * ((P : ℝ) + 1) * (16 * d + 1) ≤ r ^ 2 := by nlinarith
  calc 40 * ((P : ℝ) + 1) * gbeta d (n + 1) * ((n : ℝ) + 1)
      ≤ 40 * ((P : ℝ) + 1) * ((16 * d + 1) * (3 * r ^ 4)) * (8 * r ^ 8) := by
        gcongr
    _ = 960 * ((P : ℝ) + 1) * (16 * d + 1) * r ^ 12 := by ring
    _ ≤ r ^ 2 * r ^ 12 := mul_le_mul_of_nonneg_right hr2 (by positivity)
    _ = r ^ 14 := by ring
    _ ≤ _ := ht2

lemma thr_hb {d u : ℕ} {hs : ℝ} (hhs : 0 ≤ hs) (h : ((16 * d + 1) * hs) ^ 8 ≤ (2 * (u : ℝ) + 1)) :
    gbeta d (2 * u + 1) * hs ≤ ((((2 * u : ℕ) : ℝ) + 1) ^ ((7 : ℝ) / 8)) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hy : ((2 * u : ℕ) : ℝ) + 1 = 2 * (u : ℝ) + 1 := by push_cast; ring
  rw [hy, rpow78_eq (by positivity)]
  set ry := root8 (2 * (u : ℝ) + 1)
  have hry := le_root8 (by positivity) h
  have hr1 : 1 ≤ ry := one_le_root8 (by linarith [(Nat.cast_nonneg u : (0:ℝ) ≤ u)])
  have hsq : Real.sqrt (2 * (u : ℝ) + 1) = ry ^ 4 := sqrt_eq_root8 (by positivity)
  have hg : gbeta d (2 * u + 1) = 16 * d + ry ^ 4 := by
    unfold gbeta; rw [← hsq]; push_cast; ring_nf
  rw [hg]
  have h4 : 1 ≤ ry ^ 4 := one_le_pow₀ hr1
  calc (16 * (d : ℝ) + ry ^ 4) * hs ≤ ((16 * d + 1) * ry ^ 4) * hs :=
        mul_le_mul_of_nonneg_right (by nlinarith) hhs
    _ = ((16 * d + 1) * hs) * ry ^ 4 := by ring
    _ ≤ ry * ry ^ 4 := mul_le_mul_of_nonneg_right hry (by positivity)
    _ = ry ^ 5 := by ring
    _ ≤ ry ^ 7 := pow_le_pow_right₀ hr1 (by norm_num)

lemma thr_tau2u {u nC : ℕ} (hu : (2 : ℝ) ^ 80 ≤ (u : ℝ) + 1) (hnC : 1024 * (nC : ℝ) ≤ (u : ℝ) + 1) :
    tauB (Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1))) (2 * u) ≤ ((u : ℝ) + 1) / 4 := by
  unfold tauB
  have hy : ((2 * u : ℕ) : ℝ) + 1 ≤ 2 * ((u : ℝ) + 1) := by push_cast; linarith
  set ry := root8 ((u : ℝ) + 1)
  have hry8 : ry ^ 8 = (u : ℝ) + 1 := root8_pow (by positivity)
  have hry : (1024 : ℝ) ≤ ry := le_root8 (by norm_num) (by norm_num; linarith)
  have h1 : (((2 * u : ℕ) : ℝ) + 1) ^ ((7 : ℝ) / 8) ≤ (2 * ry) ^ 7 := by
    rw [rpow78_eq (by positivity)]
    exact pow_le_pow_left₀ (root8_nonneg _)
      ((root8_mono hy).trans (root8_two_mul (by positivity))) 7
  have h2 : (2 * ry) ^ 7 ≤ ((u : ℝ) + 1) / 8 := by
    rw [← hry8]; nlinarith [pow_pos (show (0:ℝ) < ry by linarith) 7]
  have h3 : 4 * Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1)) ≤ ((u : ℝ) + 1) / 8 := by
    have : Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1)) ≤ ((u : ℝ) + 1) / 32 := by
      rw [Real.sqrt_le_left (by positivity)]
      have : (0 : ℝ) ≤ (u : ℝ) + 1 := by positivity
      nlinarith
    linarith
  linarith

/-- `(log y)^q ≤ q! y` for `y ≥ 1` -/
lemma log_pow_le {y : ℝ} (hy : 1 ≤ y) (q : ℕ) : Real.log y ^ q ≤ (q.factorial : ℝ) * y := by
  have h0 : 0 ≤ Real.log y := Real.log_nonneg hy
  have := Real.pow_div_factorial_le_exp (x := Real.log y) h0 q
  rw [Real.exp_log (by linarith), div_le_iff₀ (by positivity)] at this
  linarith

/-- `log(e(2u+2)) ≤ 3 (u+1)/(nC+1)` once `(nC+1) log(e(nC+1)) ≤ u+1` -/
lemma log_le_R {u nC : ℕ} (h : ((nC : ℝ) + 1) * Real.log (Real.exp 1 * ((nC : ℝ) + 1)) ≤ (u : ℝ) + 1)
    (hnu : nC ≤ u) :
    Real.log (Real.exp 1 * (((2 * u : ℕ) : ℝ) + 2)) ≤ 3 * (((u : ℝ) + 1) / ((nC : ℝ) + 1)) := by
  have hn1 : (0 : ℝ) < (nC : ℝ) + 1 := by positivity
  set Rr := ((u : ℝ) + 1) / ((nC : ℝ) + 1)
  have hR1 : 1 ≤ Rr := by
    rw [le_div_iff₀ hn1]; have : (nC : ℝ) ≤ u := by exact_mod_cast hnu
    linarith
  have hl : Real.log (Real.exp 1 * ((nC : ℝ) + 1)) ≤ Rr := by
    rw [le_div_iff₀ hn1]; linarith
  have e1 : Real.exp 1 * (((2 * u : ℕ) : ℝ) + 2) = (Real.exp 1 * ((nC : ℝ) + 1)) * (2 * Rr) := by
    simp only [Rr]; push_cast; field_simp
  rw [e1, Real.log_mul (by positivity) (by positivity)]
  have h2 := Real.log_le_sub_one_of_pos (show 0 < 2 * Rr by positivity)
  linarith

end G26G


-- ===== Solutions.G26.RefAlg3 =====

/-! ### The reference block bound (Lemma G.29): algebra -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma gbeta_mono (d : ℕ) {s t : ℕ} (h : s ≤ t) : gbeta d s ≤ gbeta d t := by
  unfold gbeta
  have : Real.sqrt (s : ℝ) ≤ Real.sqrt (t : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast h)
  linarith

end G26G


-- ===== Solutions.G26.RefClean =====

/-! ### The reference block bound (Lemma G.29): probabilistic decomposition -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

/-- **raw reference-block decomposition**: near failures, preparation crossings, far successes -/
theorem ref_block_raw (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ} (hC : 0 ≤ C)
    (hcor : IsCorruptedG P 𝒜 θ C T R)
    {τ : ℕ → ℝ} (hτpos : ∀ n, 0 < τ n) (hτmono : ∀ n, τ n ≤ τ (n + 1))
    (hδ : ∀ n, τ (n + 1) - τ n ≤ 1) {m0 u nC : ℕ} (h2uT : 2 * u ≤ T) (hm0u : m0 ≤ u)
    (hnCu : nC ≤ 2 * u)
    (hhalf : 2 * ((m0 : ℝ) + 1) ≤ (u : ℝ) + 1)
    (hmP : ((4 * kk d : ℕ) : ℝ) + 1 ≤ 2 * ((m0 : ℝ) + 1))
    (hτB : ∀ n, m0 ≤ n → gB d * (gbeta d (n + 1) + 3) ≤ τ n)
    (hτm : 2 * (((4 * kk d : ℕ) : ℝ) + 1) ≤ τ m0)
    (hτβ : ∀ n, m0 ≤ n → n < 2 * u →
      40 * (((4 * kk d : ℕ) : ℝ) + 1) * gbeta d (n + 1) * ((n : ℝ) + 1) ≤ τ m0 ^ 2)
    (hhs : 2 * H.hs he ≤ ((u : ℝ) + 2) ^ 4)
    (hbC : gbeta d (2 * u + 1) * H.hs he + 4 * C ≤ 2 * τ (2 * u))
    {ρ1 : ℝ} (hρ1τ : τ m0 ≤ ρ1) (hρ1C : 4 * C ≤ ρ1)
    {ρ2 : ℝ} (hρa : 4 * τ (2 * u) ≤ ρ2) (hρb : 2 * (4 * C + 2 * τ (2 * u)) ≤ ρ2) :
    P.real {ω | ∃ s, u ≤ s ∧ s ≤ 2 * u ∧ ¬ goodS ℬ e (js ℬ e astar) (s + 1) (R.cumEst s ω)} ≤
      ∑ s ∈ Finset.Icc u (2 * u), cK d * ((s : ℝ) + 1) ^ (4 * kk d) /
          (((s : ℝ) + 2) ^ 4 / 2) ^ (4 * kk d) +
      (2 ^ (4 * kk d) * cK d * (((2 * u : ℕ) : ℝ) + 1) ^ (4 * kk d) / ρ1 ^ (4 * kk d) +
        2 ^ (4 * kk d) * 4 ^ d * (ρ1 / τ m0) ^ d / τ m0 ^ (4 * kk d) *
          (Hneg (kk d) (16 * d + 1) (gB d) * (((2 * u : ℕ) : ℝ) + 1) ^ (3 * kk d) +
            ((((2 * u : ℕ) : ℝ) + 1) / ((nC : ℝ) + 1)) ^ (d + 2) *
              (2 ^ (4 * kk d) * (cK d * ((nC : ℝ) + 1) ^ (4 * kk d) + (2 * C) ^ (4 * kk d))))) +
      2 ^ (4 * kk d) * cK d * (((2 * u : ℕ) : ℝ) + 1) ^ (4 * kk d) / ρ2 ^ (4 * kk d) +
      (2 * (4 * τ (2 * u))) ^ (4 * kk d) * (ρ2 / (4 * τ (2 * u))) ^ d *
        (2 ^ (4 * kk d) * (4 / (((u : ℝ) + 1) * H.εf he (2 * u))) ^ (4 * kk d)) := by
  set ε := H.εf he (2 * u)
  set hbv := gbeta d (2 * u + 1) * H.hs he
  -- the inclusion
  have hsub : {ω | ∃ s, u ≤ s ∧ s ≤ 2 * u ∧ ¬ goodS ℬ e (js ℬ e astar) (s + 1) (R.cumEst s ω)} ⊆
      (⋃ s ∈ Finset.Icc u (2 * u), {ω | ((s : ℝ) + 2) ^ 4 / 2 ≤ RX ℬ astar (R.cumEst s ω)}) ∪
      {ω | ∃ s, u ≤ s ∧ s ≤ 2 * u ∧ ∃ a ∈ Dfar ℬ θ astar ε,
        (a - astar) ⬝ᵥ R.cumEst s ω ≤ hbv} := by
    rintro ω ⟨s, hus, hs2, hng⟩
    have hs4 : 2 * H.hs he ≤ ((s : ℝ) + 2) ^ 4 := by
      refine hhs.trans (pow_le_pow_left₀ (by positivity) ?_ 4)
      have : (u : ℝ) ≤ s := by exact_mod_cast hus
      linarith
    rcases H.not_good he hs4 hng with h | ⟨a, ha, hX⟩
    · left
      exact Set.mem_biUnion (Finset.mem_Icc.2 ⟨hus, hs2⟩) h
    · right
      refine ⟨s, hus, hs2, a, ⟨ha.1, le_trans (H.εf_anti he hs2) ha.2⟩, hX.trans ?_⟩
      exact mul_le_mul_of_nonneg_right (gbeta_mono d (by omega)) (H.hs_pos he).le
  have hnear : P.real (⋃ s ∈ Finset.Icc u (2 * u),
      {ω | ((s : ℝ) + 2) ^ 4 / 2 ≤ RX ℬ astar (R.cumEst s ω)}) ≤
      ∑ s ∈ Finset.Icc u (2 * u), cK d * ((s : ℝ) + 1) ^ (4 * kk d) /
          (((s : ℝ) + 2) ^ 4 / 2) ^ (4 * kk d) := by
    refine (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun s hs => ?_)
    have hsT : s ≤ T := (Finset.mem_Icc.1 hs).2.trans h2uT
    exact H.near_prob he hR hsT (by positivity)
  have hfar := H.far_prob hR hC hcor hτpos hτmono hδ h2uT hm0u hhalf hmP hτB hτm hτβ
    (H.εf_pos he (2 * u)) hbC hρa hρb
  have hprep := H.prep_prob he hR hC hcor hτmono (N := 2 * u) h2uT hnCu
    (by have : (0 : ℝ) ≤ ((4 * kk d : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith) hρ1τ hρ1C
  calc _ ≤ P.real ((⋃ s ∈ Finset.Icc u (2 * u),
        {ω | ((s : ℝ) + 2) ^ 4 / 2 ≤ RX ℬ astar (R.cumEst s ω)}) ∪
      {ω | ∃ s, u ≤ s ∧ s ≤ 2 * u ∧ ∃ a ∈ Dfar ℬ θ astar ε,
        (a - astar) ⬝ᵥ R.cumEst s ω ≤ hbv}) := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := by linarith

lemma Lf_bounds {u nC : ℕ} (hnu : nC ≤ u)
    (hlogR : ((nC : ℝ) + 1) * Real.log (Real.exp 1 * ((nC : ℝ) + 1)) ≤ (u : ℝ) + 1) :
    H.Lf he (2 * u) ^ (512 * (d + 1)) ≤
      ((4 + (H.D0 he + 1) ^ 8) ^ (512 * (d + 1)) * ((512 * (d + 1)).factorial : ℝ) * 6) *
        ((u : ℝ) + 1) ∧
    H.Lf he (2 * u) ≤ (12 + (H.D0 he + 1) ^ 8) * (((u : ℝ) + 1) / ((nC : ℝ) + 1)) := by
  generalize 512 * (d + 1) = q
  have hc0 : 0 ≤ (H.D0 he + 1) ^ 8 := by have := H.D0_nonneg he; positivity
  have hLdef : H.Lf he (2 * u) = 4 * Real.log (Real.exp 1 * (((2 * u : ℕ) : ℝ) + 2)) +
      (H.D0 he + 1) ^ 8 := rfl
  generalize (H.D0 he + 1) ^ 8 = c0 at hc0 hLdef ⊢
  have hy1 : 1 ≤ Real.exp 1 * (((2 * u : ℕ) : ℝ) + 2) := by
    have := Real.add_one_le_exp (1 : ℝ)
    have : (2 : ℝ) ≤ ((2 * u : ℕ) : ℝ) + 2 := by linarith [(Nat.cast_nonneg (2 * u) : (0:ℝ) ≤ _)]
    nlinarith
  have hlog1 : 1 ≤ Real.log (Real.exp 1 * (((2 * u : ℕ) : ℝ) + 2)) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
    have : 0 ≤ Real.log (((2 * u : ℕ) : ℝ) + 2) :=
      Real.log_nonneg (by linarith [(Nat.cast_nonneg (2 * u) : (0:ℝ) ≤ _)])
    linarith
  constructor
  · have h1 : H.Lf he (2 * u) ≤ (4 + c0) * Real.log (Real.exp 1 * (((2 * u : ℕ) : ℝ) + 2)) := by
      rw [hLdef]; nlinarith
    have hL0 : 0 ≤ H.Lf he (2 * u) := by rw [hLdef]; nlinarith
    have h2 := log_pow_le hy1 q
    have h3 : Real.exp 1 * (((2 * u : ℕ) : ℝ) + 2) ≤ 6 * ((u : ℝ) + 1) := by
      have := Real.exp_one_lt_d9
      push_cast; nlinarith
    calc H.Lf he (2 * u) ^ q ≤ ((4 + c0) * Real.log (Real.exp 1 * (((2 * u : ℕ) : ℝ) + 2))) ^ q :=
          pow_le_pow_left₀ hL0 h1 q
      _ = (4 + c0) ^ q * Real.log (Real.exp 1 * (((2 * u : ℕ) : ℝ) + 2)) ^ q := mul_pow _ _ _
      _ ≤ (4 + c0) ^ q * ((q.factorial : ℝ) * (Real.exp 1 * (((2 * u : ℕ) : ℝ) + 2))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ (4 + c0) ^ q * ((q.factorial : ℝ) * (6 * ((u : ℝ) + 1))) := by gcongr
      _ = _ := by simp only [mul_assoc]
  · have h1 := log_le_R hlogR hnu
    have hR1 : 1 ≤ ((u : ℝ) + 1) / ((nC : ℝ) + 1) := by
      rw [le_div_iff₀ (by positivity)]; have : (nC : ℝ) ≤ u := by exact_mod_cast hnu
      linarith
    rw [hLdef]; nlinarith

end Sharp

end G26G


-- ===== Solutions.G26.RefMain =====

/-! ### The reference block bound (Lemma G.29) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

set_option maxHeartbeats 1000000 in
/-- **the reference block bound (G.621)–(G.622)**: for large blocks, the probability of a reference
that is not strictly `a*` somewhere in `[u, 2u]` is `O((nC/u)^4 + u^{-4})` -/
theorem ref_block (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ} (hC : 0 ≤ C)
    (hcor : IsCorruptedG P 𝒜 θ C T R) {u nC : ℕ} (hnC1 : 1 ≤ nC) (hCn : C ≤ nC)
    (h2uT : 2 * u ≤ T) (hu : H.Sref he ≤ u)
    (huC : 2 ^ 20 * (((nC : ℝ) + 1) * Real.log (Real.exp 1 * ((nC : ℝ) + 1))) ≤ (u : ℝ) + 1) :
    P.real {ω | ∃ s, u ≤ s ∧ s ≤ 2 * u ∧ ¬ goodS ℬ e (js ℬ e astar) (s + 1) (R.cumEst s ω)} ≤
      H.Dref he * ((((nC : ℝ) + 1) / ((u : ℝ) + 1)) ^ 4 + 1 / ((u : ℝ) + 1) ^ 4) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hu1 : (0 : ℝ) < (u : ℝ) + 1 := by positivity
  have hn1 : (0 : ℝ) < (nC : ℝ) + 1 := by positivity
  have hnC1r : (1 : ℝ) ≤ nC := by exact_mod_cast hnC1
  -- numeric consequences of the thresholds
  have hlog1 : 1 ≤ Real.log (Real.exp 1 * ((nC : ℝ) + 1)) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
    have : 0 ≤ Real.log ((nC : ℝ) + 1) := Real.log_nonneg (by linarith)
    linarith
  have hlogR : ((nC : ℝ) + 1) * Real.log (Real.exp 1 * ((nC : ℝ) + 1)) ≤ (u : ℝ) + 1 := by
    have : 0 ≤ ((nC : ℝ) + 1) * Real.log (Real.exp 1 * ((nC : ℝ) + 1)) := by positivity
    linarith
  have hnCu20 : 2 ^ 20 * ((nC : ℝ) + 1) ≤ (u : ℝ) + 1 := by
    have : ((nC : ℝ) + 1) ≤ ((nC : ℝ) + 1) * Real.log (Real.exp 1 * ((nC : ℝ) + 1)) :=
      le_mul_of_one_le_right hn1.le hlog1
    linarith
  have hnu : nC ≤ u := by
    have : (nC : ℝ) ≤ u := by linarith
    exact_mod_cast this
  have h1024 : 1024 * (nC : ℝ) ≤ (u : ℝ) + 1 := by linarith
  have hX0 : 0 ≤ X1 d := by unfold X1; have := G2R.gB_pos (d := d); positivity
  have hhs0 := (H.hs_pos he).le
  have hSr : 4 * X1 d + 2 * H.hs he + ((16 * d + 1) * H.hs he) ^ 8 + 2 ^ 80 ≤ (u : ℝ) := by
    have h1 := Nat.le_ceil (4 * X1 d + 2 * H.hs he + ((16 * d + 1) * H.hs he) ^ 8 + (2 : ℝ) ^ 80)
    have h2 : ((H.Sref he : ℕ) : ℝ) ≤ u := by exact_mod_cast hu
    unfold Sref at h2; push_cast at h2
    linarith
  have hpos8 : (0 : ℝ) ≤ ((16 * d + 1) * H.hs he) ^ 8 := by positivity
  have hu80 : (2 : ℝ) ^ 80 ≤ (u : ℝ) := by linarith
  have hu4X : 4 * X1 d ≤ (u : ℝ) := by linarith
  have hu2 : 2 ≤ u := by
    have : (2 : ℝ) ≤ u := by
      have : (0 : ℝ) ≤ ((16 * d + 1) * H.hs he) ^ 8 := by positivity
      nlinarith
    exact_mod_cast this
  -- the buffer
  set z := Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1)) with hzdef
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hzn : (nC : ℝ) ≤ z := by
    rw [hzdef, Real.le_sqrt (by positivity) (by positivity)]
    have : (nC : ℝ) ≤ (u : ℝ) + 1 := by linarith
    nlinarith
  have hC4 : 4 * C ≤ 4 * z := by linarith
  set m0 := u / 4 with hm0def
  have hm0u : m0 ≤ u := Nat.div_le_self u 4
  have hu4 : (u : ℝ) + 1 ≤ 4 * ((m0 : ℝ) + 1) := by
    have : u + 1 ≤ 4 * (m0 + 1) := by omega
    exact_mod_cast this
  have hX1m : X1 d ≤ (m0 : ℝ) + 1 := by linarith
  have hhalf : 2 * ((m0 : ℝ) + 1) ≤ (u : ℝ) + 1 := by
    have : 2 * (m0 + 1) ≤ u + 1 := by omega
    exact_mod_cast this
  have hP0 : (0 : ℝ) ≤ ((4 * kk d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hXparts : (gB d * (16 * d + 4)) ^ 8 ≤ X1 d ∧ (2 * (((4 * kk d : ℕ) : ℝ) + 1)) ^ 8 ≤ X1 d ∧
      (960 * (((4 * kk d : ℕ) : ℝ) + 1) * (16 * d + 1)) ^ 8 ≤ X1 d ∧
      ((4 * kk d : ℕ) : ℝ) + 1 ≤ X1 d := by
    unfold X1
    have h1 : 0 ≤ (gB d * (16 * d + 4)) ^ 8 := by have := G2R.gB_pos (d := d); positivity
    have h2 : 0 ≤ (2 * (((4 * kk d : ℕ) : ℝ) + 1)) ^ 8 := by positivity
    have h3 : 0 ≤ (960 * (((4 * kk d : ℕ) : ℝ) + 1) * (16 * d + 1)) ^ 8 := by positivity
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨hX1a, hX1b, hX1c, hX1d⟩ := hXparts
  -- thresholds for the block decomposition
  have hτpos : ∀ n, 0 < tauB z n := fun n => tauB_pos hz0 n
  have hτmono : ∀ n, tauB z n ≤ tauB z (n + 1) := tauB_mono
  have hδ : ∀ n, tauB z (n + 1) - tauB z n ≤ 1 := tauB_delta z
  have hmP : ((4 * kk d : ℕ) : ℝ) + 1 ≤ 2 * ((m0 : ℝ) + 1) := by linarith
  have hτB : ∀ n, m0 ≤ n → gB d * (gbeta d (n + 1) + 3) ≤ tauB z n := by
    intro n hn
    refine thr_tauB hz0 ?_
    have : (m0 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hτm : 2 * (((4 * kk d : ℕ) : ℝ) + 1) ≤ tauB z m0 :=
    thr_tm hz0 (by positivity) (hX1b.trans hX1m)
  have hτβ : ∀ n, m0 ≤ n → n < 2 * u →
      40 * (((4 * kk d : ℕ) : ℝ) + 1) * gbeta d (n + 1) * ((n : ℝ) + 1) ≤ tauB z m0 ^ 2 :=
    fun n _ hn => thr_tb hz0 hn hu4 (hX1c.trans hX1m)
  have hhs : 2 * H.hs he ≤ ((u : ℝ) + 2) ^ 4 := by
    have h1 : ((u : ℝ) + 2) ≤ ((u : ℝ) + 2) ^ 4 :=
      le_self_pow₀ (by linarith [(Nat.cast_nonneg u : (0:ℝ) ≤ u)]) (by norm_num)
    have : (0 : ℝ) ≤ ((16 * d + 1) * H.hs he) ^ 8 := by positivity
    nlinarith
  have hbC : gbeta d (2 * u + 1) * H.hs he + 4 * C ≤ 2 * tauB z (2 * u) := by
    have h1 := thr_hb (d := d) (u := u) hhs0 (by
      have : (0 : ℝ) ≤ X1 d := hX0
      nlinarith)
    have h2 := (tauB_ge hz0 (2 * u))
    unfold tauB at h2 ⊢
    nlinarith
  -- the free levels
  have hR1 : 1 ≤ ((u : ℝ) + 1) / ((nC : ℝ) + 1) := by
    rw [le_div_iff₀ hn1]; have : (nC : ℝ) ≤ u := by exact_mod_cast hnu
    linarith
  have hτm0 := hτpos m0
  have hρ1τ : tauB z m0 ≤ tauB z m0 * (((u : ℝ) + 1) / ((nC : ℝ) + 1)) :=
    le_mul_of_one_le_right hτm0.le hR1
  have hρ1C : 4 * C ≤ tauB z m0 * (((u : ℝ) + 1) / ((nC : ℝ) + 1)) := by
    have := (tauB_ge hz0 m0).2.1
    linarith
  have hτ2u : tauB z (2 * u) ≤ ((u : ℝ) + 1) / 4 := thr_tau2u (u := u) (nC := nC) (by linarith) h1024
  have ha0 : 0 < 4 * tauB z (2 * u) := by have := hτpos (2 * u); positivity
  have hau : 4 * tauB z (2 * u) ≤ (u : ℝ) + 1 := by linarith
  have hρ2a : 2 * (4 * tauB z (2 * u)) ≤ 2 * ((u : ℝ) + 1) ^ 2 / (4 * tauB z (2 * u)) := by
    rw [le_div_iff₀ ha0]
    have := pow_le_pow_left₀ ha0.le hau 2
    nlinarith
  have hρa : 4 * tauB z (2 * u) ≤ 2 * ((u : ℝ) + 1) ^ 2 / (4 * tauB z (2 * u)) := by linarith
  have hρb : 2 * (4 * C + 2 * tauB z (2 * u)) ≤ 2 * ((u : ℝ) + 1) ^ 2 / (4 * tauB z (2 * u)) := by
    have := (tauB_ge hz0 (2 * u)).2.1
    linarith
  have hnCu : nC ≤ 2 * u := by omega
  have raw := H.ref_block_raw he hR hC hcor hτpos hτmono hδ h2uT hm0u hnCu hhalf hmP hτB hτm hτβ
    hhs hbC hρ1τ hρ1C hρa hρb
  obtain ⟨hLq, hL5⟩ := H.Lf_bounds he hnu hlogR
  have alg := ref_block_alg (d := d) (u := u) (nC := nC) (m0 := m0) (C := C) (sig := H.sig)
    (c0 := (H.D0 he + 1) ^ 8) (τm := tauB z m0) (L := H.Lf he (2 * u)) H.sig_pos
    (by have := H.D0_nonneg he; positivity) hnC1 hnu hC hCn hu4 (tauB_ge_r7 hz0 m0)
    (tauB_ge hz0 m0).2.1 hτ2u (H.Lf_facts he (2 * u)).2.1 hLq hL5
  exact raw.trans alg

end Sharp

end G26G


theorem _root_.solution : type_of% @G26G.Sharp.ref_block := @G26G.Sharp.ref_block
